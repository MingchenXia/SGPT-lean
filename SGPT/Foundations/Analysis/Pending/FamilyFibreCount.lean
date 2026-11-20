import SGPT.Foundations.Analysis.Pending.FlatVolumeFibreBound

set_option autoImplicit false

/-!
# The fibre count of a regular-piece family is the fibre count of the subvariety

`Pending.FlatVolumeFibreBound.sum_lintegral_flatPatchDensity_le` needs, for each
coordinate projection, a bound on the TOTAL number of preimages of a point ACROSS
the whole family.  This module supplies the transfer that turns such a bound on
the subvariety itself — the geometric sheet number — into that hypothesis: the
parametrizations are injective and the pieces have pairwise disjoint images, so
the preimages in the family inject into the preimages in `V`.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FamilyFibreCount

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison

section General

variable {α β ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Disjoint injective images bound the total cardinality.**  If each `S i`
injects into `T` under `φ i` and the images are pairwise disjoint, the
cardinalities of the `S i` add up to at most that of `T`. -/
theorem sum_encard_le_encard (S : ι → Set α) (φ : ι → α → β) (T : Set β)
    (hmaps : ∀ i, ∀ a ∈ S i, φ i a ∈ T)
    (hinj : ∀ i, InjOn (φ i) (S i))
    (hdisj : Pairwise fun i j => Disjoint (φ i '' S i) (φ j '' S j)) :
    ∑ i, (S i).encard ≤ T.encard := by
  classical
  have hkey : ∀ s : Finset ι,
      ∑ i ∈ s, (φ i '' S i).encard = (⋃ i ∈ s, φ i '' S i).encard := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hd : Disjoint (φ a '' S a) (⋃ i ∈ s, φ i '' S i) :=
        Set.disjoint_iUnion₂_right.2 fun i hi => hdisj (by rintro rfl; exact ha hi)
      rw [Finset.sum_insert ha, ih, Finset.set_biUnion_insert, Set.encard_union_eq hd]
  have hrw : ∑ i, (S i).encard = ∑ i, (φ i '' S i).encard :=
    Finset.sum_congr rfl fun i _ => ((hinj i).encard_image).symm
  rw [hrw, hkey Finset.univ]
  refine Set.encard_le_encard ?_
  simp only [Set.iUnion_subset_iff]
  rintro i - _ ⟨a, ha, rfl⟩
  exact hmaps i a ha

end General

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parametrization of a regular patch is injective on its parameter
domain. -/
theorem toManifold_injOn (Q : RegularPatch V) :
    InjOn Q.toManifold Q.parameterDomain := by
  intro w hw w' hw' hEq
  have h : Q.coordinateParametrization w = Q.coordinateParametrization w' := by
    rw [← RegularPatch.chart_toManifold Q hw, ← RegularPatch.chart_toManifold Q hw', hEq]
  have h2 : planeInclusion V.dim n w = planeInclusion V.dim n w' := by
    have e1 := Q.flattening.right_inv _ hw
    have e2 := Q.flattening.right_inv _ hw'
    change Q.flattening.toFun (Q.coordinateParametrization w) = _ at e1
    change Q.flattening.toFun (Q.coordinateParametrization w') = _ at e2
    rw [← e1, ← e2, h]
  exact AdmissibleCurrentFormPositivity.planeInclusion_injective V.dim_le h2

/-- **The family's fibre count is at most the subvariety's.**  For any map `g` on
the manifold and any value `y`, the total number of parameters of a family that
`g ∘ toManifold` sends to `y` is at most the number of points of `U` that `g`
sends to `y`, provided every piece has its image in `U`. -/
theorem sum_encard_preimage_le (F : RegularPieceFamily V (∅ : Set M))
    {U : Set M} (hU : ∀ i, (F.patch i).toManifold '' F.piece i ⊆ U)
    {γ : Type*} (g : M → γ) (y : γ) :
    ∑ i, (F.piece i ∩ (fun w => g ((F.patch i).toManifold w)) ⁻¹' {y}).encard ≤
      {z | z ∈ U ∧ g z = y}.encard := by
  classical
  refine sum_encard_le_encard _ (fun i => (F.patch i).toManifold) _ ?_ ?_ ?_
  · intro i a ha
    exact ⟨hU i ⟨a, ha.1, rfl⟩, ha.2⟩
  · intro i
    exact (toManifold_injOn (F.patch i)).mono
      (fun a ha => F.piece_subset i ha.1)
  · intro i j hij
    refine Disjoint.mono ?_ ?_ (F.pairwise_disjoint_image hij) <;>
      exact Set.image_mono fun a ha => ha.1

end SGPT.Foundations.Analysis.Pending.FamilyFibreCount
