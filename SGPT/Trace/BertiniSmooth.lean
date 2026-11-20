import SGPT.Trace.BertiniSmoothConormal
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound
import SGPT.Foundations.Analysis.Pending.AnalyticImageDimension
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedDimensionParts
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-!
# Generic smoothness of the members of a linear system

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems", Step 1.1 of the proof of
`thm:Bert` (the members `H ∩ X` of `Λ = |𝒪_{ℙᴺ}(1)|` are smooth for `H` outside a proper Zariski
closed subset; the book quotes the algebraic Bertini theorem). Blueprint:
`claude-bertini:singular-members` (`blueprint/src/claude-bertini.tex`), sub-lemmas in
`blueprint/src/claude-bertini-bc.tex`.

Let `X` be a compact complex manifold and `p : X → ℙᴺ` holomorphic, `N ≥ 1`. The set
`singularMemberSet n p ⊆ Λ` of hyperplanes `H_ℓ` whose member `p⁻¹(H_ℓ)` is not a smooth hypersurface
is proved, analytically (no algebraic Bertini theorem), to be

* an analytic subset of `Λ` (`isComplexAnalyticSubset_singularMemberSet`): it is the image of the
  analytic conormal set `C ⊆ Λ × X` under the projection `pr₁`, which is proper on `C` because `X`
  is compact (Remmert's proper mapping theorem,
  `SGPT.Foundations.Analysis.Pending.ProperMappingTheorem.isComplexAnalyticSubset_image`);
* with empty interior (`interior_singularMemberSet`): on each pure-dimensional part `C⁽ᵏ⁾` of `C`
  the rank of `pr₁` is `≤ N - 1` (`rankAt_fst_le`), so the fibres of `pr₁|C⁽ᵏ⁾` have dimension
  `≥ k - (N - 1)` (`FibreDimensionLowerBound.locDimGE_fibre`) and `pr₁(C⁽ᵏ⁾)` has dimension
  `≤ N - 1` (`AnalyticImageDimension.dimLE_image`);
* hence pluripolar in the sense of `def:pluripolarsets` (`locallyPluripolar_singularMemberSet`),
  i.e. `p⁻¹(H_ℓ)` is a smooth hypersurface for quasi-every `ℓ ∈ Λ`
  (`coPluripolar_isSmoothHypersurfaceMember`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.Bertini

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.AnalyticDimensionBasics
  SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

open scoped ProductComplexManifold
open ProductComplexManifold

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

variable (n) in
/-- The set `Σ ⊆ Λ` of hyperplanes `H_ℓ` whose member `p⁻¹(H_ℓ)` is not a smooth hypersurface. -/
def singularMemberSet : Set (HyperplaneSpace N) := {l | ¬ IsSmoothHypersurfaceMember n p l}

theorem singularMemberSet_eq_image
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    singularMemberSet n p = Prod.fst '' conormalSet n p :=
  (image_fst_conormalSet p hp).symm

/-- The interior of a finite union of closed sets with empty interior is empty. -/
theorem interior_iUnion_eq_empty_of_isClosed {α ι : Type*} [TopologicalSpace α] [Finite ι]
    {s : ι → Set α} (hs : ∀ i, IsClosed (s i)) (hint : ∀ i, interior (s i) = ∅) :
    interior (⋃ i, s i) = ∅ := by
  classical
  have key : ∀ t : Finset ι, interior (⋃ i ∈ t, s i) = ∅ := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t _ ih =>
      rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hs a) ih, hint a]
  have := Fintype.ofFinite ι
  simpa using key Finset.univ

/-- The `k`-dimensional part `closure (regularLocus A k)` of an analytic set is of pure dimension
`k` (as `SGPT.Foundations.Analysis.Pending.HironakaDimensionGlobalComponents.isPureDim_dimensionPart`,
reproved here from the dimension-part API). -/
theorem isPureDim_dimensionPart' {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M] {A : Set M}
    (hA : IsComplexAnalyticSubset (n := m) A) (k : ℕ) :
    IsPureDim (n := m) (HironakaEmbeddedDimensionParts.dimensionPart (n := m) A k) k := by
  intro y j hy
  obtain ⟨z, hz, hzk⟩ := mem_closure_iff_nhds.mp
    (HironakaEmbeddedDimensionParts.subset_closure_regularLocus_dimensionPart hA.isClosed k
      hy.2.1) _ (RegularPatchNeighborhood.eventually_regularAtDim hy)
  exact RegularPointDimension.eq_of_regularAtDim (hz hzk.2.1) hzk

variable [CompactSpace X]

/-- `pr₁ : Λ × X → Λ` is proper on the (closed) conormal set, `X` being compact. -/
theorem properOn_fst_conormalSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    ProperOn (Prod.fst : HyperplaneSpace N × X → HyperplaneSpace N) (conormalSet n p) := by
  intro K hK
  exact ((isComplexAnalyticSubset_conormalSet p hp).isClosed.inter
    (hK.isClosed.preimage continuous_fst)).isCompact

/-- **The set of hyperplanes with a singular member is analytic** (Remmert's proper mapping
theorem). -/
theorem isComplexAnalyticSubset_singularMemberSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    IsComplexAnalyticSubset (n := N) (singularMemberSet n p) := by
  rw [singularMemberSet_eq_image p hp]
  exact ProperMappingTheorem.isComplexAnalyticSubset_image (n := N + n) (k := N)
    (contMDiff_fst (n := N) (m := n) (X := HyperplaneSpace N) (Y := X))
    (isComplexAnalyticSubset_conormalSet p hp) (properOn_fst_conormalSet p hp)

omit [CompactSpace X] in
/-- The image of a pure-dimensional part of the conormal set has empty interior. -/
theorem interior_image_fst_dimensionPart
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) (k : ℕ) :
    interior (Prod.fst '' HironakaEmbeddedDimensionParts.dimensionPart (n := N + n)
      (conormalSet n p) k) = ∅ := by
  set C := conormalSet n p with hCdef
  have hC := isComplexAnalyticSubset_conormalSet p hp
  set A := HironakaEmbeddedDimensionParts.dimensionPart (n := N + n) C k with hAdef
  have hA : IsComplexAnalyticSubset (n := N + n) A :=
    HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hC k
  have hpure : IsPureDim (n := N + n) A k :=
    isPureDim_dimensionPart' hC k
  have hAC : A ⊆ C := HironakaEmbeddedDimensionParts.dimensionPart_subset hC.isClosed k
  have hfst := contMDiff_fst (n := N) (m := n) (X := HyperplaneSpace N) (Y := X)
  have hfib : ∀ x ∈ A, LocDimGE (n := N + n) (A ∩ Prod.fst ⁻¹' {x.1}) x (k - (N - 1)) :=
    fun x hx => FibreDimensionLowerBound.locDimGE_fibre hA hpure hfst
      (fun y hy => rankAt_fst_le p hp hAC hy.2.1) hx
  have hdim : DimLE (n := N) (Prod.fst '' A) (k - (k - (N - 1))) :=
    AnalyticImageDimension.dimLE_image hfst hA hpure.dimLE hfib
  by_contra hne
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hreg : RegularAtDim (n := N) (Prod.fst '' A) y N := by
    refine RegularPointDimension.regularAtDim_of_inter_eq isOpen_interior hy ?_
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := N) y)
    rw [univ_inter, inter_eq_right.mpr interior_subset]
  have := hdim y N hreg
  omega

/-- **Generic smoothness**: the set of hyperplanes with a singular member has empty interior. -/
theorem interior_singularMemberSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) :
    interior (singularMemberSet n p) = ∅ := by
  have hC := isComplexAnalyticSubset_conormalSet p hp
  rw [singularMemberSet_eq_image p hp, HironakaEmbeddedDimensionParts.eq_iUnion_dimensionPart hC,
    image_iUnion]
  refine interior_iUnion_eq_empty_of_isClosed (fun k => ?_)
    (fun k => interior_image_fst_dimensionPart p hp hN k)
  exact ((HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hC
    k).isClosed.isCompact.image continuous_fst).isClosed

/-- The set of hyperplanes with a singular member is pluripolar (native chartwise form). -/
theorem manifoldLocallyPluripolar_singularMemberSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) :
    ManifoldLocallyPluripolar (n := N) (singularMemberSet n p) :=
  ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    (isComplexAnalyticSubset_singularMemberSet p hp) (interior_singularMemberSet p hp hN)

/-- **Generic smoothness, pluripolar form** (blueprint `claude-bertini:singular-members`): the set of
`ℓ ∈ Λ = |𝒪_{ℙᴺ}(1)|` such that `p⁻¹(H_ℓ)` is not a smooth hypersurface is pluripolar in the sense
of `def:pluripolarsets`. -/
theorem locallyPluripolar_singularMemberSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
      (singularMemberSet n p) :=
  SGPT.PSH.VariableComplexAtlas.locallyPluripolar_of_in_chart
    (A := SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N))
    (fun e => manifoldLocallyPluripolar_singularMemberSet p hp hN e)

/-- **Generic smoothness**: for quasi-every `ℓ ∈ Λ`, the member `p⁻¹(H_ℓ)` is a smooth
hypersurface (possibly empty). -/
theorem coPluripolar_isSmoothHypersurfaceMember
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsSmoothHypersurfaceMember n p l} := by
  have h := locallyPluripolar_singularMemberSet p hp hN
  exact h.mono fun l hl => hl

/-- **Source `thm:Bert`, smoothness clause**: for quasi-every `H ∈ |𝒪_{ℙᴺ}(1)|`, the
scheme-theoretic inverse image `H' = H ×_{ℙᴺ} X` is smooth (of dimension `n - 1`: its support is
a closed submanifold and its ideal sheaf is reduced), i.e. the first condition defining the set `𝒢`
of `thm:Bert` holds quasi-everywhere. (The multiplier-ideal condition is not proved here.) -/
theorem coPluripolar_exists_isSmoothMemberOfDim
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hN : 1 ≤ N) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ k ≤ n, IsSmoothMemberOfDim p hp l k} := by
  refine (locallyPluripolar_singularMemberSet p hp hN).mono fun l hl => ?_
  intro hsm
  exact hl ⟨n - 1, Nat.sub_le n 1, isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p hp hsm⟩

end SGPT.Trace.Bertini
