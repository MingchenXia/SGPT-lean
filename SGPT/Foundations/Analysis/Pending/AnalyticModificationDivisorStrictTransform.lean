import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
import SGPT.Foundations.Analysis.Pending.StrictTransformSubvariety
import SGPT.Foundations.Analysis.Pending.RawProperStrictTransformLelongReader

set_option autoImplicit false

/-!
# Every specified whole divisor lifts through an actual proper modification

The intrinsic exceptional-image dimension bound internally supplies avoidance
for the SAME specified possibly singular codimension-one subvariety.  A genuine
regular-component construction then gives its literal strict transform, dimension,
whole image and raw Lelong reader for every weight after one geometric choice.
Neither a finite factorization nor caller strict-transform data is used.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform

open FirstPass FirstPass.BlowupSequences FirstPass.NonKahlerLocus
  RegularLocusComponent StrictTransformSubvariety AnalyticModificationLocalDiscrepancy

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- An irreducible analytic subvariety not contained in the exceptional image
has an irreducible strict transform of the same dimension under a modification. -/
theorem exists_strictTransform_subvariety_of_not_subset
    {g : Z → Y} (hg : IsAnalyticModification (n := n) g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) :
    ∃ Wt : ClosedIrreducibleAnalyticSubvariety n Z,
      Wt.carrier = strictTransform n g W.carrier ∧ Wt.dim = W.dim := by
  classical
  set T := g '' exceptionalLocus n g with hTdef
  have hT : IsComplexAnalyticSubset (n := n) T :=
    AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hg
  have hTc : IsClosed T := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hg
  have hExc : g ⁻¹' T = exceptionalLocus n g := AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hg
  have hgc : Continuous g := hg.1.continuous
  set Ω : Set Z := (exceptionalLocus n g)ᶜ with hΩdef
  have hΩ : IsOpen Ω := StrictTransformComposition.isOpen_compl_exceptionalLocus hg.1
  set Wt : Set Z := strictTransform n g W.carrier with hWtdef
  -- analyticity
  have hWtA : IsComplexAnalyticSubset (n := n) Wt := by
    have h := ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.1 W.analytic)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.1 hT)
    rwa [hExc] at h
  have hpreW : IsClosed (g ⁻¹' W.carrier) := W.isClosed_carrier.preimage hgc
  have hWt_sub : Wt ⊆ g ⁻¹' W.carrier := closure_minimal sdiff_subset hpreW
  have hWtΩ : ∀ u ∈ Ω, u ∈ Wt ↔ g u ∈ W.carrier := fun u hu =>
    ⟨fun h => hWt_sub h, fun h => subset_closure ⟨h, hu⟩⟩
  -- a regular point of `W` off `T`
  obtain ⟨y, hyW, hyT⟩ := not_subset.mp hW
  obtain ⟨c, hcT, k, hck⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen W.analytic
    hTc.isOpen_compl hyW hyT
  have hkd : k = W.dim := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim W hck
  subst hkd
  obtain ⟨ct, hct⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg c
  have hctΩ : ct ∈ Ω := fun h => hcT ⟨ct, h, hct⟩
  have hreg : ∀ u ∈ Ω, RegularAtDim (n := n) W.carrier (g u) W.dim →
      RegularAtDim (n := n) Wt u W.dim := fun u hu hr =>
    RegularAtDimTransport.regularAtDim_of_preimage hg.1 hu hΩ hu hWtΩ hr
  have hctreg : RegularAtDim (n := n) Wt ct W.dim := hreg ct hctΩ (hct ▸ hck)
  -- the component through `c` and its part off `T`
  set K := component (n := n) W.carrier c with hKdef
  have hWK : W.carrier = closure K := eq_closure_component W.irreducible_carrier hck
  have hKT : ¬ K ⊆ T := fun h => hW (hWK ▸ closure_minimal h hTc)
  obtain ⟨hKTconn, hKTdense⟩ :=
    ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
      W.analytic hT hck hKT
  -- `g` on `Ω` is an injective open map
  let f : Ω → Y := fun u => g u
  have hfinj : Function.Injective f := fun u v huv =>
    Subtype.ext (AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg v.2 huv)
  have hfopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun u => ?_
    have h1 := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
      hg.1 u.2
    have h2 : map ((↑) : Ω → Z) (𝓝 u) = 𝓝 (u : Z) := (hΩ.isOpenEmbedding_subtypeVal).map_nhds_eq u
    change 𝓝 (g u) ≤ map (g ∘ (↑)) (𝓝 u)
    rw [← map_map, h2, h1]
  have hrange : K \ T ⊆ range f := by
    rintro x ⟨-, hxT⟩
    obtain ⟨z, rfl⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg x
    exact ⟨⟨z, fun h => hxT ⟨z, h, rfl⟩⟩, rfl⟩
  set S : Set Z := (↑) '' (f ⁻¹' (K \ T)) with hSdef
  have hSconn : IsPreconnected S :=
    (hKTconn.preimage_of_isOpenMap hfinj hfopen hrange).image _ continuous_subtype_val.continuousOn
  have hSreg : S ⊆ regularPoints (n := n) Wt := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨W.dim, hreg u u.2 (regularAtDim_of_mem_component hck hu.1)⟩
  have hctS : ct ∈ S := ⟨⟨ct, hctΩ⟩, ⟨show g ct ∈ K by rw [hct]; exact mem_component_self hck,
    show g ct ∉ T by rw [hct]; exact hcT⟩, rfl⟩
  have hSK : S ⊆ component (n := n) Wt ct :=
    subset_component_of_isPreconnected hSconn hSreg ⟨ct, hctS, mem_component_self hctreg⟩
  -- density
  have hdense : Wt ⊆ closure (component (n := n) Wt ct) := by
    have h1 : g ⁻¹' W.carrier \ exceptionalLocus n g ⊆ closure S := by
      rintro u ⟨huW, huΩ⟩
      refine mem_closure_iff.mpr fun N hN huN => ?_
      have hmap := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
        hg.1 huΩ
      have himg : g '' (N ∩ Ω) ∈ 𝓝 (g u) := by
        rw [← hmap]
        exact image_mem_map ((hN.inter hΩ).mem_nhds ⟨huN, huΩ⟩)
      have hgu : g u ∈ closure (K \ T) := by
        have h := hWK ▸ huW
        exact closure_minimal hKTdense isClosed_closure h
      obtain ⟨_, ⟨v, ⟨hvN, hvΩ⟩, rfl⟩, hvKT⟩ :=
        mem_closure_iff_nhds.mp hgu _ himg
      exact ⟨v, hvN, ⟨v, hvΩ⟩, hvKT, rfl⟩
    exact closure_minimal (h1.trans (closure_mono hSK)) isClosed_closure
  have hWt_eq : Wt = closure (component (n := n) Wt ct) :=
    Subset.antisymm hdense (closure_minimal (component_subset (n := n) Wt ct) hWtA.isClosed)
  have hirr : IsComplexAnalyticallyIrreducible (n := n) Wt := by
    rw [IsComplexAnalyticallyIrreducible.congr hWt_eq]
    exact isComplexAnalyticallyIrreducible_closure_component hWtA hctreg
  exact ⟨⟨Wt, hWtA.isClosed, hirr, W.dim, W.dim_le, ⟨ct, hctreg⟩⟩, rfl, rfl⟩


/-- The SAME specified whole divisor has a genuine strict transform and one
literal raw-reader equality for every quasi-PSH weight, without input avoidance. -/
theorem exists_strictTransform_reader
    {g : Z → Y} (hg : IsAnalyticModification (n := n) g)
    (V : ClosedIrreducibleAnalyticSubvariety n Y) (hVdim : V.dim + 1 = n) :
    ∃ Vt : ClosedIrreducibleAnalyticSubvariety n Z,
      Vt.carrier = strictTransform n g V.carrier ∧ Vt.dim = V.dim ∧
      g '' Vt.carrier = V.carrier ∧
      ∀ (u : Y → EReal), ManifoldQuasiPlurisubharmonic (n := n) u →
        (⨅ y ∈ Vt.carrier, lelongNumber (n := n) (fun y => u (g y)) y) =
          ⨅ x ∈ V.carrier, lelongNumber (n := n) u x := by
  obtain ⟨Vt, hstrict, hd⟩ := exists_strictTransform_subvariety_of_not_subset hg V
    (AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
      hg V hVdim)
  refine ⟨Vt, hstrict, hd, ?_, fun u hu => ?_⟩
  · exact RawProperStrictTransformLelongReader.image_eq_of_strictTransform
      hg.1 hg.2.1 V Vt hstrict
  · exact RawProperStrictTransformLelongReader.iInf_lelongNumber_comp_eq_of_strictTransform
      hg.1 hg.2.1 hu V Vt hstrict

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
