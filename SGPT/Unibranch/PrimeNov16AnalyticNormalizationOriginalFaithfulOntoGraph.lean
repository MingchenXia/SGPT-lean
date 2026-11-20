import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFaithfulGraph
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseOnto
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationProperNormalShrink

/-! Original-only SAME genuine graph has a normal ENTIRE base preimage and actual proper finite restriction.
Blueprint: prime-nov16-analytic-normalization-original-faithful-onto-graph.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFaithfulOntoGraph
open AnalyticGermDecomposition
open PrimeNov16AnalyticNormalizationOriginalFaithfulGraph
open PrimeNov16AnalyticNormalizationOriginalBaseOnto
open PrimeNov16AnalyticNormalizationProperNormalShrink
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationLocalGraph
open HironakaActualAnalyticSubspace

private theorem zero_mem_original_irreducible_germ {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) : (0 : ComplexModel n) ∈ Z := by
  by_contra h0
  obtain ⟨s,G,hG,hset⟩ := hZ.1
  have hn : ¬ ∀ i,G i 0=0 := fun h => h0 (hset.self_of_nhds.mpr h)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hne : ∀ᶠ z in 𝓝 (0 : ComplexModel n),G i z ≠ 0 :=
    ((hG i).self_of_nhds.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hi
  apply hZ.2.1
  apply eventuallyEq_set.mpr
  filter_upwards [hset,hne] with z hz hzi
  constructor
  · intro hzZ
    exact (hzi ((hz.mp hzZ) i)).elim
  · intro hzE
    exact hzE.elim

theorem exists_original_faithful_onto_normal_graph {n : ℕ}
    {Z N : Set (ComplexModel n)} (hZ : IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (k : ℕ) (r : ℝ) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
      (hH : DifferentiableOn ℂ H (ballDomain (n := n) r))
      (hG : ∀ i,DifferentiableOn ℂ (G i) (ballDomain (n := n) r))
      (hC : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z}),
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ H z) ∧
      (¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → H z=0) ∧
      let B := (sourceReducedComplexSpaceModel (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} hC).obj.left
      let S := graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G
      let f : S → B := (projection (ballDomain (n := n) r) hC H G hH hG).hom.left.base
      IsProperMap f ∧ (∀ b : B,(f ⁻¹' {b}).Finite) ∧
        ∃ b0 : B,b0.val.val=0 ∧ ∃ V : Set B,IsOpen V ∧ b0 ∈ V ∧
          Function.Surjective (V.restrictPreimage f) ∧ IsProperMap (V.restrictPreimage f) ∧ (∀ v : V,((V.restrictPreimage f) ⁻¹' {v}).Finite) ∧
          ∀ p : S,f p ∈ V → IsDomain ((actualSubspaceSheaf (n := n+k) S).presheaf.stalk p).carrier ∧
            IsIntegrallyClosed ((actualSubspaceSheaf (n := n+k) S).presheaf.stalk p).carrier := by
  obtain ⟨k,r,H,G,hH,hG,hC,hr,hrN,hHg,hnonzero,hproper,hfinite,hcentral⟩ :=
    exists_original_faithful_normal_central_graph hZ hN
  refine ⟨k,r,H,G,hH,hG,hC,hr,hrN,hHg,hnonzero,hproper,hfinite,?_⟩
  let B := (sourceReducedComplexSpaceModel (ballDomain (n := n) r)
    {z : ballDomain (n := n) r | z.val ∈ Z} hC).obj.left
  let S := graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G
  let f : S → B := (projection (ballDomain (n := n) r) hC H G hH hG).hom.left.base
  let b0 : B := ⟨⟨0,mem_ball_self hr⟩,zero_mem_original_irreducible_germ hZ⟩
  have hc : ∀ p : S,f p=b0 → p ∈ originalNormalLocus (n := n+k) S := by
    intro p hp
    have hproj : (f p).val.val=baseProjection n k p.val.val :=
      congrArg Subtype.val (projection_apply (ballDomain (n := n) r) hC H G hH hG p)
    have hz : (f p).val.val=0 := congrArg (fun b : B => b.val.val) hp
    exact hcentral p (hproj.symm.trans hz)
  obtain ⟨W,hW,hbW,honto⟩ := exists_original_open_onto hZ (ballDomain (n := n) r)
    hC b0 rfl H G hH hG hHg hnonzero hproper
  have hWB : IsOpen {b : B | b.val ∈ W} := hW.preimage continuous_subtype_val
  obtain ⟨V,hV,hbV,hVN,hpV,hfV,hNormal⟩ := exists_actual_proper_finite_normal_full_preimage
    S (graphClosure_analytic (ballDomain (n := n) r) hC H G hH hG) f hproper hfinite b0 hc
      (hWB.mem_nhds hbW)
  refine ⟨b0,rfl,V,hV,hbV,?_,hpV,hfV,hNormal⟩
  intro v
  obtain ⟨p,hp⟩ := honto v.val (hVN v.property)
  have hp' : f (show S from p)=v.val := hp
  have hmem : (show S from p) ∈ f ⁻¹' V := by
    change f (show S from p) ∈ V
    exact hp'.symm ▸ v.property
  exact ⟨⟨(show S from p),hmem⟩,Subtype.ext hp'⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFaithfulOntoGraph
