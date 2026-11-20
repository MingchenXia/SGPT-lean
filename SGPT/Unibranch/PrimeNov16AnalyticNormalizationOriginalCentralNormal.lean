import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralGraph

/-! Actual normal domain stalks on the ENTIRE central fibre, original-only input.
Blueprint: prime-nov16-analytic-normalization-original-central-normal.tex.
The normal-neighbourhood and global gluing gates remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralNormal
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationOriginalCentralGraph

theorem exists_original_proper_finite_graph_normal_central_stalks {n : ℕ}
    {Z N : Set (ComplexModel n)} (hZ : IsIrreducibleGerm Z)
    (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (k : ℕ) (r : ℝ) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
      (hHOn : DifferentiableOn ℂ H (ballDomain (n := n) r))
      (hGOn : ∀ i,DifferentiableOn ℂ (G i) (ballDomain (n := n) r))
      (hCarrier : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z}),
      0 < r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      IsProperMap (projection (ballDomain (n := n) r) hCarrier H G hHOn hGOn).hom.left.base ∧
      (∀ x : (sourceReducedComplexSpaceModel (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} hCarrier).obj.left,
        ((projection (ballDomain (n := n) r) hCarrier H G hHOn hGOn).hom.left.base ⁻¹' {x}).Finite) ∧
      ∀ p : graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G,
        baseProjection n k p.val.val = 0 →
        IsDomain ((actualSubspaceSheaf (n := n+k)
          (graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G)).presheaf.stalk p).carrier ∧
        IsIntegrallyClosed ((actualSubspaceSheaf (n := n+k)
          (graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G)).presheaf.stalk p).carrier := by
  obtain ⟨k,r,H,G,hHOn,hGOn,hCarrier,hr,hrN,hproper,hfinite,hcanonical⟩ :=
    exists_original_proper_finite_graph_canonical_central_stalks hZ hN
  let : (vanishingIdeal Z).IsPrime := (isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
  let : IsIntegrallyClosed (integralClosure (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z)
      (FractionRing (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z))) :=
    PrimeNov16AnalyticIntegralClosure.normal_analytic_germ_integralClosure (vanishingIdeal Z)
  refine ⟨k,r,H,G,hHOn,hGOn,hCarrier,hr,hrN,hproper,hfinite,?_⟩
  intro p hp
  obtain ⟨e,_he⟩ := hcanonical p hp
  exact ⟨Function.Injective.isDomain e e.injective,IsIntegrallyClosed.of_equiv e.symm⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralNormal
