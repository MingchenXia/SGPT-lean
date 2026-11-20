import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralCanonicalStalk
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalGraph

/-! Original-only proper finite analytic graph with SAME canonical central stalks.
Blueprint: prime-nov16-analytic-normalization-original-central-graph.tex.
Normal source neighbourhood and global normalization are separate gates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationCentralStalkInjective

theorem exists_original_proper_finite_graph_canonical_central_stalks {n : ℕ}
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
        ∀ hp : baseProjection n k p.val.val = 0,
        ∃ e : ((actualSubspaceSheaf (n := n+k)
          (graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G)).presheaf.stalk p).carrier ≃+*
          integralClosure (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z)
            (FractionRing (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z)),
          ∀ b,e (centralBaseMap hZ (ballDomain (n := n) r) hCarrier H G hHOn hGOn p hp b) = algebraMap _ _ b := by
  obtain ⟨k,s,h,g,polys,hh,hs,hpolys,H,hH,G,hG,a,ha,r,hHOn,hGOn,hCarrier,
    hr,hrN,hHclass,hGclass,_haclass,haOn,_hnonzero,hrel,hproper,hfinite⟩ :=
    exists_original_proper_finite_generator_graph hZ hN
  refine ⟨k,r,H,G,hHOn,hGOn,hCarrier,hr,hrN,hproper,hfinite,?_⟩
  intro p hp
  have hm : ∀ x : {z : ballDomain (n := n) r | z.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (polys i).natDegree (a i) x.val.val (G i x.val.val/H x.val.val) = 0 := by
    intro x hx i
    exact hrel x.val.val x.property x.val.property hx i
  apply PrimeNov16AnalyticNormalizationCentralCanonicalStalk.exists_actual_central_canonical_equiv
    hZ (ballDomain (n := n) r) hCarrier H G hHOn hGOn hH hG p hp
      (fun i => (polys i).natDegree) a haOn hm h hh s hs hHclass
  intro i
  rw [hGclass]
  exact (hpolys i).1.symm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralGraph
