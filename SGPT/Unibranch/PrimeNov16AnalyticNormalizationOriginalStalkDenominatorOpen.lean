import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorOpen

/-! Actual central multiplication kernel spreads by coherence to ONE original open.
Blueprint: prime-nov16-analytic-normalization-original-stalk-denominator-open.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentEqualityOpen
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
open HironakaSmoothCentreRealDomainActualSheafStalk

open PrimeNov16AnalyticNormalizationOriginalDenominatorOpen

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_original_open_entire_stalk_regular (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (p : C) (D : M → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D)
    (hx : ∀ r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier,
      originalFunctionImage C p D (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)*r=0 → r=0) :
    ∃ U : Set M,IsOpen U ∧ p.val ∈ U ∧ ∀ y : C,y.val ∈ U →
      ∀ r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk y).carrier,
        originalFunctionImage C y D (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)*r=0 → r=0 := by
  let P := vanishingIdeal (n := n) C
  have hP : P.IsCoherent := CartanIrreducible.cartanCoherence C hC
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  have hin (y : C) : actualSubspaceStalkChartEquiv (n := n) C y
      (originalFunctionImage C y D (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)) =
      Ideal.Quotient.mk _ (chartTranslatedGerm y.val y.val (mem_chart_source _ y.val) D
        (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)) :=
    (actualSubspaceStalkChartEquiv (n := n) C y).apply_symm_apply _
  have hq : ∀ r : HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal P p.val p.val (mem_chart_source _ p.val),
      Ideal.Quotient.mk _ (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) D
        (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z))*r=0 → r=0 := by
    intro r hr
    have hz : originalFunctionImage C p D
        (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)*e.symm r=0 := by
      apply e.injective
      rw [map_mul,hin p,e.apply_symm_apply,map_zero]
      exact hr
    have hz' := congrArg e (hx _ hz)
    simpa only [e.apply_symm_apply,map_zero] using hz'
  obtain ⟨U,hU,hpU,hreg⟩ := exists_original_open_quotient_regular P hP D hD p.val hq
  refine ⟨U,hU,hpU,fun y hy r hr => ?_⟩
  let ey := actualSubspaceStalkChartEquiv (n := n) C y
  apply ey.injective
  rw [map_zero]
  apply hreg y.val hy
  have hz := congrArg ey hr
  rw [map_mul,hin y,map_zero] at hz
  exact hz

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
