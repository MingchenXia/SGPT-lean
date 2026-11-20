import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartVanishing
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGermTestRadical

/-! Actual original test-set ideal equals the FULL actual radical, with no intrinsic dictionary supplier.
Blueprint: prime-nov16-analytic-normalization-original-test-radical.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalTestRadical
open PrimeNov16AnalyticNormalizationOriginalChartVanishing
open PrimeNov16AnalyticNormalizationGermTestRadical
open AnalyticDescendingChain HironakaHolomorphicJetRankLoci HolGerm
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_whole_test_radical (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (x : M) (Q : M → ℂ) (hQ : HolomorphicAt n Q x) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) (C ∩ {y | Q y=0})) x x (mem_chart_source _ x) =
      (wholeChartStalkIdeal (vanishingIdeal (n := n) C) x x (mem_chart_source _ x) ⊔
        Ideal.span {chartTranslatedGerm x x (mem_chart_source _ x) Q hQ}).radical := by
  let e := (complexChartAt (n := n) x).val
  let T : ComplexModel n → ℂ := fun w => Q (e.symm (w+e x))
  have hT : ∀ᶠ w in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ T w :=
    translated_holomorphic (e x) (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hQ)
  have hread : chartTranslatedGerm x x (mem_chart_source _ x) Q hQ=HolGerm.mk T hT := rfl
  have hset : chartGerm (n := n) (C ∩ {y | Q y=0}) x =
      chartGerm (n := n) C x ∩ {w | T w=0} := by
    ext w
    change (w+e x ∈ e.target ∧ (e.symm (w+e x) ∈ C ∧ Q (e.symm (w+e x))=0)) ↔
      ((w+e x ∈ e.target ∧ e.symm (w+e x) ∈ C) ∧ Q (e.symm (w+e x))=0)
    exact and_assoc.symm
  rw [original_whole_chart_vanishing,original_whole_chart_vanishing C x,hset,hread]
  exact original_test_vanishing_eq_radical _ (isAnalyticGerm_chartGerm hC x) T hT

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalTestRadical
