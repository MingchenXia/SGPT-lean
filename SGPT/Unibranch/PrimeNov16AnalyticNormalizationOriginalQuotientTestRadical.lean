import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalTestRadical

/-! Actual original quotient test ideal is the ENTIRE radical principal ideal, internally.
Blueprint: prime-nov16-analytic-normalization-original-quotient-test-radical.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalQuotientTestRadical
open PrimeNov16AnalyticNormalizationOriginalTestRadical HironakaHolomorphicJetRankLoci
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_quotient_test_radical (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (x : M) (Q : M → ℂ) (hQ : HolomorphicAt n Q x) :
    let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) x x (mem_chart_source _ x)
    Ideal.map (Ideal.Quotient.mk P)
      (wholeChartStalkIdeal (vanishingIdeal (n := n) (C ∩ {y | Q y=0})) x x (mem_chart_source _ x)) =
      (Ideal.span {Ideal.Quotient.mk P (chartTranslatedGerm x x (mem_chart_source _ x) Q hQ)}).radical := by
  let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) x x (mem_chart_source _ x)
  let g := chartTranslatedGerm x x (mem_chart_source _ x) Q hQ
  have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ P ⊔ Ideal.span {g} := by
    rw [Ideal.mk_ker]
    exact le_sup_left
  change Ideal.map (Ideal.Quotient.mk P)
      (wholeChartStalkIdeal (vanishingIdeal (n := n) (C ∩ {y | Q y=0})) x x (mem_chart_source _ x)) =
      (Ideal.span {Ideal.Quotient.mk P g}).radical
  rw [original_whole_test_radical C hC x Q hQ,
    Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective hker,
    Ideal.map_sup,Ideal.map_quotient_self,Ideal.map_span,Set.image_singleton,bot_sup_eq]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalQuotientTestRadical
