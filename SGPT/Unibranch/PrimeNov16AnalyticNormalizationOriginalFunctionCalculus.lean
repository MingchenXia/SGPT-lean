import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives

/-! Finite polynomial expressions retain literal original representatives and entire stalk images.
Blueprint: prime-nov16-analytic-normalization-original-function-calculus.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open HironakaHolomorphicJetRankLoci HolGerm
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem holomorphic_pow (x : M) (F : M → ℂ) (hF : HolomorphicAt n F x) (N : ℕ) :
    HolomorphicAt n (fun y => F y^N) x := hF.mono fun _y hy => hy.pow N

theorem chartTranslatedGerm_pow (x : M) (F : M → ℂ) (hF : HolomorphicAt n F x) (N : ℕ) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => F y^N) (holomorphic_pow x F hF N) =
      (chartTranslatedGerm x x (mem_chart_source _ x) F hF)^N := by
  simp only [chartTranslatedGerm,translatedGerm]
  exact HolGerm.mk_pow _ _ N

theorem chartTranslatedGerm_add (x : M) (F G : M → ℂ)
    (hF : HolomorphicAt n F x) (hG : HolomorphicAt n G x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => F y+G y) (hF.add hG) =
      chartTranslatedGerm x x (mem_chart_source _ x) F hF+
        chartTranslatedGerm x x (mem_chart_source _ x) G hG := by
  simp only [chartTranslatedGerm,translatedGerm]
  exact HolGerm.mk_add _ _ _ _

theorem chartTranslatedGerm_sum (x : M) {k : ℕ} (F : Fin k → M → ℂ)
    (hF : ∀ i,HolomorphicAt n (F i) x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => ∑ i,F i y)
      (HolomorphicAt.sum Finset.univ fun i _ => hF i) =
      ∑ i,chartTranslatedGerm x x (mem_chart_source _ x) (F i) (hF i) := by
  simp only [chartTranslatedGerm,translatedGerm]
  rw [HolGerm.mk_sum Finset.univ]

theorem originalFunctionImage_add (C : Set M) (p : C) (F G : M → ℂ)
    (hF : HolomorphicAt n F p.val) (hG : HolomorphicAt n G p.val) :
    originalFunctionImage C p (fun y => F y+G y) (hF.add hG) =
      originalFunctionImage C p F hF+originalFunctionImage C p G hG := by
  unfold originalFunctionImage
  rw [chartTranslatedGerm_add,map_add]

theorem originalFunctionImage_mul (C : Set M) (p : C) (F G : M → ℂ)
    (hF : HolomorphicAt n F p.val) (hG : HolomorphicAt n G p.val) :
    originalFunctionImage C p (fun y => F y*G y) (hF.mul hG) =
      originalFunctionImage C p F hF*originalFunctionImage C p G hG := by
  unfold originalFunctionImage
  rw [chartTranslatedGerm_mul,map_mul]

theorem originalFunctionImage_pow (C : Set M) (p : C) (F : M → ℂ)
    (hF : HolomorphicAt n F p.val) (N : ℕ) :
    originalFunctionImage C p (fun y => F y^N) (holomorphic_pow p.val F hF N) =
      (originalFunctionImage C p F hF)^N := by
  unfold originalFunctionImage
  rw [chartTranslatedGerm_pow,map_pow]

theorem originalFunctionImage_sum (C : Set M) (p : C) {k : ℕ} (F : Fin k → M → ℂ)
    (hF : ∀ i,HolomorphicAt n (F i) p.val) :
    originalFunctionImage C p (fun y => ∑ i,F i y)
      (HolomorphicAt.sum Finset.univ fun i _ => hF i) =
      ∑ i,originalFunctionImage C p (F i) (hF i) := by
  unfold originalFunctionImage
  rw [chartTranslatedGerm_sum,map_sum]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
