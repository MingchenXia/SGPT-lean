import SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
import SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator
import SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound

set_option autoImplicit false

/-! # Genuine rational analytic types admit an actual maximum -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum

open FirstPass AnalyticGeneratorTensorPowers

noncomputable section

/-- Tensor powers reexpress the same actual potential and the same bounded
remainder with the divided coefficient. -/
theorem logarithmicTypeAt_tensorPowerFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {c : ℝ} {N r : ℕ} {f : Fin N → E → ℂ} {x : E}
    (hu : LogarithmicTypeAt u c f x) (hr : 0 < r) :
    LogarithmicTypeAt u (c / (r : ℝ)) (tensorPowerFamily f r) x := by
  obtain ⟨hc, hf, b, hb, heq⟩ := hu
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨div_pos hc hrR, holomorphicGeneratorsAt_tensorPowerFamily hf, b, hb, ?_⟩
  filter_upwards [heq] with y hy
  rw [hy, generatorLog_tensorPowerFamily,
    MultiplierIdealWeightLowerBound.coe_mul_coe_mul, div_mul_cancel₀ c hrR.ne']

/-- The actual rational common denominator and tensor families internally
produce same-coefficient presentations of both original weights. -/
theorem exists_common_coefficient_presentations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (hv : HasAnalyticSingularityTypeAt v x) :
    ∃ e : ℚ, ∃ N P : ℕ, ∃ F : Fin N → E → ℂ, ∃ G : Fin P → E → ℂ,
      LogarithmicTypeAt u (e : ℝ) F x ∧ LogarithmicTypeAt v (e : ℝ) G x := by
  obtain ⟨c, N, f, huf⟩ := hu
  obtain ⟨d, P, g, hvg⟩ := hv
  have hcQ : (0 : ℚ) < c := by exact_mod_cast huf.1
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hvg.1
  let a : Fin 2 → ℚ := ![c, d]
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    fin_cases i
    · exact hcQ.le
    · exact hdQ.le
  obtain ⟨q, p, hq, hcoeff⟩ := MeteredDivisorSingleGenerator.exists_commonDenominator a ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcEq : (c : ℝ) = (p 0 : ℝ) / (q : ℝ) := by simpa only [a, Matrix.cons_val_zero] using hcoeff 0
  have hdEq : (d : ℝ) = (p 1 : ℝ) / (q : ℝ) := by
    simpa only [a, Matrix.cons_val_one, Matrix.cons_val_zero] using hcoeff 1
  have hp0R : (0 : ℝ) < p 0 := by
    rw [← (eq_div_iff hqR.ne').mp hcEq]
    exact mul_pos huf.1 hqR
  have hp1R : (0 : ℝ) < p 1 := by
    rw [← (eq_div_iff hqR.ne').mp hdEq]
    exact mul_pos hvg.1 hqR
  have hp0 : 0 < p 0 := by exact_mod_cast hp0R
  have hp1 : 0 < p 1 := by exact_mod_cast hp1R
  let e : ℚ := 1 / (q : ℚ)
  have hcNew : (c : ℝ) / (p 0 : ℝ) = (e : ℝ) := by
    dsimp only [e]
    push_cast
    rw [hcEq]
    field_simp
  have hdNew : (d : ℝ) / (p 1 : ℝ) = (e : ℝ) := by
    dsimp only [e]
    push_cast
    rw [hdEq]
    field_simp
  have huf' := logarithmicTypeAt_tensorPowerFamily huf hp0
  have hvg' := logarithmicTypeAt_tensorPowerFamily hvg hp1
  rw [hcNew] at huf'
  rw [hdNew] at hvg'
  exact ⟨e, _, _, tensorPowerFamily f (p 0), tensorPowerFamily g (p 1), huf', hvg'⟩

/-- A maximum preserves genuine rational analytic type without supplied
coefficient synchronization or a maximum presentation. -/
theorem hasAnalyticSingularityTypeAt_max
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (hv : HasAnalyticSingularityTypeAt v x) :
    HasAnalyticSingularityTypeAt (fun y => max (u y) (v y)) x := by
  obtain ⟨e, N, P, F, G, hu', hv'⟩ := exists_common_coefficient_presentations hu hv
  exact DemaillyAnalyticType.HasAnalyticSingularityTypeAt.max_of_generators hu' hv'

end

end SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum
