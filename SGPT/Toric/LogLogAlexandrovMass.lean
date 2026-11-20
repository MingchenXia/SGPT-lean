import SGPT.Toric.LogLogProfile
import SGPT.Convex.HalfLine
import SGPT.Convex.SubgradientMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Convex
open scoped Topology ENNReal

/-- The original checked scalar cost supremum is the actual perfect-pairing conjugate. -/
theorem conjugate_scalar_logLogProfile (m : ℝ) :
    conjugate scalarPairing (fun x : ℝ => (logLogProfile x : EReal)) m =
      logLogConjugate m := by
  unfold conjugate logLogConjugate
  congr 1
  funext x
  change (↑(x * m) : EReal) - ↑(logLogProfile x) = ↑(m * x - logLogProfile x)
  rw [← EReal.coe_sub, mul_comm x m]

/-- The true conjugate domain includes slope one and excludes slope zero. -/
theorem effectiveDomain_conjugate_scalar_logLogProfile :
    effectiveDomain (conjugate scalarPairing (fun x : ℝ => (logLogProfile x : EReal))) =
      Ioc 0 1 := by
  ext m
  change conjugate scalarPairing (fun x : ℝ => (logLogProfile x : EReal)) m < ⊤ ↔
    0 < m ∧ m ≤ 1
  rw [conjugate_scalar_logLogProfile]
  by_cases hm : 0 < m
  · by_cases hm1 : m ≤ 1
    · refine ⟨fun _ => ⟨hm, hm1⟩, fun _ => ?_⟩
      by_cases hmb : m ≤ logLogLambda⁻¹
      · rw [logLogConjugate_small hm hmb]
        exact EReal.coe_lt_top _
      · rw [logLogConjugate_large (le_of_lt (lt_of_not_ge hmb)) hm1]
        exact EReal.coe_lt_top _
    · rw [logLogConjugate_one_lt (lt_of_not_ge hm1)]
      simp [hm1]
  · rw [logLogConjugate_nonpos (le_of_not_gt hm)]
    simp [hm]

/-- This is the checked Alexandrov pushforward, not an independently prescribed mass. -/
def logLogAlexandrovMeasure : Measure ℝ :=
  alexandrovMeasure scalarPairing volume (fun x : ℝ => (logLogProfile x : EReal))

/-- Actual total mass, from the original open dual interval and canonical Lebesgue measure. -/
theorem logLogAlexandrovMeasure_univ : logLogAlexandrovMeasure univ = 1 := by
  rw [logLogAlexandrovMeasure, alexandrovMeasure_univ,
    effectiveDomain_conjugate_scalar_logLogProfile, interior_Ioc, Real.volume_Ioo]
  simp

/-- At the actual corner, the raw inequality is exactly attained conjugate cost. -/
theorem mem_rawSubdifferential_logLog_corner_iff {m : ℝ} :
    m ∈ rawSubdifferential scalarPairing (fun x : ℝ => (logLogProfile x : EReal))
        (-logLogLambda) ↔
      logLogConjugate m = (((1 - m) * logLogLambda - 2 : ℝ) : EReal) := by
  have hp := isProper_coe_of_convexOn convexOn_logLogProfile
  rw [rawSubdifferential_eq_subdifferential_of_isProper scalarPairing hp,
    mem_subdifferential_iff_fenchel scalarPairing hp
      (show -logLogLambda ∈ effectiveDomain (fun x : ℝ => (logLogProfile x : EReal)) by
        exact EReal.coe_lt_top _), conjugate_scalar_logLogProfile,
    logLogProfile_neg_lambda]
  change (logLogConjugate m = (↑((-logLogLambda) * m) : EReal) -
    ↑(2 - logLogLambda)) ↔ _
  rw [← EReal.coe_sub]
  have hcost : (-logLogLambda) * m - (2 - logLogLambda) =
      (1 - m) * logLogLambda - 2 := by ring
  rw [hcost]

/-- The real circle mass comes from the whole interval of actual touching slopes. -/
theorem rawSubdifferential_logLog_corner :
    rawSubdifferential scalarPairing (fun x : ℝ => (logLogProfile x : EReal))
      (-logLogLambda) = Icc logLogLambda⁻¹ 1 := by
  ext m
  rw [mem_rawSubdifferential_logLog_corner_iff]
  constructor
  · intro heq
    have hmDom : m ∈ effectiveDomain
        (conjugate scalarPairing (fun x : ℝ => (logLogProfile x : EReal))) := by
      change conjugate scalarPairing (fun x : ℝ => (logLogProfile x : EReal)) m < ⊤
      rw [conjugate_scalar_logLogProfile, heq]
      exact EReal.coe_lt_top _
    rw [effectiveDomain_conjugate_scalar_logLogProfile] at hmDom
    refine ⟨?_, hmDom.2⟩
    by_contra hmLow
    have hmLt : m < logLogLambda⁻¹ := lt_of_not_ge hmLow
    have hell : 0 < logLogLambda := by linarith [logLogLambda_gt_two]
    have hprod : m * logLogLambda < 1 := by
      have h := (mul_lt_mul_of_pos_right hmLt hell)
      simpa only [inv_mul_cancel₀ (ne_of_gt hell)] using h
    have hstrict := Real.log_lt_sub_one_of_pos (mul_pos hmDom.1 hell)
      (ne_of_lt hprod)
    rw [Real.log_mul (ne_of_gt hmDom.1) (ne_of_gt hell), log_logLogLambda] at hstrict
    rw [logLogConjugate_small hmDom.1 hmLt.le] at heq
    have hreal := EReal.coe_injective heq
    nlinarith
  · intro hm
    exact logLogConjugate_large hm.1 hm.2

/-- The actual singleton image contains every touching slope, including both endpoints. -/
theorem rawSubgradientImageOn_logLog_corner :
    rawSubgradientImageOn scalarPairing (fun x : ℝ => (logLogProfile x : EReal))
      {-logLogLambda} = Icc logLogLambda⁻¹ 1 := by
  rw [rawSubgradientImageOn]
  simpa only [mem_singleton_iff, iUnion_iUnion_eq_left] using rawSubdifferential_logLog_corner

/-- The corner atom omitted by a classical AE second-derivative integral. -/
theorem logLogAlexandrovMeasure_corner :
    logLogAlexandrovMeasure {-logLogLambda} = ENNReal.ofReal (1 - logLogLambda⁻¹) := by
  rw [logLogAlexandrovMeasure,
    alexandrovMeasure_apply_coe scalarPairing convexOn_logLogProfile
      (measurableSet_singleton (-logLogLambda)),
    rawSubgradientImageOn_logLog_corner, Real.volume_Icc]
  simp

/-- The actual jump mass is strictly positive, since the crossing is greater than two. -/
theorem logLogAlexandrovMeasure_corner_pos : 0 < logLogAlexandrovMeasure {-logLogLambda} := by
  rw [logLogAlexandrovMeasure_corner]
  apply ENNReal.ofReal_pos.mpr
  have hell : 0 < logLogLambda := by linarith [logLogLambda_gt_two]
  have hinv : logLogLambda⁻¹ < 1 := (inv_lt_one₀ hell).2 (by linarith [logLogLambda_gt_two])
  linarith

end SGPT.Toric
