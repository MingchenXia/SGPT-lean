import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure

set_option autoImplicit false

/-! Actual calibrated AC top measure of a positive weak-current limit.
The full owned BP statement and entire proof precede Lean. No limit-density
or finite-mass certificate, analytic type or CY existence is an input. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.CalibratedCurrentWeakACLimit
open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  LocalProductCurrents LocalCurrentDeterminant PositiveCurrentACTopMeasure

variable {m : ℕ} {U : Opens (ComplexModel (m+1))}

private theorem topDensity_eq_det {S : LocalProductCurrent (m+1) U m}
    (hS : IsPositive S) (x : ComplexModel (m+1)) :
    actualTopPowerDensity (acForm hS x) =
      ((m+1).factorial : ℝ) / Real.pi ^ (m+1) * (acMatrix hS x).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hS x),
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- A real calibration of every original sequence term, with one convergent
scalar coefficient, produces an actual complete measure bound for the limit. -/
theorem acTopMeasure_ge_of_calibrated_weak_limits
    {T : ℕ → LocalProductCurrent (m+1) U m}
    {T₀ : LocalProductCurrent (m+1) U m}
    (hT : ∀ k, IsPositive (T k)) (hT₀ : IsPositive T₀)
    (hconv : ∀ γ φ, Tendsto (fun k => T k γ φ) atTop (𝓝 (T₀ γ φ)))
    {c : ℕ → ℝ} {a : ℝ} (hc : ∀ k, 0 ≤ c k)
    (hca : Tendsto c atTop (𝓝 a))
    {w : ComplexModel (m+1) → ℝ} (hw : ∀ x ∈ U, 0 ≤ w x)
    (hcal : ∀ k, ∀ᵐ x ∂volume.restrict U,
      actualTopPowerDensity (acForm (hT k) x) = c k * w x) :
    (volume.withDensity (fun x => ENNReal.ofReal (a * w x))).restrict U ≤
      acTopMeasure hT₀ := by
  have ha : 0 ≤ a := ge_of_tendsto hca (Eventually.of_forall hc)
  let N : ℝ := ((m+1).factorial : ℝ) / Real.pi ^ (m+1)
  let r : ℝ := ((m+1 : ℕ) : ℝ)⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hsem := ae_liminf_rpow_det_acMatrix_le hT hT₀ hconv
  have hpsd := ae_posSemidef_acMatrix hT₀
  have hcalall := ae_all_iff.mpr hcal
  have hbound : ∀ᵐ x ∂volume.restrict U,
      a * w x ≤ actualTopPowerDensity (acForm hT₀ x) := by
    filter_upwards [ae_restrict_of_ae hsem,ae_restrict_of_ae hpsd,
      hcalall,ae_restrict_mem U.isOpen.measurableSet] with x hx hxpsd hxcal hxU
    have hdet (k : ℕ) : (acMatrix (hT k) x).det.re = c k * w x / N := by
      have he := hxcal k
      rw [topDensity_eq_det] at he
      dsimp [N]
      apply (eq_div_iff hN.ne').mpr
      simpa only [mul_comm] using he
    have hfun : Continuous (fun t : ℝ => (t * w x / N) ^ r) :=
      (continuous_id.mul_const (w x) |>.div_const N).rpow_const
        (fun _ => Or.inr hr.le)
    have hroot : Tendsto (fun k => ENNReal.ofReal ((acMatrix (hT k) x).det.re ^ r))
        atTop (𝓝 (ENNReal.ofReal ((a * w x / N) ^ r))) := by
      simp_rw [hdet]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((hfun.tendsto a).comp hca)
    have hrootle : ENNReal.ofReal ((a * w x / N) ^ r) ≤
        ENNReal.ofReal ((acMatrix hT₀ x).det.re ^ r) := by
      have hlim := hx hxU
      change liminf (fun k => ENNReal.ofReal ((acMatrix (hT k) x).det.re ^ r)) atTop ≤ _ at hlim
      rw [hroot.liminf_eq] at hlim
      exact hlim
    have hrootle' := (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg (MinkowskiDeterminant.re_det_nonneg hxpsd) r)).mp hrootle
    have hbase := (Real.rpow_le_rpow_iff
      (div_nonneg (mul_nonneg ha (hw x hxU)) hN.le)
      (MinkowskiDeterminant.re_det_nonneg hxpsd) hr).mp hrootle'
    rw [topDensity_eq_det]
    simpa only [N,mul_comm] using (div_le_iff₀ hN).mp hbase
  unfold acTopMeasure
  rw [restrict_withDensity U.isOpen.measurableSet,
    restrict_withDensity U.isOpen.measurableSet]
  exact withDensity_mono (hbound.mono fun _ h => ENNReal.ofReal_le_ofReal h)

end SGPT.Foundations.Analysis.Pending.CalibratedCurrentWeakACLimit
