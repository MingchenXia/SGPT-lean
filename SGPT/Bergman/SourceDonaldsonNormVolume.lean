import SGPT.Bergman.SourceComplexNormBalls

/-!
# DonaldsonNormVolume

The log-volume ratio of norm unit balls and the Donaldson functional `n!/k^{n+1} log (vol{H ≤ 1}/vol{H₀ ≤ 1})`; independence of the Haar normalization and the comparison estimate used in source `lma:BML`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.QuantizationFrontier
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
  (vol ν : Measure E) [hvol : vol.IsAddHaarMeasure] [hν : ν.IsAddHaarMeasure]

include hvol in
/-- Ratio of ACTUAL real Haar volumes of entire original norm unit balls. -/
def normBallVolumeRatio (N N0 : ComplexNorm E) : ℝ :=
  vol.real (normUnitBall N) / vol.real (normUnitBall N0)

omit [BorelSpace E] in
/-- A genuine finite positive ratio, proved from actual norm-ball geometry. -/
theorem normBallVolumeRatio_pos (N N0 : ComplexNorm E) : 0 < normBallVolumeRatio vol N N0 :=
  div_pos (normUnitBall_real_pos vol N) (normUnitBall_real_pos vol N0)

/-- Arbitrary genuine Haar normalization cancels in BOTH actual volumes; no invariance input. -/
theorem normBallVolumeRatio_haarIndependent (N N0 : ComplexNorm E) :
    normBallVolumeRatio ν N N0 = normBallVolumeRatio vol N N0 := by
  have hc : (addHaarScalarFactor ν vol : ℝ) ≠ 0 :=
    ne_of_gt (NNReal.coe_pos.mpr (addHaarScalarFactor_pos_of_isAddHaarMeasure ν vol))
  unfold normBallVolumeRatio
  rw [isAddLeftInvariant_eq_smul ν vol]
  simp only [measureReal_nnreal_smul_apply]
  exact mul_div_mul_left _ _ hc

/-- The original source normalization is n!/k^(n+1), not its measure normalization n!/k^n. -/
def sourceDonaldsonNormalization (n k : ℕ) : ℝ := (n.factorial : ℝ) / (k : ℝ) ^ (n + 1)

/-- Literal source L942 on actual entire norm balls with an actual reference norm. -/
def sourceDonaldsonFunctional (n k : ℕ) (N N0 : ComplexNorm E) : ℝ :=
  sourceDonaldsonNormalization n k * Real.log (normBallVolumeRatio vol N N0)

/-- Independence of the actual arbitrary source Lebesgue/Haar normalization is PROVED. -/
theorem sourceDonaldsonFunctional_haarIndependent (n k : ℕ) (N N0 : ComplexNorm E) :
    sourceDonaldsonFunctional ν n k N N0 = sourceDonaldsonFunctional vol n k N N0 := by
  rw [sourceDonaldsonFunctional, sourceDonaldsonFunctional,
    normBallVolumeRatio_haarIndependent vol ν]

omit [BorelSpace E] in
/-- A genuine norm compared to itself has exactly the original zero log-volume ratio. -/
theorem sourceDonaldsonFunctional_self (n k : ℕ) (N : ComplexNorm E) :
    sourceDonaldsonFunctional vol n k N N = 0 := by
  unfold sourceDonaldsonFunctional normBallVolumeRatio
  rw [div_self (normUnitBall_real_pos vol N).ne', Real.log_one, mul_zero]

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- In the genuine zero-vector space every original norm ball is the whole space. -/
theorem normUnitBall_eq_univ [Subsingleton E] (N : ComplexNorm E) : normUnitBall N = univ := by
  ext x
  simp only [normUnitBall, mem_ofPred_eq, mem_univ, iff_true]
  rw [Subsingleton.elim x 0, map_zero]
  norm_num

omit [BorelSpace E] in
/-- Every pair of genuine norms on a zero-dimensional space gives true source functional zero. -/
theorem sourceDonaldsonFunctional_zeroDim (n k : ℕ) (N N0 : ComplexNorm E)
    (hdim : Module.finrank ℂ E = 0) : sourceDonaldsonFunctional vol n k N N0 = 0 := by
  have : Subsingleton E := Module.finrank_zero_iff.mp hdim
  have h : normUnitBall N0 = normUnitBall N := by rw [normUnitBall_eq_univ, normUnitBall_eq_univ]
  unfold sourceDonaldsonFunctional normBallVolumeRatio
  rw [h, div_self (normUnitBall_real_pos vol N).ne', Real.log_one, mul_zero]

omit [BorelSpace E] in
/-- Positive finite actual balls justify the real logarithm quotient formula. -/
theorem log_normBallVolumeRatio (N N0 : ComplexNorm E) :
    Real.log (normBallVolumeRatio vol N N0) =
      Real.log (vol.real (normUnitBall N)) - Real.log (vol.real (normUnitBall N0)) :=
  Real.log_div (normUnitBall_real_pos vol N).ne' (normUnitBall_real_pos vol N0).ne'

omit [BorelSpace E] in
/-- The SAME actual reference cancels exactly from differences of the source functionals. -/
theorem sourceDonaldsonFunctional_difference (n k : ℕ) (N M N0 : ComplexNorm E) :
    sourceDonaldsonFunctional vol n k N N0 - sourceDonaldsonFunctional vol n k M N0 =
      sourceDonaldsonNormalization n k *
        (Real.log (vol.real (normUnitBall N)) - Real.log (vol.real (normUnitBall M))) := by
  unfold sourceDonaldsonFunctional
  rw [log_normBallVolumeRatio, log_normBallVolumeRatio]
  ring

/-- The positive-degree scalar is nonnegative, produced from the genuine degree. -/
theorem sourceDonaldsonNormalization_nonneg (n k : ℕ) : 0 ≤ sourceDonaldsonNormalization n k := by
  unfold sourceDonaldsonNormalization
  positivity

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- Exact homogeneity for real dilation on the SAME complex module. -/
theorem ComplexNorm.real_smul (N : ComplexNorm E) (a : ℝ) (x : E) :
    N.toAddGroupNorm (a • x) = |a| * N.toAddGroupNorm x := by
  rw [← algebraMap_smul ℂ a x]
  simpa only [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] using N.norm_smul (a : ℂ) x

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual norm inequality produces an entire unit-ball inclusion. -/
theorem normUnitBall_antitone (N M : ComplexNorm E)
    (hNM : ∀ x, N.toAddGroupNorm x ≤ M.toAddGroupNorm x) : normUnitBall M ⊆ normUnitBall N :=
  fun x hx => (hNM x).trans hx

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- The BM radius comparison is a TRUE constructed dilation inclusion, not supplied ball data. -/
theorem normUnitBall_subset_smul (N M : ComplexNorm E) {a : ℝ} (ha : 0 < a)
    (hMN : ∀ x, M.toAddGroupNorm x ≤ a * N.toAddGroupNorm x) :
    normUnitBall N ⊆ a • normUnitBall M := by
  intro x hx
  refine ⟨a⁻¹ • x, ?_, smul_inv_smul₀ ha.ne' x⟩
  change M.toAddGroupNorm (a⁻¹ • x) ≤ 1
  rw [ComplexNorm.real_smul, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ a⁻¹ * (a * N.toAddGroupNorm x) := mul_le_mul_of_nonneg_left (hMN x) (inv_nonneg.mpr ha.le)
    _ = N.toAddGroupNorm x := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    _ ≤ 1 := hx

/-- Real Haar scaling retains the exact factor 2*complex dimension, for all true norm balls. -/
theorem normUnitBall_real_smul (N : ComplexNorm E) {a : ℝ} (ha : 0 ≤ a) :
    vol.real (a • normUnitBall N) = a ^ (2 * Module.finrank ℂ E) * vol.real (normUnitBall N) := by
  change (vol (a • normUnitBall N)).toReal = _
  rw [normUnitBall_measure_smul vol N ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha _)]
  rfl

/-- Entire norm inequalities yield the true finite-degree log-volume bound, with exact real dimension. -/
theorem sourceDonaldsonFunctional_abs_difference_le
    (n k : ℕ) (N M N0 : ComplexNorm E) {a : ℝ} (ha : 1 ≤ a)
    (hNM : ∀ x, N.toAddGroupNorm x ≤ M.toAddGroupNorm x)
    (hMN : ∀ x, M.toAddGroupNorm x ≤ a * N.toAddGroupNorm x) :
    |sourceDonaldsonFunctional vol n k M N0 - sourceDonaldsonFunctional vol n k N N0| ≤
      sourceDonaldsonNormalization n k * ((2 * Module.finrank ℂ E : ℕ) : ℝ) * Real.log a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlow : vol.real (normUnitBall M) ≤ vol.real (normUnitBall N) :=
    measureReal_mono (normUnitBall_antitone N M hNM) (normUnitBall_measure_ne_top vol N)
  have htop : vol (a • normUnitBall M) ≠ ⊤ := by
    rw [normUnitBall_measure_smul vol M ha0.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (normUnitBall_measure_ne_top vol M)
  have hupp : vol.real (normUnitBall N) ≤
      a ^ (2 * Module.finrank ℂ E) * vol.real (normUnitBall M) := by
    rw [← normUnitBall_real_smul vol M ha0.le]
    exact measureReal_mono (normUnitBall_subset_smul N M ha0 hMN) htop
  have hloLog := Real.log_le_log (normUnitBall_real_pos vol M) hlow
  have hupLog := Real.log_le_log (normUnitBall_real_pos vol N) hupp
  rw [Real.log_mul (pow_pos ha0 _).ne' (normUnitBall_real_pos vol M).ne', Real.log_pow] at hupLog
  have hc := sourceDonaldsonNormalization_nonneg n k
  rw [sourceDonaldsonFunctional_difference vol n k M N N0]
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hloLog))]
  calc
    _ = sourceDonaldsonNormalization n k *
      (Real.log (vol.real (normUnitBall N)) - Real.log (vol.real (normUnitBall M))) := by ring
    _ ≤ sourceDonaldsonNormalization n k *
      (((2 * Module.finrank ℂ E : ℕ) : ℝ) * Real.log a) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end SGPT.Bergman.QuantizationFrontier
