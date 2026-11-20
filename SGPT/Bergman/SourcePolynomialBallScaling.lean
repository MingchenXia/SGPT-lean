import SGPT.Foundations.Analysis.Pending.BergmanKernelSmooth
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# PolynomialBallScaling

Balls of radius `r/√k` and their Haar volume in `ℂⁿ` (local step for `h⁰ = O(kⁿ)`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set Metric MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped ENNReal

/-- The actual shrinking radius; no asymptotic or growth bound is supplied. -/
def polynomialRadius (r : ℝ) (k : ℕ) : ℝ := r / Real.sqrt k

theorem polynomialRadius_pos {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : 0 < k) :
    0 < polynomialRadius r k := div_pos hr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))

theorem polynomialRadius_le {r : ℝ} (hr : 0 ≤ r) {k : ℕ} (hk : 0 < k) :
    polynomialRadius r k ≤ r := by
  have hs : 1 ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hk)
  exact div_le_self hr hs

theorem polynomialRadius_sq {r : ℝ} {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * polynomialRadius r k ^ 2 = r ^ 2 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  dsimp only [polynomialRadius]
  rw [div_pow, hs]
  exact mul_div_cancel₀ _ (by exact_mod_cast hk.ne')

/-- Exact real dimension 2n, including n=0. -/
theorem complexModel_real_finrank (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex]
  simp [ComplexModel]

/-- Actual Haar ball scaling on the genuine complex model, without a
nontrivial-space hypothesis; the zero-dimensional ball is retained. -/
theorem polynomialRadius_ball_volume (n : ℕ) (a : ComplexModel n) {r : ℝ}
    {k : ℕ} (hk : 0 < k) :
    ENNReal.ofReal ((k : ℝ) ^ n) * volume (ball a (polynomialRadius r k)) =
      volume (ball (0 : ComplexModel n) r) := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkp
  have he : ((Real.sqrt (k : ℝ))⁻¹) ^ (2 * n) = ((k : ℝ) ^ n)⁻¹ := by
    rw [pow_mul, inv_pow, Real.sq_sqrt hkp.le, inv_pow]
  have hscale := Measure.addHaar_ball_mul_of_pos volume a (inv_pos.mpr hs) r
  rw [complexModel_real_finrank, he] at hscale
  have hradius : polynomialRadius r k = (Real.sqrt (k : ℝ))⁻¹ * r := by
    simp only [polynomialRadius, div_eq_inv_mul]
  rw [hradius, hscale, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hkp.le _),
    mul_inv_cancel₀ (pow_ne_zero _ hkp.ne'), ENNReal.ofReal_one, one_mul]

end SGPT.Bergman.PolynomialH0Growth
