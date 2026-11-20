import SGPT.Trace.TwistedL2Statement
import Mathlib.Analysis.Complex.Norm

/-!
# Exact Young remainder for the twisted adjoint

Pointwise support for the twisted L² argument. For positive original twists a,b and actual
complex values u,v, the error made when replacing the adjoint for the weight
φ−log a by the original adjoint is the displayed nonnegative square. This is
an independent algebraic input toward the global twisting calculation; it
does not assume or prove a Bochner--Kodaira inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2.FunctionalTwistedYoungDraft

open Complex
open scoped ComplexConjugate

/-- The exact pointwise positive remainder in the twisted-adjoint estimate.
No order assumption on b is required for the equality. -/
theorem twistedYoung_exact (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (u v : ℂ) :
    (a + b) * ‖u‖ ^ 2 + (a⁻¹ + b⁻¹) * ‖v‖ ^ 2 -
        a * ‖u - ((a⁻¹ : ℝ) : ℂ) * v‖ ^ 2 =
      b⁻¹ * ‖(b : ℂ) * u + v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  field_simp [ha, hb]
  ring

/-- The twisted-adjoint bound with the exact coefficients needed when the
weight is changed by −log a. -/
theorem twistedYoung_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : ℂ) :
    a * ‖u - ((a⁻¹ : ℝ) : ℂ) * v‖ ^ 2 ≤
      (a + b) * ‖u‖ ^ 2 + (a⁻¹ + b⁻¹) * ‖v‖ ^ 2 := by
  have h := twistedYoung_exact a b ha.ne' hb.ne' u v
  have hnonneg : 0 ≤ b⁻¹ * ‖(b : ℂ) * u + v‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hb.le) (sq_nonneg _)
  linarith

/-- A denominator-free version that avoids choosing square roots and remains
valid when b is zero. -/
theorem twistedYoung_polynomial (a b : ℝ) (u v : ℂ) :
    a * b * (a + b) * ‖u‖ ^ 2 + (a + b) * ‖v‖ ^ 2 -
        b * ‖(a : ℂ) * u - v‖ ^ 2 = a * ‖(b : ℂ) * u + v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  ring

end SGPT.Trace.TwistedL2.FunctionalTwistedYoungDraft
