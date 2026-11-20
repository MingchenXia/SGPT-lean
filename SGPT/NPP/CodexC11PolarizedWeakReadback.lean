import SGPT.NPP.CodexC11PolarizingDirections

/-! Distributional real and imaginary complex-Hessian entries obtained by
the repository's exact four-direction polarization formula.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11PolarizedWeakReadback.lean` (module `C11PolarizedWeakReadback`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Envelopes.DNTC11

namespace SGPT.NPP.Codex.C11PolarizedWeakReadback
variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- A pair of actual directional weak identities determines the real part of
the corresponding complex-Hessian test pairing, with the native factor 1/4. -/
theorem real_component_pairing
    {g : ComplexModel n → ℝ} (hg : LocallyIntegrableOn g Ω volume)
    (j k : Fin n) (φ : 𝓓(Ω, ℝ))
    (a b : ℝ)
    (ha : (∫ z, g z * leviForm φ z (polVec j k 0)) = a)
    (hb : (∫ z, g z * leviForm φ z (polVec j k 1)) = b) :
    (∫ z, g z * (complexHessian φ z j k).re) = (a-b)/4 := by
  have h0 := integrable_mul_leviForm_testFunction hg φ (polVec j k 0)
  have h1 := integrable_mul_leviForm_testFunction hg φ (polVec j k 1)
  have hφ2 : ContDiff ℝ 2 (φ : ComplexModel n → ℝ) :=
    φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  calc
    (∫ z, g z * (complexHessian φ z j k).re) =
      ∫ z, (g z * leviForm φ z (polVec j k 0) -
        g z * leviForm φ z (polVec j k 1)) / 4 := by
          apply integral_congr_ae
          filter_upwards with z
          rw [complexHessian_eq_polarize hφ2.contDiffAt]
          simp only [polarize, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
          ring
    _ = ((∫ z, g z * leviForm φ z (polVec j k 0)) -
        (∫ z, g z * leviForm φ z (polVec j k 1))) / 4 := by
          rw [integral_div, integral_sub h0 h1]
    _ = (a-b)/4 := by rw [ha,hb]

/-- The corresponding imaginary component uses the `± i eₖ` directions,
with the same native polarization convention. -/
theorem imaginary_component_pairing
    {g : ComplexModel n → ℝ} (hg : LocallyIntegrableOn g Ω volume)
    (j k : Fin n) (φ : 𝓓(Ω, ℝ))
    (a b : ℝ)
    (ha : (∫ z, g z * leviForm φ z (polVec j k 2)) = a)
    (hb : (∫ z, g z * leviForm φ z (polVec j k 3)) = b) :
    (∫ z, g z * (complexHessian φ z j k).im) = (a-b)/4 := by
  have h0 := integrable_mul_leviForm_testFunction hg φ (polVec j k 2)
  have h1 := integrable_mul_leviForm_testFunction hg φ (polVec j k 3)
  have hφ2 : ContDiff ℝ 2 (φ : ComplexModel n → ℝ) :=
    φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  calc
    (∫ z, g z * (complexHessian φ z j k).im) =
      ∫ z, (g z * leviForm φ z (polVec j k 2) -
        g z * leviForm φ z (polVec j k 3)) / 4 := by
          apply integral_congr_ae
          filter_upwards with z
          rw [complexHessian_eq_polarize hφ2.contDiffAt]
          simp only [polarize, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
          ring
    _ = ((∫ z, g z * leviForm φ z (polVec j k 2)) -
        (∫ z, g z * leviForm φ z (polVec j k 3))) / 4 := by
          rw [integral_div, integral_sub h0 h1]
    _ = (a-b)/4 := by rw [ha,hb]

end SGPT.NPP.Codex.C11PolarizedWeakReadback
