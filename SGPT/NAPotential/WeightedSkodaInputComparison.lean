import SGPT.Okounkov.TranscendentalSkodaRegularization

/-!
# Domination of regularized Skoda input densities

The finite input integral for the original tuple and psh weight controls the
smooth-weight division inputs.  This pointwise inequality is valid at common
zeros of the tuple, at poles of the psh weight, and when the holomorphic
numerator vanishes; no solution or bound certificate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalSkoda

variable {n r : ℕ}

/-- The actual regularized input density is bounded by the original one.
The only comparison assumption is that the real smooth approximant dominates
the original extended-real weight at this point. -/
theorem regularized_input_density_le
    (g : Fin r → ComplexModel n → ℂ) (f : ComplexModel n → ℂ)
    {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    {ψ : ComplexModel n → EReal} {s : ℝ} {z : ComplexModel n}
    (hψ : ψ z ≤ (s : EReal)) :
    ENNReal.ofReal (‖f z‖ ^ 2 * (generatorNormSq g z + δ) ^ (-q) * Real.exp (-s)) ≤
      ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight q (generatorLog g z) *
        multiplierWeight 1 (ψ z) := by
  have hS : 0 ≤ generatorNormSq g z + δ := by
    linarith [generatorNormSq_nonneg g z]
  have hwg : ENNReal.ofReal ((generatorNormSq g z + δ) ^ (-q)) ≤
      multiplierWeight q (generatorLog g z) :=
    ofReal_rpow_le_multiplierWeight g hq hδ z
  have hwψ : ENNReal.ofReal (Real.exp (-s)) ≤ multiplierWeight 1 (ψ z) := by
    have h := multiplierWeight_antitone (c := (1 : ℝ)) (by norm_num) hψ
    rw [multiplierWeight_coe, one_mul] at h
    exact h
  calc
    _ = ENNReal.ofReal (‖f z‖ ^ 2) *
        ENNReal.ofReal ((generatorNormSq g z + δ) ^ (-q)) *
        ENNReal.ofReal (Real.exp (-s)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS _)),
        ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ _ := mul_le_mul' (mul_le_mul_of_nonneg_left hwg zero_le) hwψ

end SGPT.NAPotential.GAGAMult
