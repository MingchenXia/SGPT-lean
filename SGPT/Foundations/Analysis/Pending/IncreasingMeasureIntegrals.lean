import SGPT.Foundations.Analysis.FirstPass.IncreasingMeasures
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

/-! # Nonnegative integrals at actual increasing measure limits

No finiteness assumption is imposed. These measure-theoretic producers
support genuine non-pluripolar truncation limits.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.IncreasingMeasureIntegrals

open FirstPass.IncreasingMeasures

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Nonnegative measurable integration commutes with the actual increasing
measure limit, including infinite integrals. -/
theorem lintegral_increasingLimit (μ : ℕ → Measure X) (hμ : Monotone μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂increasingLimit μ hμ) = ⨆ k, ∫⁻ x, f x ∂μ k := by
  have hs (s : SimpleFunc X ℝ≥0∞) :
      s.lintegral (increasingLimit μ hμ) = ⨆ k, s.lintegral (μ k) := by
    simp only [SimpleFunc.lintegral]
    simp_rw [increasingLimit_apply_measurable μ hμ (s.measurableSet_preimage _),
      ENNReal.mul_iSup]
    apply ENNReal.finsetSum_iSup_of_monotone
    intro c k l hkl
    dsimp only
    gcongr
    exact hμ hkl
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]
  rw [iSup_comm]
  exact iSup_congr fun j => hs (SimpleFunc.eapprox f j)

/-- A finite shift of truncation levels preserves the actual limit measure. -/
theorem increasingLimit_add (μ : ℕ → Measure X) (hμ : Monotone μ) (r : ℕ) :
    increasingLimit (fun k => μ (k + r))
      (fun _ _ hkl => hμ (Nat.add_le_add_right hkl r)) = increasingLimit μ hμ := by
  apply Measure.ext
  intro E hE
  rw [increasingLimit_apply_measurable (fun k => μ (k + r))
    (fun _ _ hkl => hμ (Nat.add_le_add_right hkl r)) hE,
    increasingLimit_apply_measurable μ hμ hE]
  apply le_antisymm
  · exact iSup_le fun k => le_iSup (fun j => μ j E) (k + r)
  · exact iSup_le fun k =>
      (Measure.le_iff'.mp (hμ (Nat.le_add_right k r)) E).trans
        (le_iSup (fun j => μ (j + r) E) k)

end

end SGPT.Foundations.Analysis.Pending.IncreasingMeasureIntegrals
