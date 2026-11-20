import SGPT.Convex.GrowthClasses
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open MeasureTheory
open scoped ENNReal

private theorem positive_upper_gap (C : ℝ) (hC : 0 ≤ C) (z : EReal)
    (hz : z ≤ (C : EReal)) :
    z.toENNReal + ((C : EReal) - z).toENNReal =
      ENNReal.ofReal C + (-z).toENNReal := by
  induction z using EReal.rec with
  | bot => simp
  | top => exact False.elim (EReal.coe_ne_top C (top_le_iff.mp hz))
  | coe r =>
    have hr : r ≤ C := EReal.coe_le_coe_iff.mp hz
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    by_cases hr0 : 0 ≤ r
    · rw [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hr0), add_zero,
        ← ENNReal.ofReal_add hr0 (sub_nonneg.mpr hr)]
      congr 1
      ring
    · have hrn : r ≤ 0 := le_of_lt (lt_of_not_ge hr0)
      rw [ENNReal.ofReal_eq_zero.mpr hrn, zero_add,
        ← ENNReal.ofReal_add hC (neg_nonneg.mpr hrn)]
      congr 1

/-- The actual extended signed integral of a measurable function with a finite
upper bound. Infinite negative values are retained. -/
theorem extendedSignedIntegral_eq_upper_gap {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] {H : A → EReal} (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hle : H ≤ᵐ[μ] fun _ => (C : EReal)) :
    extendedSignedIntegral μ H =
      ((ENNReal.ofReal C * μ Set.univ : ℝ≥0∞) : EReal) -
        ((∫⁻ x, ((C : EReal) - H x).toENNReal ∂μ) : EReal) := by
  let p : ℝ≥0∞ := ∫⁻ x, (H x).toENNReal ∂μ
  let n : ℝ≥0∞ := ∫⁻ x, (-H x).toENNReal ∂μ
  let i : ℝ≥0∞ := ∫⁻ x, ((C : EReal) - H x).toENNReal ∂μ
  let d : ℝ≥0∞ := ENNReal.ofReal C * μ Set.univ
  have hp : Measurable (fun x => (H x).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp hH
  have hn : Measurable (fun x => (-H x).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp hH.neg
  have hi : Measurable (fun x => ((C : EReal) - H x).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_const.sub hH)
  have hd : d < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
  have hpd : p ≤ d := by
    calc
      p ≤ ∫⁻ _x : A, ENNReal.ofReal C ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hle] with x hx
        simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hx
      _ = d := by simp [d]
  have hpf : p < ⊤ := lt_of_le_of_lt hpd hd
  have hsum : p + i = d + n := by
    calc
      p + i = ∫⁻ x, (H x).toENNReal + ((C : EReal) - H x).toENNReal ∂μ :=
        (lintegral_add_left hp _).symm
      _ = ∫⁻ x, ENNReal.ofReal C + (-H x).toENNReal ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hle] with x hx
        exact positive_upper_gap C hC (H x) hx
      _ = d + n := by rw [lintegral_add_left measurable_const]; simp [d, n]
  change (p : EReal) - (n : EReal) = (d : EReal) - (i : EReal)
  by_cases hit : i = ⊤
  · have hnt : n = ⊤ := by
      have h : d + n = ⊤ := by rw [← hsum, hit, add_top]
      exact (ENNReal.add_eq_top.mp h).resolve_left hd.ne
    rw [hit, hnt]
    simp only [EReal.coe_ennreal_top, EReal.sub_top]
  · have hif : i < ⊤ := lt_top_iff_ne_top.mpr hit
    have hnf : n < ⊤ := by
      have h : d + n < ⊤ := hsum ▸ ENNReal.add_lt_top.mpr ⟨hpf, hif⟩
      exact (ENNReal.add_lt_top.mp h).2
    have hreal := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hpf.ne hit, ENNReal.toReal_add hd.ne hnf.ne] at hreal
    rw [← EReal.coe_ennreal_toReal hpf.ne, ← EReal.coe_ennreal_toReal hnf.ne,
      ← EReal.coe_ennreal_toReal hd.ne, ← EReal.coe_ennreal_toReal hit,
      ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith
end SGPT.Convex
