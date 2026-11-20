import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false

/-! # Actual sign-region domination and integrability from positive measure balance -/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.PositiveMeasureDensityBalance

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A positive additive balance with mutually singular defects yields genuine domination without cancellation of infinite measures. -/
theorem mutuallySingular_le_of_add_balance {m₁ m₂ A B : Measure X}
    (hbalance : m₁ + B = m₂ + A) (hsingular : A ⟂ₘ B) :
    A ≤ m₁ ∧ B ≤ m₂ := by
  obtain ⟨S, hS, hAS, hBSc⟩ := hsingular
  have hArS : A.restrict S = 0 := Measure.restrict_eq_zero.mpr hAS
  have hBrSc : B.restrict Sᶜ = 0 := Measure.restrict_eq_zero.mpr hBSc
  have hArSc : A.restrict Sᶜ = A := by
    simpa only [hArS, zero_add] using Measure.restrict_add_restrict_compl (μ := A) hS
  have hBrS : B.restrict S = B := by
    simpa only [hBrSc, add_zero] using Measure.restrict_add_restrict_compl (μ := B) hS
  have hSc := congrArg (fun m : Measure X => m.restrict Sᶜ) hbalance
  have hSr := congrArg (fun m : Measure X => m.restrict S) hbalance
  simp only [Measure.restrict_add, hBrSc, hArSc, add_zero] at hSc
  simp only [Measure.restrict_add, hBrS, hArS, add_zero] at hSr
  constructor
  · exact (Measure.le_add_left (ν' := m₂.restrict Sᶜ) (le_refl A)).trans
      (hSc.symm.le.trans Measure.restrict_le_self)
  · exact (Measure.le_add_left (ν' := m₁.restrict S) (le_refl B)).trans
      (hSr.le.trans Measure.restrict_le_self)

/-- The actual positive and negative real densities have measurable disjoint sign regions, hence the positive balance genuinely dominates each density. -/
theorem withDensity_ofReal_le_of_add_balance {m₁ m₂ μ : Measure X}
    {c : X → ℝ} (hc : Measurable c)
    (hbalance : m₁ + μ.withDensity (fun x => ENNReal.ofReal (-c x)) =
      m₂ + μ.withDensity (fun x => ENNReal.ofReal (c x))) :
    μ.withDensity (fun x => ENNReal.ofReal (c x)) ≤ m₁ ∧
      μ.withDensity (fun x => ENNReal.ofReal (-c x)) ≤ m₂ :=
  mutuallySingular_le_of_add_balance hbalance (withDensity_ofReal_mutuallySingular hc)

/-- Two natural regularizer integrability facts produce both the signed density integrability and its actual real integral defect, without baseline mass finiteness. -/
theorem integrable_mul_and_integral_sub_of_density_balance {m₁ m₂ μ : Measure X}
    {c : X → ℝ} (hc : Measurable c)
    (hbalance : m₁ + μ.withDensity (fun x => ENNReal.ofReal (-c x)) =
      m₂ + μ.withDensity (fun x => ENNReal.ofReal (c x)))
    {H : X → ℝ} (h₁ : Integrable H m₁) (h₂ : Integrable H m₂) :
    Integrable (fun x => H x * c x) μ ∧
      (∫ x, H x ∂m₁) - (∫ x, H x ∂m₂) = ∫ x, H x * c x ∂μ := by
  have hcn : Measurable (fun x => -c x) := hc.neg
  have hdom := withDensity_ofReal_le_of_add_balance hc hbalance
  have hplus : Integrable H (μ.withDensity (fun x => ENNReal.ofReal (c x))) := h₁.mono_measure hdom.1
  have hminus : Integrable H (μ.withDensity (fun x => ENNReal.ofReal (-c x))) := h₂.mono_measure hdom.2
  have hcp : Integrable (fun x => H x * max (c x) 0) μ := by
    have h := (integrable_withDensity_iff_integrable_smul' hc.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hplus
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using h
  have hcm : Integrable (fun x => H x * max (-c x) 0) μ := by
    have h := (integrable_withDensity_iff_integrable_smul' hcn.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hminus
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using h
  have heq : (fun x => H x * max (c x) 0 - H x * max (-c x) 0) = fun x => H x * c x := by
    funext x
    by_cases h : 0 ≤ c x
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), mul_zero, sub_zero]
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring
  refine ⟨heq ▸ hcp.sub hcm, ?_⟩
  have hint := congrArg (fun m : Measure X => ∫ x, H x ∂m) hbalance
  rw [integral_add_measure h₁ hminus, integral_add_measure h₂ hplus,
    integral_withDensity_eq_integral_toReal_smul hcn.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hc.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hint
  simp only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] at hint
  have hparts : (∫ x, H x * c x ∂μ) =
      (∫ x, H x * max (c x) 0 ∂μ) - (∫ x, H x * max (-c x) 0 ∂μ) := by
    rw [← heq, integral_sub hcp hcm]
  linarith

end

end SGPT.Foundations.Analysis.Pending.PositiveMeasureDensityBalance
