import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

/-! A bounded scalar distribution on an open set is represented by an
essentially bounded density of the supplied finite reference measure.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-DETERMINANT-BRIDGE/BoundedDistributionDensity.lean` (module `BoundedDistributionDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions CompactlySupported ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation
namespace SGPT.NPP.Codex.BoundedDistributionDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

theorem exists_density_of_bounded_distribution
    (ξ : Measure Ω) [IsLocallyFiniteMeasure ξ] [IsFiniteMeasure ξ]
    (T : 𝓓'(Ω, ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      |T φ| ≤ C * ∫ x : Ω, φ x ∂ξ) :
    ∃ h : Ω → ℝ, Measurable h ∧ (∀ᵐ x ∂ξ, |h x| ≤ C) ∧
      ∀ φ : 𝓓(Ω, ℝ), T φ = ∫ x : Ω, φ x * h x ∂ξ := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let v : 𝓓'(Ω, ℝ) := subtypeRegularDistribution ξ (fun _ => C) (locallyIntegrable_const C)
  have hv (φ : 𝓓(Ω, ℝ)) : v φ = C * ∫ x : Ω, φ x ∂ξ := by
    rw [subtypeRegularDistribution_apply]
    simp only [mul_comm _ C, integral_const_mul]
  have hpos : PositiveDistribution (T + v) := by
    intro φ hφ
    have h := hbound φ hφ
    change 0 ≤ T φ + v φ
    rw [hv]
    linarith [neg_abs_le (T φ)]
  obtain ⟨μ,hμreg,hμloc,hμ⟩ := hpos.exists_regular_measure
  let : IsLocallyFiniteMeasure μ := hμloc
  let ν : Measure Ω := ENNReal.ofReal (2*C) • ξ
  have : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ξ _)⟩
  have hμν : μ ≤ ν := by
    apply Measure.le_of_testFunction_integral_le ν μ
    intro φ hφ
    rw [hμ φ]
    change T φ + v φ ≤ _
    rw [hv]
    have hφabs := le_abs_self (T φ)
    have hb := hbound φ hφ
    have hint : (∫ x : Ω, φ x ∂ν) = (2*C) * ∫ x : Ω, φ x ∂ξ := by
      rw [show ν = ENNReal.ofReal (2*C) • ξ from rfl, integral_smul_measure]
      simp [hC, smul_eq_mul]
    rw [hint]
    linarith
  have hμξ : μ ≪ ξ := (Measure.absolutelyContinuous_of_le hμν).trans Measure.smul_absolutelyContinuous
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν hμν
  let h : Ω → ℝ := fun x => (μ.rnDeriv ξ x).toReal - C
  have hm : Measurable h := (Measure.measurable_rnDeriv μ ξ).ennreal_toReal.sub measurable_const
  have hrn : ∀ᵐ x ∂ξ, μ.rnDeriv ξ x ≤ ENNReal.ofReal (2*C) := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ξ) (fun s hs hsf => ?_)
    have h := (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ξ) s).trans (hμν s)
    simpa [ν, Measure.smul_apply, lintegral_const, mul_comm] using h
  have habs : ∀ᵐ x ∂ξ, |h x| ≤ C := by
    filter_upwards [hrn] with x hx
    have hx' : (μ.rnDeriv ξ x).toReal ≤ 2*C := by
      have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hx
      simpa [hC] using this
    have hx0 : 0 ≤ (μ.rnDeriv ξ x).toReal := ENNReal.toReal_nonneg
    dsimp [h]
    rw [abs_le]
    constructor <;> linarith
  refine ⟨h,hm,habs,?_⟩
  intro φ
  have hconst : Integrable (fun x : Ω => φ x * C) ξ := by
    let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    have hg : Integrable (fun x : Ω => φ x) ξ := by
      have he : (fun x : Ω => φ x) = g₀ := by funext x; rfl
      rw [he]
      exact g₀.continuous.integrable_of_hasCompactSupport g₀.hasCompactSupport
    exact hg.mul_const C
  have hr : Integrable (fun x : Ω => φ x * (μ.rnDeriv ξ x).toReal) ξ := by
    have hloc : LocallyIntegrable (fun x : Ω => (μ.rnDeriv ξ x).toReal) ξ := by
      rw [locallyIntegrable_iff]
      intro K hK
      exact Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top
    let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    have hg : Continuous (fun x : Ω => φ x) := φ.continuous.comp continuous_subtype_val
    have hc : HasCompactSupport (fun x : Ω => φ x) := by
      have he : (fun x : Ω => φ x) = g₀ := by funext x; rfl
      rw [he]
      exact g₀.hasCompactSupport
    simpa [smul_eq_mul, mul_comm] using hloc.integrable_smul_right_of_hasCompactSupport hg hc
  have hrep : (∫ x : Ω, φ x * (μ.rnDeriv ξ x).toReal ∂ξ) = ∫ x : Ω, φ x ∂μ := by
    rw [← integral_rnDeriv_smul hμξ]
    congr 1
    funext x
    rw [smul_eq_mul, mul_comm]
  rw [show (∫ x : Ω, φ x * h x ∂ξ) = (∫ x : Ω, φ x * (μ.rnDeriv ξ x).toReal ∂ξ) - ∫ x : Ω, φ x * C ∂ξ by
    simp_rw [h, mul_sub]; exact integral_sub hr hconst]
  rw [hrep, hμ φ]
  change T φ = (T φ + v φ) - _
  rw [hv]
  simp only [mul_comm _ C, integral_const_mul]
  ring
end SGPT.NPP.Codex.BoundedDistributionDensity
