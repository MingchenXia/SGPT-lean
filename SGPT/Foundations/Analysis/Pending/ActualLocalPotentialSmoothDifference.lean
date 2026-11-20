import SGPT.Foundations.Analysis.Pending.ActualZeroLeviDistributionSmoothness
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false

/-! # The actual locally integrable difference of potentials is smooth

Complete full native `ddC` equality is the natural same-current hypothesis.
No smooth difference or almost-everywhere compatibility is supplied.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocalPotentialSmoothDifference
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Two actual local L1 potentials of the same complete native current have an
internally constructed smooth pluriharmonic difference, retaining all tests. -/
theorem exists_smooth_difference_of_equal_native_ddc
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {u v : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hv : LocallyIntegrableOn v Ω μ)
    (heq : ddC (regularDistribution μ u hu) = ddC (regularDistribution μ v hv))
    (x : E) (hx : x ∈ Ω) :
    ∃ (U : Opens E) (hU : U ≤ Ω) (h : E → ℝ),
      x ∈ U ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      ∃ hh : LocallyIntegrableOn h U μ,
        (fun z ↦ u z - v z) =ᵐ[μ.restrict U] h ∧
        restrictDistribution
          (regularDistribution μ u hu - regularDistribution μ v hv) hU =
          regularDistribution μ h hh ∧
        ∀ z ∈ U, ∀ w : E, leviForm h z w = 0 := by
  have hsubreg : regularDistribution μ (fun z ↦ u z - v z) (hu.sub hv) =
      regularDistribution μ u hu - regularDistribution μ v hv := by
    ext φ
    change _ = regularDistribution μ u hu φ - regularDistribution μ v hv φ
    simp only [regularDistribution_apply, mul_sub]
    exact integral_sub (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu)
      (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hv)
  have hddcsub : ddC (regularDistribution μ u hu - regularDistribution μ v hv) =
      ddC (regularDistribution μ u hu) - ddC (regularDistribution μ v hv) := by
    ext w : 1
    have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
    rw [hw, AlternatingMap.sub_apply, ddC_apply, ddC_apply, ddC_apply]
    ext φ
    simp only [map_sub, _root_.smul_apply, _root_.sub_apply, smul_eq_mul]
    ring
  have hddc : ddC (regularDistribution μ (fun z ↦ u z - v z) (hu.sub hv)) = 0 := by
    rw [hsubreg, hddcsub, heq, sub_self]
  have hzero : ∀ w : E,
      distributionalLeviCLM w (regularDistribution μ (fun z ↦ u z - v z) (hu.sub hv)) = 0 := by
    intro w
    have hline : (1 / Real.pi : ℝ) •
        distributionalLeviCLM w (regularDistribution μ (fun z ↦ u z - v z) (hu.sub hv)) = 0 := by
      rw [← ddC_complexLine, hddc]
      rfl
    exact (smul_eq_zero.mp hline).resolve_left (one_div_ne_zero Real.pi_ne_zero)
  obtain ⟨U, hU, h, hxU, hsm, hh, hcurrent, hlevi⟩ :=
    ActualZeroLeviDistributionSmoothness.exists_smooth_local_representative_of_zero_levi
      μ (regularDistribution μ (fun z ↦ u z - v z) (hu.sub hv)) hzero x hx
  have hregular : regularDistribution μ (fun z ↦ u z - v z)
      ((hu.sub hv).mono_set hU) = regularDistribution μ h hh := by
    simpa only [restrictDistribution_regularDistribution] using hcurrent
  have hnull : ∀ᵐ z ∂μ, z ∈ U → ((u z - v z) - h z) = 0 := by
    apply U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hu.sub hv).mono_set hU).sub hh)
    intro g hg hgc hgU
    let ψ : 𝓓(U, ℝ) := ⟨g, hg, hgc, hgU⟩
    have htest := congrArg (fun T : 𝓓'(U, ℝ) ↦ T ψ) hregular
    have hpair : (∫ z, g z * (u z - v z) ∂μ) = ∫ z, g z * h z ∂μ := by
      simpa only [regularDistribution_apply, ψ, TestFunction.coe_mk] using htest
    have hIq : Integrable (fun z ↦ g z * (u z - v z)) μ :=
      ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) ((hu.sub hv).mono_set hU)
    have hIh : Integrable (fun z ↦ g z * h z) μ :=
      ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hh
    change (∫ z, g z * ((u z - v z) - h z) ∂μ) = 0
    calc
      (∫ z, g z * ((u z - v z) - h z) ∂μ) =
          ∫ z, g z * (u z - v z) - g z * h z ∂μ :=
        integral_congr_ae (Eventually.of_forall fun z ↦ mul_sub (g z) (u z - v z) (h z))
      _ = (∫ z, g z * (u z - v z) ∂μ) - ∫ z, g z * h z ∂μ :=
        integral_sub hIq hIh
      _ = 0 := sub_eq_zero.mpr hpair
  refine ⟨U, hU, h, hxU, hsm, hh, ?_, ?_, hlevi⟩
  · apply (ae_restrict_iff' U.isOpen.measurableSet).mpr
    exact hnull.mono (fun z hz hzU ↦ sub_eq_zero.mp (hz hzU))
  · rw [← hsubreg]
    exact hcurrent

end SGPT.Foundations.Analysis.Pending.ActualLocalPotentialSmoothDifference
