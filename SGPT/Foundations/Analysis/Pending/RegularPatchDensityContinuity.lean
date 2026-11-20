import SGPT.Foundations.Analysis.Pending.RegularPatchTransition
import SGPT.Foundations.Analysis.FirstPass.StandardKahlerTopPower

set_option autoImplicit false

/-!
# Continuity and local finiteness of a patch parameter density

The parameter density of a smooth real `(1,1)`-form along a regular patch is
continuous on the parameter domain, so its integral over a compact parameter
ball inside that domain is finite.  Only continuity is used: the bound is by the
maximum of the density on the ball times the measure of the ball, with no
integrability or positivity input.

`Pending.RegularBranchKahlerJacobian` proves the same two facts higher up in the
import order, for the special case of a Kähler background; they are re-proved
here because the local Lelong bound of `Pending.SubvarietyBackgroundMass` sits
below that module.
-/

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RegularPatchTransition

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
  FirstPass.MongeAmpere

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The genuine top-power density is continuous in the coordinate two-form: the
pairing-sum formula makes it a polynomial in the values on the standard frame. -/
theorem continuous_topPowerDensity (k : ℕ) :
    Continuous (fun A : CoordinateRealTwoForm k => actualTopPowerDensity A) := by
  have hformula : (fun A : CoordinateRealTwoForm k => actualTopPowerDensity A) =
      fun A => ((2 : ℝ) ^ k)⁻¹ *
        coordinatePairingSum A
          (finProdFinEquiv : Fin k × Fin 2 → Fin (k * 2)) coordinateRealFrame := by
    funext A
    exact coordinateWedgePower_apply_eq_pairingSum A k coordinateRealFrame
  rw [hformula]
  unfold coordinatePairingSum
  fun_prop

/-- Pullback by a continuously varying real linear map preserves continuity of
the top-power density. -/
theorem continuousOn_topPowerDensity_comp {X : Type*} [TopologicalSpace X]
    {k : ℕ} {s : Set X} (A : X → CoordinateRealTwoForm n)
    (L : X → ComplexModel k →L[ℝ] ComplexModel n)
    (hA : ContinuousOn A s) (hL : ContinuousOn L s) :
    ContinuousOn (fun x =>
      actualTopPowerDensity ((A x).compContinuousLinearMap (L x))) s := by
  have hpull : ContinuousOn (fun x => (A x).compContinuousLinearMap (L x)) s := by
    change ContinuousOn (fun x =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (L x)) (A x)) s
    exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      hL).clm_apply hA
  exact (continuous_topPowerDensity k).comp_continuousOn hpull

/-- The parameter density of a smooth real two-form along a regular patch is
continuous on the parameter domain. -/
theorem continuousOn_actualTopPowerDensity_patchCoordinateForm
    (a : SmoothRealForm n M 2) (P : RegularPatch V) :
    ContinuousOn (fun w => actualTopPowerDensity (patchCoordinateForm a P w))
      P.parameterDomain := by
  have hparam : ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
    have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
      contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
        P.flattening.isOpen_target
    exact hinv.comp ((AdmissibleCurrentFormPositivity.planeInclusionCLM V.dim n).restrictScalars ℝ).contDiff.contDiffOn
      fun w hw => hw
  have hderiv : ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
    hparam.continuousOn_fderiv_of_isOpen
      (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P)
      (by simp)
  have hcoeff : ContinuousOn (fun w =>
      a.coeff (complexChartAt (n := n) P.center)
        (P.coordinateParametrization w)) P.parameterDomain := by
    refine (a.smooth _).continuousOn.comp hparam.continuousOn ?_
    intro w hw
    exact P.source_subset (P.flattening.mapsTo_invFun hw)
  exact continuousOn_topPowerDensity_comp _ _ hcoeff hderiv

/-- The parameter integral of the density over a compact parameter ball inside
the parameter domain is finite: bound the density by its maximum on the ball. -/
theorem lintegral_closedBall_actualTopPowerDensity_lt_top
    (a : SmoothRealForm n M 2) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
      ENNReal.ofReal (actualTopPowerDensity (patchCoordinateForm a P w)) < ⊤ := by
  set K := Metric.closedBall (0 : ComplexModel V.dim) r with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun w => actualTopPowerDensity (patchCoordinateForm a P w)) K :=
    (continuousOn_actualTopPowerDensity_patchCoordinateForm a P).mono hr
  rcases K.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  obtain ⟨w₀, _, hmax⟩ := hKc.exists_isMaxOn hne hcont
  set C := actualTopPowerDensity (patchCoordinateForm a P w₀) with hC
  calc ∫⁻ w in K, ENNReal.ofReal (actualTopPowerDensity (patchCoordinateForm a P w))
      ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hKc.measurableSet] with w hw
        exact ENNReal.ofReal_le_ofReal (hmax hw)
    _ = ENNReal.ofReal C * volume K := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top

end

end SGPT.Foundations.Analysis.Pending.RegularPatchTransition
