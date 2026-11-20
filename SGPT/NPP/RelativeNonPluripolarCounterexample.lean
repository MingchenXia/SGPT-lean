import SGPT.NPP.RelativeNonPluripolarMass
import SGPT.NPP.NonPluripolarCurrent3Gauge
import SGPT.Foundations.Analysis.Pending.ActualOpenLogarithmicDivisorSingularity
import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: RelativePoleSupportedDraft
section OriginalFragment_01

/-! Actual relative products vanish when their base trace is carried by the
original potential's pole set. The current and all mass bounds are produced. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCalculus
open LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {n r : ℕ} {U : Opens (ComplexModel n)}

/-- The genuine actual relative differential of every truncation is zero
when the ORIGINAL base trace is carried by the ORIGINAL pole set. -/
theorem ddcMul_truncationReal_eq_zero_of_pole_carried
    (T : LocalProductCurrent n U (r + 1)) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u U) (hpole : ∀ᵐ x ∂hT.traceMeasure, u x = ⊥) (k : ℕ) :
    ddcMul T (truncationReal u k) = 0 := by
  have hv := truncationReal_isLocallyBoundedPshOn hu k
  have hc := isLocallyBoundedPshOn_const U (-(k : ℝ))
  have heq : mulBorel T ((U : Set (ComplexModel n)).indicator (truncationReal u k)) =
      mulBorel T ((U : Set (ComplexModel n)).indicator fun _ => -(k : ℝ)) := by
    ext γ φ
    rw [mulBorel_apply hT (measurable_indicator_of_isLocallyBoundedPshOn hv)
      (isLocallyBoundedOn_indicator hv),
      mulBorel_apply hT (measurable_indicator_of_isLocallyBoundedPshOn hc)
        (isLocallyBoundedOn_indicator hc)]
    apply integral_congr_ae
    filter_upwards [hpole] with x hx
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU,
        truncationReal_of_le k (by rw [hx]; exact bot_le)]
    · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]
  unfold ddcMul
  rw [heq]
  exact ddcMul_eq_zero_of_smoothDDC_eq_zero hT hTc contDiffOn_const
    (fun x _ => GlobalPotentialTransforms.smoothDDC_const (-(k : ℝ)) x)

/-- Actual finite relative mass is zero and hence finite; the hypothesis
concerns ONLY the original base trace and potential, not any output current. -/
theorem hasFiniteRelativeMass_of_pole_carried
    (T : LocalProductCurrent n U (r + 1)) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u U) (hpole : ∀ᵐ x ∂hT.traceMeasure, u x = ⊥) :
    HasFiniteRelativeMass T hT hTc (fun _ : Fin 1 => u) (fun _ => hu) := by
  apply hasFiniteRelativeMass_of_positive_extension T hT hTc
    (fun _ : Fin 1 => u) (fun _ => hu) isPositive_zero
  intro k
  change mulBorel (0 : LocalProductCurrent n U r) _ =
    mulBorel (ddcMul T (truncationReal u k)) _
  rw [ddcMul_truncationReal_eq_zero_of_pole_carried T hT hTc hu hpole k]

/-- The actual constructed current is zero, with its original finite mass
proved from original pole support, not supplied as a candidate certificate. -/
theorem relativeNonPluripolarProduct_eq_zero_of_pole_carried
    (T : LocalProductCurrent n U (r + 1)) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u U) (hpole : ∀ᵐ x ∂hT.traceMeasure, u x = ⊥) :
    (relativeNonPluripolarProduct T hT hTc (fun _ : Fin 1 => u) (fun _ => hu)
      (hasFiniteRelativeMass_of_pole_carried T hT hTc hu hpole)).val = 0 := by
  apply (eq_relativeNonPluripolarProduct_of_mulBorel T hT hTc
    (fun _ : Fin 1 => u) (fun _ => hu)
    (hasFiniteRelativeMass_of_pole_carried T hT hTc hu hpole)
    isPositive_zero ?_ (mulBorel_zero_current _)).symm
  intro k
  change mulBorel (0 : LocalProductCurrent n U r) _ =
    mulBorel (ddcMul T (truncationReal u k)) _
  rw [ddcMul_truncationReal_eq_zero_of_pole_carried T hT hTc hu hpole k]

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.ddcMul_truncationReal_eq_zero_of_pole_carried
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_pole_carried
#check @SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct_eq_zero_of_pole_carried
#print axioms SGPT.NPP.RelativeNonPluripolar.ddcMul_truncationReal_eq_zero_of_pole_carried
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_pole_carried
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct_eq_zero_of_pole_carried

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: CoordinateDivisorCurrentDraft
section OriginalFragment_02

/-! The actual coordinate divisor of a ball in C^2, as the SAME native
LocalProductCurrent used by the relative products. No divisor/current
identification, positivity or nonzero coefficient is supplied as input. -/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCalculus
open LocalBedfordTaylorLocality LocalCurrentL1Ddc LocalCurrentPullbackDdc
open SGPT.NPP.NonPluripolarCurrent

/-- The genuine coordinate ball on which the current-valued witness lives. -/
def coordinateBall : Opens (ComplexModel 2) := ⟨ball 0 1, isOpen_ball⟩

private def coordinateProjectionLinear : ComplexModel 2 →ₗ[ℂ] ℂ where
  toFun z := z 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual first holomorphic coordinate, with its genuine linear topology. -/
def coordinateProjection : ComplexModel 2 →L[ℂ] ℂ :=
  coordinateProjectionLinear.toContinuousLinearMap

/-- The genuine squared logarithmic coordinate pole. -/
def coordinateLog : ComplexModel 2 → EReal :=
  generatorLog (fun _ : Fin 1 => coordinateProjection)

theorem coordinateProjection_nonzero_germ :
    ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel 2), coordinateProjection x = 0 := by
  intro hz
  have hevent : (fun x : ComplexModel 2 => coordinateProjection x) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := hz
  have hd0 : HasFDerivAt coordinateProjection (0 : ComplexModel 2 →L[ℂ] ℂ) 0 :=
    (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) (0 : ComplexModel 2)).congr_of_eventuallyEq hevent
  have heq : coordinateProjection = 0 := coordinateProjection.hasFDerivAt.unique hd0
  have h := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ =>
    L (EuclideanSpace.single (0 : Fin 2) 1)) heq
  change (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) 0 = (0 : ℂ) at h
  simp at h

theorem coordinateProjection_frequently_ne_zero :
    ∀ x ∈ coordinateBall, ∃ᶠ y in 𝓝 x, coordinateProjection y ≠ 0 := by
  obtain ⟨_, _, hd0, _⟩ :=
    ActualLogarithmicDivisorCurrent.single_logarithmic_ddC_eq_divisorCurrent
      coordinateProjection (by norm_num : 0 < (1 : ℝ))
      coordinateProjection.differentiable.differentiableOn
      coordinateProjection_nonzero_germ (by norm_num : 0 < (1 : ℝ))
  exact hd0

theorem coordinateLog_psh : PlurisubharmonicOn coordinateLog coordinateBall := by
  intro x hx
  simpa only [EReal.coe_one, one_mul, coordinateLog] using
    (plurisubharmonicAt_scaled_generatorLog
      ⟨coordinateBall, coordinateBall.isOpen, hx,
        fun _ => coordinateProjection.differentiable.differentiableOn⟩
      (by norm_num : 0 < (1 : ℝ)))

theorem coordinateLog_isL1Psh : IsL1PshOn coordinateBall coordinateLog := by
  refine ⟨coordinateLog_psh, fun x hx => ?_⟩
  exact (coordinateProjection_frequently_ne_zero x hx).mono fun y hy => by
    rw [coordinateLog, generatorLog_of_nonzero
      (f := fun _ : Fin 1 => coordinateProjection) ⟨0, hy⟩]
    exact EReal.coe_ne_bot _

theorem coordinateLog_pole_iff (x : ComplexModel 2) :
    coordinateLog x = ⊥ ↔ coordinateProjection x = 0 := by
  simp [coordinateLog]

theorem coordinateLog_origin_pole : coordinateLog 0 = ⊥ :=
  (coordinateLog_pole_iff 0).mpr (map_zero coordinateProjection)

/-- The actual closed positive integration current of the coordinate divisor. -/
def coordinateDivisorCurrent : LocalProductCurrent 2 coordinateBall 1 :=
  ddcL1 coordinateBall coordinateLog

theorem isPositive_coordinateDivisorCurrent : IsPositive coordinateDivisorCurrent :=
  coordinateLog_isL1Psh.isPositive_ddcL1

theorem isClosed_coordinateDivisorCurrent : IsClosedCurrent coordinateDivisorCurrent :=
  isClosedAny_ddcL1 coordinateLog

/-- The genuine full local integration current and every complementary
coefficient agree with the SAME native relative-product base current. -/
theorem coordinateDivisorCurrent_eq_actual_integration_current :
    coordinateDivisorCurrent = ActualDistributionTwoFormReading.complementaryRead
      (DivisorIntegrationCurrent.divisorCurrent
        coordinateProjection.differentiable.differentiableOn
        coordinateProjection_frequently_ne_zero) := by
  have hlog := DivisorIntegrationCurrent.locallyIntegrableOn_log_normSq
    coordinateBall.isOpen coordinateProjection.differentiable.differentiableOn
    coordinateProjection_frequently_ne_zero
  have heq := (ActualOpenLogarithmicDivisorSingularity.exists_positive_singular_divisor_reading
    coordinateProjection.differentiable.differentiableOn
    coordinateProjection_frequently_ne_zero).1
  change ddc (l1Current coordinateBall coordinateLog) = _
  rw [SGPT.Currents.l1Current_eq_scalarTopCurrent coordinateLog_isL1Psh.locallyIntegrableOn,
    heq]
  apply congrArg ddc
  apply congrArg ScalarLeviPositiveCurrent.scalarTopCurrent
  apply regularDistribution_congr_ae_on coordinateLog_isL1Psh.locallyIntegrableOn hlog
  exact Eventually.of_forall fun x => by
    change (coordinateLog x).toReal = Real.log (‖coordinateProjection x‖ ^ 2)
    by_cases hz : coordinateProjection x = 0
    · rw [(coordinateLog_pole_iff x).mpr hz]
      simp [hz]
    · rw [coordinateLog, generatorLog_of_nonzero
        (f := fun _ : Fin 1 => coordinateProjection) ⟨0, hz⟩, EReal.toReal_coe]
      simp only [generatorNormSq, Fintype.sum_unique]

/-- The actual integration current is nonzero: zero current would make
the genuine logarithmic pole pluriharmonic and hence finite at the origin. -/
theorem coordinateDivisorCurrent_ne_zero : coordinateDivisorCurrent ≠ 0 := by
  intro hz
  have h0 : IsL1PshOn coordinateBall (fun _ => (0 : EReal)) := {
    psh := (isLocallyBoundedPshOn_const coordinateBall (0 : ℝ)).1
    frequently_ne_bot := fun _ _ =>
      (Eventually.of_forall fun _ => EReal.coe_ne_bot (0 : ℝ)).frequently }
  have hd0 : ddcL1 coordinateBall (fun _ => (0 : EReal)) = 0 := by
    change ddcL1 coordinateBall (fun _ => ((0 : ℝ) : EReal)) = 0
    rw [ddcL1_coe_eq_ddcMul (isLocallyBoundedPshOn_const coordinateBall (0 : ℝ))]
    exact ddcMul_eq_zero_of_smoothDDC_eq_zero (n := 2) (m := 1)
      (S := oneCurrent coordinateBall) isPositive_oneCurrent
      (isClosedAny_oneCurrent (n := 2) (U := coordinateBall)) contDiffOn_const
      (fun x _ => GlobalPotentialTransforms.smoothDDC_const (0 : ℝ) x)
  obtain ⟨g, _, _, h⟩ := SGPT.Currents.exists_pluriharmonic_of_ddcL1_eq
    coordinateLog_isL1Psh h0 (hz.trans hd0.symm)
  have hzero := h 0 (mem_ball_self (by norm_num : 0 < (1 : ℝ)))
  rw [coordinateLog_origin_pole] at hzero
  simp at hzero

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_eq_actual_integration_current
#check @SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_ne_zero
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateProjection_nonzero_germ
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateProjection_frequently_ne_zero
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateLog_psh
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateLog_isL1Psh
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateLog_pole_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateLog_origin_pole
#print axioms SGPT.NPP.RelativeNonPluripolar.isPositive_coordinateDivisorCurrent
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_coordinateDivisorCurrent
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_eq_actual_integration_current
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_ne_zero

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: CoordinateDivisorSupportDraft
section OriginalFragment_03

/-! The actual geometric coordinate-divisor density forces the ORIGINAL
native base trace to be carried by the ORIGINAL logarithmic pole set. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCollar
open ActualDistributionTwoFormReading DivisorIntegrationCurrent DivisorRegularLocus

/-- Support of the actual integration-density coefficient measures, with
no supplied support, singularity, output-current or trace certificate. -/
theorem coordinateDivisorCurrent_trace_carried_by_poles :
    ∀ᵐ x ∂isPositive_coordinateDivisorCurrent.traceMeasure, coordinateLog x = ⊥ := by
  let hT := isPositive_coordinateDivisorCurrent
  have hWo : IsOpen {x : ComplexModel 2 | coordinateProjection x ≠ 0} :=
    (isClosed_eq coordinateProjection.continuous continuous_const).isOpen_compl
  let W : Opens (ComplexModel 2) :=
    ⟨(coordinateBall : Set (ComplexModel 2)) ∩ {x | coordinateProjection x ≠ 0},
      coordinateBall.isOpen.inter hWo⟩
  have hWU : W ≤ coordinateBall := inter_subset_left
  let D := divisorCurrent coordinateProjection.differentiable.differentiableOn
    coordinateProjection_frequently_ne_zero
  have hDzero : LelongPoincareDivisor.restrictForm D hWU = 0 := by
    ext v φ
    change D v (extTest hWU φ) = 0
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    change divisorCurrent coordinateProjection.differentiable.differentiableOn
      coordinateProjection_frequently_ne_zero ![v 0, v 1] (extTest hWU φ) = 0
    rw [divisorCurrent_apply]
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      change (extTest hWU φ) x * divisorDensity coordinateProjection (v 0) (v 1) x = 0
      by_cases hxW : x ∈ W
      · have hn : x ∉ regularLocus coordinateProjection :=
          fun hx => hxW.2 (eq_zero_of_mem_regularLocus hx)
        rw [divisorDensity, Set.indicator_of_notMem hn, mul_zero]
      · rw [extTest_apply, testFunction_eq_zero_of_notMem φ hxW, zero_mul]
  have hreader : restrict hWU (complementaryRead D) =
      complementaryRead (LelongPoincareDivisor.restrictForm D hWU) := by
    ext γ φ
    simp only [complementaryRead, LocalBedfordTaylorLocality.restrict_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
      LelongPoincareDivisor.restrictForm_apply, extTest]
  have hWzero : restrict hWU coordinateDivisorCurrent = 0 := by
    rw [coordinateDivisorCurrent_eq_actual_integration_current]
    change restrict hWU (complementaryRead D) = 0
    rw [hreader, hDzero]
    ext γ φ
    simp [complementaryRead]
  let hTW := isPositive_restrict hT hWU
  have htraceW : hTW.traceMeasure = 0 := by
    apply eq_of_forall_testFunction_integral_eq hTW.traceMeasure_compl (by simp)
      (fun K hK hKW => hTW.traceMeasure_lt_top hK hKW) (by intros; simp)
    intro φ
    rw [hTW.integral_traceMeasure, hWzero]
    simp
  have hWmass : hT.traceMeasure W = 0 := by
    have h := congrArg (fun μ : Measure (ComplexModel 2) => μ univ) htraceW
    rw [traceMeasure_restrict hT hWU, Measure.restrict_apply' W.isOpen.measurableSet,
      univ_inter] at h
    simpa using h
  filter_upwards [LocalBedfordTaylorDecreasing.ae_mem_of_compl_eq_zero hT.traceMeasure_compl,
    measure_eq_zero_iff_ae_notMem.mp hWmass] with x hxU hxW
  exact (coordinateLog_pole_iff x).mpr (by
    by_contra hn
    exact hxW ⟨hxU, hn⟩)

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_trace_carried_by_poles
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateDivisorCurrent_trace_carried_by_poles

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativeSmoothNonzeroDraft
section OriginalFragment_04

/-! Actual scalar tests distinguish the genuine relative product with the
smooth squared-norm potential from zero. The exact native trace normalization
and original nonzero coordinate integration current are used internally. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
open LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalBedfordTaylorDecreasing
open SGPT.NPP.NonPluripolarCurrent

/-- Every nonzero positive closed bidimension-one current has an actual
nonzero scalar coefficient test after wedging with the squared-norm Hessian. -/
theorem exists_test_ddcMul_ballPot_nonzero {n : ℕ} {U : Opens (ComplexModel n)}
    (T : LocalProductCurrent n U 1) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) (hTne : T ≠ 0) :
    ∃ φ : 𝓓(U, ℝ),
      ddcMul T (ballPot 1 (0 : ComplexModel n) 0) (kahlerPower n 0) φ ≠ 0 := by
  let hs : ContDiffOn ℝ ∞ (ballPot 1 (0 : ComplexModel n) 0) U :=
    (contDiff_ballPot 1 (0 : ComplexModel n) 0).contDiffOn
  let hlev : ∀ x ∈ U, ∀ v, 0 ≤ leviForm (ballPot 1 (0 : ComplexModel n) 0) x v :=
    leviForm_ballPot_nonneg (by norm_num : 0 ≤ (1 : ℝ)) (0 : ComplexModel n) 0
  let hR := isPositive_ddcWedge hT hs hlev
  have hmass := traceMeasure_ddcWedge_ballPot (m := 0) hT (by norm_num : 0 ≤ (1 : ℝ))
    (0 : ComplexModel n) 0
  by_contra hn
  push Not at hn
  have hR0 : hR.traceMeasure = 0 := by
    apply eq_of_forall_testFunction_integral_eq hR.traceMeasure_compl (by simp)
      (fun K hK hKU => hR.traceMeasure_lt_top hK hKU) (by intros; simp)
    intro φ
    rw [hR.integral_traceMeasure, ← ddcMul_eq_ddcWedge hT hTc hs]
    simpa only [integral_zero_measure] using hn φ
  have hc : ENNReal.ofReal (1 / Real.pi) ≠ 0 := by positivity
  have hscale : ENNReal.ofReal (1 / Real.pi) • hT.traceMeasure = 0 := hmass.symm.trans hR0
  have hT0 : hT.traceMeasure = 0 := by
    ext A hA
    have h := congrArg (fun μ : Measure (ComplexModel n) => μ A) hscale
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  apply hTne
  ext γ φ
  rw [hT.apply_eq_integral_density, hT0]
  simp

/-- The actual smooth potential in the original coordinate-current example. -/
def coordinateSmoothPotential : ComplexModel 2 → ℝ := ballPot 1 0 0

theorem coordinateSmoothPotential_eq_norm_sq :
    coordinateSmoothPotential = fun x : ComplexModel 2 => ‖x‖ ^ 2 := by
  funext x
  simp [coordinateSmoothPotential, ballPot]

theorem coordinateSmoothPotential_locallyBoundedPsh :
    IsLocallyBoundedPshOn coordinateBall coordinateSmoothPotential :=
  isLocallyBoundedPshOn_ballPot (by norm_num : 0 ≤ (1 : ℝ)) 0 0

/-- An actual original compact coefficient test distinguishes the genuine
relative NPP from zero. Its finite mass and its base T nonvanishing are
manufactured internally; no nonzero-output/test premise is supplied. -/
theorem exists_coordinate_smooth_relative_nonzero_test :
    ∃ φ : 𝓓(coordinateBall, ℝ),
      (relativeNonPluripolarProduct (p := 1) (r := 0)
        coordinateDivisorCurrent isPositive_coordinateDivisorCurrent
        isClosed_coordinateDivisorCurrent
        (fun _ : Fin 1 => fun x => (coordinateSmoothPotential x : EReal))
        (fun _ => coordinateSmoothPotential_locallyBoundedPsh.1)
        (hasFiniteRelativeMass_of_isLocallyBoundedPshOn (p := 1) (r := 0)
          coordinateDivisorCurrent
          isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
          (fun _ : Fin 1 => coordinateSmoothPotential)
          (fun _ => coordinateSmoothPotential_locallyBoundedPsh))).val
        (kahlerPower 2 0) φ ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_test_ddcMul_ballPot_nonzero coordinateDivisorCurrent
    isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    coordinateDivisorCurrent_ne_zero
  refine ⟨φ, fun hz => hφ ?_⟩
  have heq := relativeNonPluripolarProduct_of_isLocallyBoundedPshOn (p := 1) (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    (fun _ : Fin 1 => coordinateSmoothPotential)
    (fun _ => coordinateSmoothPotential_locallyBoundedPsh)
  have hval := congrArg (fun S : LocalProductCurrent 2 coordinateBall 0 =>
    S (kahlerPower 2 0) φ) heq
  exact hval.symm.trans hz

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.exists_test_ddcMul_ballPot_nonzero
#check @SGPT.NPP.RelativeNonPluripolar.exists_coordinate_smooth_relative_nonzero_test
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_test_ddcMul_ballPot_nonzero
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSmoothPotential
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSmoothPotential_eq_norm_sq
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSmoothPotential_locallyBoundedPsh
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_coordinate_smooth_relative_nonzero_test

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04

-- Exact frozen body: RelativeActualNonlinearityDraft
section OriginalFragment_05

/-! An actual current-valued failure of additivity for relative NPP.
The original coordinate divisor, smooth current, all three finite-mass
products and an actual nonzero compact coefficient test are produced.
No current/test/nonlinearity output certificate is a premise. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorDecreasing LocalCurrentL1Ddc ScalarLeviPositiveCurrent
open SGPT.NPP.NonPluripolarCurrent

def coordinateSumPotential : ComplexModel 2 → EReal :=
  fun x => coordinateLog x + (coordinateSmoothPotential x : EReal)

theorem coordinateSumPotential_psh :
    PlurisubharmonicOn coordinateSumPotential coordinateBall :=
  coordinateLog_psh.add coordinateSmoothPotential_locallyBoundedPsh.1

theorem coordinateSmoothPotential_isL1Psh :
    IsL1PshOn coordinateBall (fun x => (coordinateSmoothPotential x : EReal)) := {
  psh := coordinateSmoothPotential_locallyBoundedPsh.1
  frequently_ne_bot := fun _ _ =>
    (Eventually.of_forall fun x => EReal.coe_ne_bot (coordinateSmoothPotential x)).frequently }

theorem coordinateSumPotential_isL1Psh :
    IsL1PshOn coordinateBall coordinateSumPotential := by
  refine ⟨coordinateSumPotential_psh, fun x hx => ?_⟩
  exact (coordinateLog_isL1Psh.frequently_ne_bot x hx).mono fun y hy => by
    have heq : coordinateLog y = ((coordinateLog y).toReal : EReal) :=
      (EReal.coe_toReal (generatorLog_ne_top (fun _ : Fin 1 => coordinateProjection) y) hy).symm
    change coordinateLog y + (coordinateSmoothPotential y : EReal) ≠ ⊥
    rw [heq, ← EReal.coe_add]
    exact EReal.coe_ne_bot _

def coordinateSmoothCurrent : LocalProductCurrent 2 coordinateBall 1 :=
  ddcL1 coordinateBall (fun x => (coordinateSmoothPotential x : EReal))

theorem isPositive_coordinateSmoothCurrent : IsPositive coordinateSmoothCurrent :=
  coordinateSmoothPotential_isL1Psh.isPositive_ddcL1

theorem isClosed_coordinateSmoothCurrent : IsClosedCurrent coordinateSmoothCurrent :=
  isClosedAny_ddcL1 (fun x => (coordinateSmoothPotential x : EReal))

/-- The SAME original current factors satisfy genuine distributional
additivity; nonadditivity below is of the relative product, not a proxy. -/
theorem coordinate_source_current_add :
    ddcL1 coordinateBall coordinateSumPotential =
      coordinateDivisorCurrent + coordinateSmoothCurrent := by
  let hu := coordinateLog_isL1Psh.locallyIntegrableOn
  let hv := coordinateSmoothPotential_isL1Psh.locallyIntegrableOn
  let hs := coordinateSumPotential_isL1Psh.locallyIntegrableOn
  have hdist : regularDistribution volume (fun x => (coordinateSumPotential x).toReal) hs =
      regularDistribution volume (fun x => (coordinateLog x).toReal) hu +
        regularDistribution volume (fun x => ((coordinateSmoothPotential x : EReal)).toReal) hv := by
    calc
      _ = regularDistribution volume
          (fun x => (coordinateLog x).toReal + ((coordinateSmoothPotential x : EReal)).toReal)
          (hu.add hv) := by
        apply regularDistribution_congr_ae_on hs (hu.add hv)
        filter_upwards [coordinateLog_isL1Psh.ae_ne_bot] with x hx
        have heq : coordinateLog x = ((coordinateLog x).toReal : EReal) :=
          (EReal.coe_toReal (generatorLog_ne_top (fun _ : Fin 1 => coordinateProjection) x) hx).symm
        change (coordinateLog x + (coordinateSmoothPotential x : EReal)).toReal =
          (coordinateLog x).toReal + ((coordinateSmoothPotential x : EReal)).toReal
        conv_lhs => rw [heq, ← EReal.coe_add, EReal.toReal_coe]
        rw [EReal.toReal_coe]
      _ = _ := by
        ext φ
        rw [regularDistribution_apply, _root_.add_apply,
          regularDistribution_apply, regularDistribution_apply]
        rw [← integral_add (integrable_testFunction_mul hu φ) (integrable_testFunction_mul hv φ)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_add _ _ _
  have hl1 : l1Current coordinateBall coordinateSumPotential =
      l1Current coordinateBall coordinateLog +
        l1Current coordinateBall (fun x => (coordinateSmoothPotential x : EReal)) := by
    rw [SGPT.Currents.l1Current_eq_scalarTopCurrent hs,
      SGPT.Currents.l1Current_eq_scalarTopCurrent hu,
      SGPT.Currents.l1Current_eq_scalarTopCurrent hv, hdist]
    ext γ φ
    simp only [scalarTopCurrent_apply, LinearMap.add_apply, _root_.add_apply, mul_add]
  change ddc (l1Current coordinateBall coordinateSumPotential) =
    ddc (l1Current coordinateBall coordinateLog) +
      ddc (l1Current coordinateBall (fun x => (coordinateSmoothPotential x : EReal)))
  rw [hl1, ddc_add]

theorem coordinateSum_trace_carried_by_poles :
    ∀ᵐ x ∂isPositive_coordinateDivisorCurrent.traceMeasure, coordinateSumPotential x = ⊥ := by
  filter_upwards [coordinateDivisorCurrent_trace_carried_by_poles] with x hx
  change coordinateLog x + (coordinateSmoothPotential x : EReal) = ⊥
  simp [hx]

theorem coordinateLog_relative_mass :
    HasFiniteRelativeMass (p := 1) (r := 0)
      coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => coordinateLog) (fun _ => coordinateLog_psh) :=
  hasFiniteRelativeMass_of_pole_carried (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    coordinateLog_psh coordinateDivisorCurrent_trace_carried_by_poles

theorem coordinateSum_relative_mass :
    HasFiniteRelativeMass (p := 1) (r := 0)
      coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => coordinateSumPotential) (fun _ => coordinateSumPotential_psh) :=
  hasFiniteRelativeMass_of_pole_carried (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    coordinateSumPotential_psh coordinateSum_trace_carried_by_poles

def coordinateRelativeLogCurrent : LocalProductCurrent 2 coordinateBall 0 :=
  (relativeNonPluripolarProduct (p := 1) (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    (fun _ : Fin 1 => coordinateLog) (fun _ => coordinateLog_psh) coordinateLog_relative_mass).val

def coordinateRelativeSumCurrent : LocalProductCurrent 2 coordinateBall 0 :=
  (relativeNonPluripolarProduct (p := 1) (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    (fun _ : Fin 1 => coordinateSumPotential) (fun _ => coordinateSumPotential_psh)
    coordinateSum_relative_mass).val

def coordinateRelativeSmoothCurrent : LocalProductCurrent 2 coordinateBall 0 :=
  (relativeNonPluripolarProduct (p := 1) (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    (fun _ : Fin 1 => fun x => (coordinateSmoothPotential x : EReal))
    (fun _ => coordinateSmoothPotential_locallyBoundedPsh.1)
    (hasFiniteRelativeMass_of_isLocallyBoundedPshOn (p := 1) (r := 0)
      coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => coordinateSmoothPotential)
      (fun _ => coordinateSmoothPotential_locallyBoundedPsh))).val

theorem coordinateRelativeLogCurrent_eq_zero : coordinateRelativeLogCurrent = 0 :=
  relativeNonPluripolarProduct_eq_zero_of_pole_carried (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    coordinateLog_psh coordinateDivisorCurrent_trace_carried_by_poles

theorem coordinateRelativeSumCurrent_eq_zero : coordinateRelativeSumCurrent = 0 :=
  relativeNonPluripolarProduct_eq_zero_of_pole_carried (r := 0)
    coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
    coordinateSumPotential_psh coordinateSum_trace_carried_by_poles

/-- A genuine pair of positive closed original current factors, their SAME
distributional sum, and an ACTUAL compact test witnessing nonadditivity.
All three relative mass conditions and the nonzero output are manufactured. -/
theorem coordinate_actual_relative_nonadditivity :
    IsPositive coordinateDivisorCurrent ∧ IsClosedCurrent coordinateDivisorCurrent ∧
      IsPositive coordinateSmoothCurrent ∧ IsClosedCurrent coordinateSmoothCurrent ∧
      ddcL1 coordinateBall coordinateSumPotential =
        coordinateDivisorCurrent + coordinateSmoothCurrent ∧
      ∃ φ : 𝓓(coordinateBall, ℝ),
        coordinateRelativeSumCurrent (kahlerPower 2 0) φ ≠
          coordinateRelativeLogCurrent (kahlerPower 2 0) φ +
            coordinateRelativeSmoothCurrent (kahlerPower 2 0) φ := by
  refine ⟨isPositive_coordinateDivisorCurrent, isClosed_coordinateDivisorCurrent,
    isPositive_coordinateSmoothCurrent, isClosed_coordinateSmoothCurrent,
    coordinate_source_current_add, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_coordinate_smooth_relative_nonzero_test
  refine ⟨φ, ?_⟩
  have hlog := congrArg (fun S : LocalProductCurrent 2 coordinateBall 0 => S (kahlerPower 2 0) φ)
    coordinateRelativeLogCurrent_eq_zero
  have hsum := congrArg (fun S : LocalProductCurrent 2 coordinateBall 0 => S (kahlerPower 2 0) φ)
    coordinateRelativeSumCurrent_eq_zero
  simp only [LinearMap.zero_apply, _root_.zero_apply] at hlog hsum
  intro h
  apply hφ
  change coordinateRelativeSmoothCurrent (kahlerPower 2 0) φ = 0
  linarith

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.coordinate_source_current_add
#check @SGPT.NPP.RelativeNonPluripolar.coordinate_actual_relative_nonadditivity
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSumPotential_isL1Psh
#print axioms SGPT.NPP.RelativeNonPluripolar.isPositive_coordinateSmoothCurrent
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_coordinateSmoothCurrent
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinate_source_current_add
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateLog_relative_mass
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSum_relative_mass
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateRelativeLogCurrent_eq_zero
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateRelativeSumCurrent_eq_zero
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinate_actual_relative_nonadditivity

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_05
