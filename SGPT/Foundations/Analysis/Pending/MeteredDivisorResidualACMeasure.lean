import SGPT.Foundations.Analysis.Pending.SingularPositiveCurrentACInvariance
import SGPT.Foundations.Analysis.Pending.ActualMeteredDivisorSingularReading
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.Pending.DivisorialDomination

set_option autoImplicit false

/-! Full mathematical statement and ENTIRE proof precede this import baseline.
The residual potential can be unbounded and nonanalytic. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.MeteredDivisorResidualACMeasure
open FirstPass FirstPass.HolomorphicIdealSheaves GlobalCurrents GlobalCurrentPotentials
  CanonicalCurrentFrame NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  LocalProductCurrents LocalCurrentLebesgue LocalCurrentDeterminant
  ActualAnalyticCurrentLocalDensity GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure PositiveCurrentACTopMeasure
  ActualCanonicalComplementaryCurrentCalibration ActualMeteredDivisorSingularReading
  SingularPositiveCurrentACInvariance DivisorialDomination LelongPoincareDivisor
  ActualDistributionTwoFormReading _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem regular_sum
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hv : IsGlobalQuasiPshPotential (n := m + 1) v)
    (hw : IsGlobalQuasiPshPotential (n := m + 1) (fun x => u x + v x))
    (e : ComplexChart (m + 1) M) :
    regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (fun x => u x + v x) e z).toReal)
      (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) _ hw e) =
      regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu e) +
      regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction v e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) v hv e) := by
  ext φ
  have hfu := quasiPsh_chart_ae_finite (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu e
  have hfv := quasiPsh_chart_ae_finite (canonicalBasis (m + 1)) (Nat.succ_pos m) v hv e
  have hiu : Integrable (fun z => φ z * (chartFunction u e z).toReal)
      (canonicalBasis (m + 1)).addHaar := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu e)
  have hiv : Integrable (fun z => φ z * (chartFunction v e z).toReal)
      (canonicalBasis (m + 1)).addHaar := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) v hv e)
  rw [_root_.add_apply, regularDistribution_apply,
    regularDistribution_apply, regularDistribution_apply]
  rw [← integral_add hiu hiv]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' e.val.open_target.measurableSet).mp hfu,
    (ae_restrict_iff' e.val.open_target.measurableSet).mp hfv] with z hzu hzv
  by_cases hz : z ∈ e.val.target
  · change φ z * (chartFunction u e z + chartFunction v e z).toReal = _
    rw [EReal.toReal_add (hzu hz).1 (hzu hz).2 (hzv hz).1 (hzv hz).2, mul_add]
  · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (φ.tsupport_subset h))
    rw [hφ]
    simp

private theorem weight_add_current
    (F : MeteredEffectiveQDivisor (m + 1) M) (hF : LocallyNondegenerate F.weight)
    (θ : ClosedRealOneOneForm (m + 1) M) {ℓ : M → EReal}
    (hℓ : IsThetaPshPotential (θ - F.curvature).val ℓ)
    (hw : IsThetaPshPotential θ.val (fun x => F.weight x + ℓ x)) :
    thetaPotentialCurrent θ.val (fun x => F.weight x + ℓ x) hw =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F +
        thetaPotentialCurrent (θ - F.curvature).val ℓ hℓ := by
  have hFq : IsGlobalQuasiPshPotential (n := m + 1) F.weight :=
    ⟨(MeteredDivisorPositivity.thetaPlurisubharmonic_weight F).quasiPlurisubharmonic, hF⟩
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  simp only [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    coefficients_smoothGlobalCurrent, globalDDC_coefficients,
    coefficients_integrationCurrent]
  unfold chartDDC
  rw [regular_sum hFq hℓ.quasiPshPotential hw.quasiPshPotential e, ← ddCLM_apply, map_add, ddCLM_apply, ddCLM_apply,
    smoothFormDistribution_sub (canonicalBasis (m + 1)) θ F.curvature e]
  abel

private theorem span_add
    (S R : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) :
    chartSpanCurrent (S + R) e = chartSpanCurrent S e + chartSpanCurrent R e := by
  ext γ φ
  rfl

private theorem acForm_congr {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (heq : S = R) : acForm hS = acForm hR := by
  subst R
  rfl

private theorem acTopMeasure_congr {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (heq : S = R) :
    acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The natural metered divisor and arbitrary genuine residual potential
internally produce the full original current sum, every SAME canonical RN
chart form and equality of entire global AC measures. -/
theorem exists_weight_add_current_ac_invariance
    (F : MeteredEffectiveQDivisor (m + 1) M) (hF : LocallyNondegenerate F.weight)
    (θ : ClosedRealOneOneForm (m + 1) M) {ℓ : M → EReal}
    (hℓ : IsThetaPshPotential (θ - F.curvature).val ℓ) :
    ∃ hw : IsThetaPshPotential θ.val (fun x => F.weight x + ℓ x),
      let S := thetaPotentialCurrent θ.val (fun x => F.weight x + ℓ x) hw
      let R := thetaPotentialCurrent (θ - F.curvature).val ℓ hℓ
      ∃ hS : IsFullPositive S, ∃ hR : IsFullPositive R,
        S = integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F + R ∧
        (∀ e : ComplexChart (m + 1) M,
          ∀ᵐ z ∂(volume : Measure (ComplexModel (m + 1))), z ∈ e.val.target →
            acForm (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent S hS e) z =
              acForm (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent R hR e) z) ∧
        globalACtopMeasure S hS = globalACtopMeasure R hR := by
  let hw := isThetaPshPotential_weight_add F hF hℓ
  let S := thetaPotentialCurrent θ.val (fun x => F.weight x + ℓ x) hw
  let R := thetaPotentialCurrent (θ - F.curvature).val ℓ hℓ
  let D := integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F
  let hS : IsFullPositive S := fun e α hα =>
    thetaPotentialCurrent_full_positive θ.val _ hw e α hα
  let hR : IsFullPositive R := fun e α hα =>
    thetaPotentialCurrent_full_positive (θ - F.curvature).val ℓ hℓ e α hα
  have heq : S = D + R := weight_add_current F hF θ hℓ hw
  have hlocal (e : ComplexChart (m + 1) M) :
      (∀ᵐ z ∂(volume : Measure (ComplexModel (m + 1))), z ∈ e.val.target →
        acForm (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent S hS e) z =
          acForm (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent R hR e) z) ∧
      acTopMeasure (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent S hS e) =
        acTopMeasure (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent R hR e) := by
    have hdiv : ∃ hD : IsPositive (chartSpanCurrent D e), hD.traceMeasure ⟂ₘ volume := by
      obtain ⟨hD, hDs, _, _⟩ :=
        exists_positive_singular_chart_reading (canonicalBasis (m + 1)) F e
      have h : ∃ h : IsPositive (complementaryRead
          ((integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F).coefficients
            (canonicalBasis (m + 1)) e)), h.traceMeasure ⟂ₘ volume := ⟨hD, hDs⟩
      simpa only [complementaryRead_coefficients_eq_chartSpanCurrent, D] using h
    obtain ⟨hD, hDs⟩ := hdiv
    let hRe := GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent R hR e
    let hSe := GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent S hS e
    have he : chartSpanCurrent S e = chartSpanCurrent D e + chartSpanCurrent R e := by
      rw [heq, span_add]
    have hform := acForm_congr hSe (hD.add hRe) he
    have hmeasure := acTopMeasure_congr hSe (hD.add hRe) he
    constructor
    · rw [hform]
      exact ae_acForm_add_singular hD hRe hDs
    · exact hmeasure.trans (acTopMeasure_add_singular_eq hD hRe hDs)
  refine ⟨hw, hS, hR, heq, fun e => (hlocal e).1, ?_⟩
  apply (globalACtopMeasure_unique S hS (globalACtopMeasure R hR) ?_).symm
  intro e
  rw [globalACtopMeasure_restrict_chart]
  unfold chartACMeasure
  rw [(hlocal e).2]

end SGPT.Foundations.Analysis.Pending.MeteredDivisorResidualACMeasure
