import SGPT.Okounkov.GlobalDivisorResidual
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open LelongPoincareDivisor ThetaPshCodimTwoExtension
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual original divisor nullity and original potential finiteness give
the genuine real representative identity in every ORIGINAL chart. -/
theorem smooth_divisor_residual_chart_ae_toReal
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W) (c : ℝ)
    (e : ComplexChart (m + 1) M) :
    (fun z => (chartFunction (extensionAcross W (smoothDivisorOffResidual E c u)) e z).toReal)
      =ᵐ[(canonicalBasis (m + 1)).addHaar.restrict (chartTarget e)]
        (fun z => (chartFunction u e z).toReal - c * (chartFunction E.weight e z).toReal) := by
  have hWa : IsComplexAnalyticSubset (n := m + 1) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hW.1, fun x hx => ⟨m, hW.2.2 x hx⟩⟩
  have hnull := (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    hWa (smooth_divisor_interior_eq_empty hW)).chart_measure_eq_zero e
      (canonicalBasis (m + 1)).addHaar
  have hoffae : ∀ᵐ z ∂(canonicalBasis (m + 1)).addHaar.restrict (chartTarget e),
      e.val.symm z ∉ W := by
    change ∀ᵐ z ∂(canonicalBasis (m + 1)).addHaar.restrict e.val.target,
      e.val.symm z ∉ W
    rw [ae_restrict_iff' e.val.open_target.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzt hw
    exact hz ⟨hzt, hw⟩
  have hoff : ThetaPshOff (θ - c • E.curvature).val W (smoothDivisorOffResidual E c u) := by
    simpa only [hEW] using thetaPshOff_smoothDivisorOffResidual hu E c
  filter_upwards [hoffae, quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
    (Nat.succ_pos m) u hu.quasiPshPotential e] with z hzW hzu
  have hzE : e.val.symm z ∉ E.support := by rw [hEW]; exact hzW
  obtain ⟨F, _hF, hFeq⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hzE
  have hweight : E.weight (e.val.symm z) = (F (e.val.symm z) : EReal) :=
    Filter.EventuallyEq.eq_of_nhds
      (show E.weight =ᶠ[𝓝 (e.val.symm z)] (fun y => (F y : EReal)) from hFeq)
  simp only [chartFunction, extensionAcross_eq_of_notMem hW.1 hoff hzW,
    smoothDivisorOffResidual, if_neg hzE, hweight, ← EReal.coe_mul]
  change u (e.val.symm z) ≠ ⊤ ∧ u (e.val.symm z) ≠ ⊥ at hzu
  rw [EReal.toReal_sub hzu.1 hzu.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
    EReal.toReal_coe, EReal.toReal_coe]

private theorem smoothFormDistribution_smul_closed
    (c : ℝ) (σ : ClosedRealOneOneForm (m + 1) M) (e : ComplexChart (m + 1) M) :
    smoothFormDistribution (canonicalBasis (m + 1)) (c • σ).val e =
      c • smoothFormDistribution (canonicalBasis (m + 1)) σ.val e := by
  ext w φ
  rw [smoothFormDistribution_apply, AlternatingMap.smul_apply, smul_apply,
    smoothFormDistribution_apply]
  have hfun : (fun x => φ x • (c • σ).val.coeff e x) =
      fun x => c • (φ x • σ.val.coeff e x) := by
    funext x
    rw [ClosedRealOneOneForm.coeff_smul]
    exact smul_comm _ _ _
  rw [hfun, integral_smul]
  rfl

/-- Actual chart Haar-nullity and genuine L1 densities give the WHOLE current
identity, including all divisor-supported distribution coefficients. -/
theorem smooth_divisor_residual_current_eq
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W) (c : ℝ)
    (hv : IsThetaPshPotential (θ - c • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u))) :
    thetaPotentialCurrent (θ - c • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
        thetaPotentialCurrent θ.val u hu -
          c • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E := by
  let b := canonicalBasis (m + 1)
  let v := extensionAcross W (smoothDivisorOffResidual E c u)
  have hchart (e : ComplexChart (m + 1) M) :
      chartDDC b v e (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) v hv.quasiPshPotential e) =
        chartDDC b u e (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e) -
          c • chartDDC b E.weight e (chartLocallyIntegrable_weight b E e) := by
    have hLu := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
    have hLE := chartLocallyIntegrable_weight b E e
    have hLv := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) v hv.quasiPshPotential e
    have hneg : LocallyIntegrableOn
        (fun z => (-c) * (chartFunction E.weight e z).toReal) (chartTarget e) b.addHaar :=
      hLE.smul (-c)
    have hsum : LocallyIntegrableOn
        (fun z => (chartFunction u e z).toReal + (-c) * (chartFunction E.weight e z).toReal)
        (chartTarget e) b.addHaar := hLu.add hneg
    have hreal : (fun z => (chartFunction v e z).toReal) =ᵐ[b.addHaar.restrict (chartTarget e)]
        (fun z => (chartFunction u e z).toReal + (-c) * (chartFunction E.weight e z).toReal) := by
      simpa only [neg_mul, sub_eq_add_neg] using
        smooth_divisor_residual_chart_ae_toReal hu hW E hEW c e
    unfold chartDDC
    rw [regularDistribution_congr_ae_on hLv hsum hreal]
    change ddC (regularDistribution b.addHaar
      (fun z => (chartFunction u e z).toReal + (-c) * (chartFunction E.weight e z).toReal) hsum) = _
    rw [regularDistribution_add' hLu hneg hsum,
      regularDistribution_const_mul (-c) hLE hneg,
      ← ddCLM_apply, map_add, map_smul]
    simp only [ddCLM_apply, neg_smul, sub_eq_add_neg]
  apply globalCurrent_ext b
  intro e
  dsimp only [b] at hchart ⊢
  simp only [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    coefficients_sub, GlobalCurrent.coefficients_smul,
    coefficients_smoothGlobalCurrent, globalDDC_coefficients, coefficients_integrationCurrent]
  rw [smoothFormDistribution_sub (canonicalBasis (m + 1)) θ (c • E.curvature) e,
    smoothFormDistribution_smul_closed c E.curvature e, hchart e]
  module

/-- Original compact smooth-divisor geometry and the original theta-PSH
potential produce a genuine potential for the literal current difference,
and every FULL positive test pairing, closedness and type `(1,1)`.
No current equality or positivity is an input. -/
theorem exists_normalized_smooth_divisor_full_positive_residual
    [CompactSpace M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
        (extensionAcross W (smoothDivisorOffResidual E c u)),
        thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
            thetaPotentialCurrent θ.val u hu -
              (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E ∧
        (thetaPotentialCurrent θ.val u hu -
          (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).IsClosed
            (canonicalBasis (m + 1)) ∧
        (thetaPotentialCurrent θ.val u hu -
          (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).IsTypeOneOne
            (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
        ∀ (e : ComplexChart (m + 1) M) (α : TestForm (chartTarget e) (2 * m)),
          (∀ x, α x ∈ StronglyPositiveForms.spCone m) →
            0 ≤ (thetaPotentialCurrent θ.val u hu -
              (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).inChart e
                (CanonicalComplementaryCurrentTests.castTestDegree
                  (by rw [complexModel_real_finrank]; omega :
                    2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  let c : ℝ≥0 :=
    (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  obtain ⟨D, hDI, E, hEW, hmetric, hv⟩ :=
    exists_normalized_smooth_divisor_residual_potential hu hW
  have hEq := smooth_divisor_residual_current_eq hu hW E hEW c hv
  refine ⟨D, hDI, E, hEW, hmetric, hv, hEq, ?_⟩
  rw [← hEq]
  exact thetaPotentialCurrent_closed_type_positive
    (θ - (c : ℝ) • E.curvature).val _ hv


/-- Original compact smooth-divisor geometry and the original theta-PSH
potential produce a genuine potential for the literal current difference,
and every FULL positive test pairing, closedness and type `(1,1)`.
No current equality or positivity is an input. -/
theorem exists_smooth_divisor_full_positive_residual
    [CompactSpace M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
      ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
        (extensionAcross W (smoothDivisorOffResidual E c u)),
        thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
            thetaPotentialCurrent θ.val u hu -
              (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E ∧
        (thetaPotentialCurrent θ.val u hu -
          (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).IsClosed
            (canonicalBasis (m + 1)) ∧
        (thetaPotentialCurrent θ.val u hu -
          (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).IsTypeOneOne
            (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
        ∀ (e : ComplexChart (m + 1) M) (α : TestForm (chartTarget e) (2 * m)),
          (∀ x, α x ∈ StronglyPositiveForms.spCone m) →
            0 ≤ (thetaPotentialCurrent θ.val u hu -
              (c : ℝ) • integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E).inChart e
                (CanonicalComplementaryCurrentTests.castTestDegree
                  (by rw [complexModel_real_finrank]; omega :
                    2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  obtain ⟨D, _hDI, E, hEW, _hmetric, hv, hEq, hclosed, htype, hpositive⟩ :=
    exists_normalized_smooth_divisor_full_positive_residual hu hW
  exact ⟨E, hEW, hv, hEq, hclosed, htype, hpositive⟩

end SGPT.Okounkov
