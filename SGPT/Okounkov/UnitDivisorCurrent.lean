import SGPT.Okounkov.SmoothDivisorTrace
import SGPT.Foundations.Analysis.Pending.ActualDivisorCurrentMetricIndependence

set_option autoImplicit false
noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

private theorem exists_unit_divisor_metric {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, DivisorMetric.IsDivisorMetric D E := by
  obtain ⟨D, hDI, E, _hEW, hmetric, _hforms⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms hW
  exact ⟨D, hDI, E, hmetric⟩

omit [IsComplexManifold (m + 1) M] [CompactSpace M] in
private theorem effectiveDivisor_eq_of_ideal_eq {D D' : EffectiveDivisor (m + 1) M}
    (h : D.ideal = D'.ideal) : D = D' := by
  cases D
  cases D'
  cases h
  rfl

/-- The actual whole unit integration current of the original smooth
divisor, constructed from its genuine unit vanishing ideal and metric. -/
def smoothDivisorIntegrationCurrent {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  let E := Classical.choose (Classical.choose_spec (exists_unit_divisor_metric hW)).2
  LelongPoincareDivisor.integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E

/-- Every metric of the actual original unit ideal produces the same
whole integration current, retaining its divisor-supported coefficients. -/
theorem smoothDivisorIntegrationCurrent_eq_of_unit_metric {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hmetric : DivisorMetric.IsDivisorMetric D E) :
    smoothDivisorIntegrationCurrent hW =
      LelongPoincareDivisor.integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E := by
  let D₀ := Classical.choose (exists_unit_divisor_metric hW)
  have hD₀ : D₀.ideal = vanishingIdeal (n := m + 1) W :=
    (Classical.choose_spec (exists_unit_divisor_metric hW)).1
  let E₀ := Classical.choose (Classical.choose_spec (exists_unit_divisor_metric hW)).2
  have hmetric₀ : DivisorMetric.IsDivisorMetric D₀ E₀ :=
    Classical.choose_spec (Classical.choose_spec (exists_unit_divisor_metric hW)).2
  have hD : D₀ = D := effectiveDivisor_eq_of_ideal_eq (hD₀.trans hDI.symm)
  exact ActualDivisorCurrentMetricIndependence.integrationCurrent_eq_of_isDivisorMetric
    (canonicalBasis (m + 1)) D₀ E₀ E hmetric₀ (hD.symm ▸ hmetric)

/-- The checked residual identity uses the literal actual unit current of
the original divisor, independently of its genuine smooth metric. -/
theorem smooth_divisor_residual_current_eq_unit_current
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) (c : ℝ≥0)
    (hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u))) :
    thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
        thetaPotentialCurrent θ.val u hu - (c : ℝ) • smoothDivisorIntegrationCurrent hW := by
  rw [smoothDivisorIntegrationCurrent_eq_of_unit_metric hW D hDI E hmetric]
  exact smooth_divisor_residual_current_eq hu hW E hEW c hv

end SGPT.Okounkov
