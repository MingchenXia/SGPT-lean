import SGPT.Okounkov.UnitDivisorCurrent
import SGPT.Okounkov.ThetaPotentialCurrentSingularity

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- Different genuine unit metrics and theta representations of the same
original current produce the same whole residual current. -/
theorem smooth_divisor_residual_currents_eq_of_thetaPotentialCurrent_eq
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (heq : thetaPotentialCurrent θ.val u hu = thetaPotentialCurrent σ.val v hv)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D₀ D₁ : EffectiveDivisor (m + 1) M)
    (hDI₀ : D₀.ideal = vanishingIdeal (n := m + 1) W)
    (hDI₁ : D₁.ideal = vanishingIdeal (n := m + 1) W)
    (E₀ E₁ : MeteredEffectiveQDivisor (m + 1) M)
    (hEW₀ : E₀.support = W) (hEW₁ : E₁.support = W)
    (hmetric₀ : DivisorMetric.IsDivisorMetric D₀ E₀)
    (hmetric₁ : DivisorMetric.IsDivisorMetric D₁ E₁)
    (hres₀ : IsThetaPshPotential
      (θ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toReal • E₀.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u)))
    (hres₁ : IsThetaPshPotential
      (σ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toReal • E₁.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₁
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v))) :
    thetaPotentialCurrent
      (θ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toReal • E₀.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u)) hres₀ =
    thetaPotentialCurrent
      (σ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toReal • E₁.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₁
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v)) hres₁ := by
  have hcoef := sourceGeneric_eq_of_thetaPotentialCurrent_eq hu hv heq (Subtype.val : W → M)
  calc
    _ = thetaPotentialCurrent θ.val u hu -
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toReal •
          smoothDivisorIntegrationCurrent hW := by
      exact smooth_divisor_residual_current_eq_unit_current hu hW D₀ hDI₀ E₀ hEW₀ hmetric₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal hres₀
    _ = thetaPotentialCurrent σ.val v hv -
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toReal •
          smoothDivisorIntegrationCurrent hW := by rw [heq, hcoef]
    _ = _ := (smooth_divisor_residual_current_eq_unit_current hv hW D₁ hDI₁ E₁ hEW₁ hmetric₁
      (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal hres₁).symm

/-- True same-current residual choices have every actual multiplier ideal
equal, through produced local smooth differences and compact global bounds. -/
theorem iEquivalent_smooth_divisor_residuals_of_thetaPotentialCurrent_eq
    [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (heq : thetaPotentialCurrent θ.val u hu = thetaPotentialCurrent σ.val v hv)
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D₀ D₁ : EffectiveDivisor (m + 1) M)
    (hDI₀ : D₀.ideal = vanishingIdeal (n := m + 1) W)
    (hDI₁ : D₁.ideal = vanishingIdeal (n := m + 1) W)
    (E₀ E₁ : MeteredEffectiveQDivisor (m + 1) M)
    (hEW₀ : E₀.support = W) (hEW₁ : E₁.support = W)
    (hmetric₀ : DivisorMetric.IsDivisorMetric D₀ E₀)
    (hmetric₁ : DivisorMetric.IsDivisorMetric D₁ E₁)
    (hres₀ : IsThetaPshPotential
      (θ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toReal • E₀.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u)))
    (hres₁ : IsThetaPshPotential
      (σ - (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toReal • E₁.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E₁
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v))) :
    IEquivalentOnManifold (n := m + 1)
      (extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u))
      (extensionAcross W (smoothDivisorOffResidual E₁
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v).toNNReal v)) := by
  exact iEquivalent_of_thetaPotentialCurrent_eq omega hres₀ hres₁
    (smooth_divisor_residual_currents_eq_of_thetaPotentialCurrent_eq hu hv heq hW D₀ D₁
      hDI₀ hDI₁ E₀ E₁ hEW₀ hEW₁ hmetric₀ hmetric₁ hres₀ hres₁)

end SGPT.Okounkov
