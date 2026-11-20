import SGPT.Okounkov.DivisorResidualGenericZero
import SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistenceAllDimensions

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
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
open NaturalSubmanifoldSourceTraceDefinition

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- The original smooth divisor and original potential produce a genuine
plain source trace of the actual unit-divisor residual. All approximation,
restriction and singularity-metric witnesses are internally produced. -/
theorem exists_normalized_smooth_divisor_residual_sourceTrace
    (omega : KahlerBackground (m + 1) M)
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
        IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) ∧
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
          (extensionAcross W (smoothDivisorOffResidual E c u)) = 0 ∧
        ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW
          (extensionAcross W (smoothDivisorOffResidual E c u)) τ := by
  obtain ⟨D, hDI, E, hEW, hmetric, hv, hzero⟩ :=
    exists_normalized_smooth_divisor_residual_generic_zero hu hW
  obtain ⟨τ, hτ⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      omega hW hv hzero
  exact ⟨D, hDI, E, hEW, hmetric, hv, hzero, τ, hτ⟩

/-- The same actual unit-normalized residual current, rather than an
analytic-singularity substitute, has a genuine source plain trace. -/
theorem exists_normalized_smooth_divisor_residual_current_sourceTrace
    (omega : KahlerBackground (m + 1) M)
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)),
        NaturalThetaPshGeometricCurrent.thetaPotentialCurrent
          (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
            NaturalThetaPshGeometricCurrent.thetaPotentialCurrent θ.val u hu -
              (c : ℝ) • LelongPoincareDivisor.integrationCurrent
                (CanonicalCurrentFrame.canonicalBasis (m + 1)) (Nat.succ_pos m) E ∧
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
          (extensionAcross W (smoothDivisorOffResidual E c u)) = 0 ∧
        ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW
          (extensionAcross W (smoothDivisorOffResidual E c u)) τ := by
  obtain ⟨D, hDI, E, hEW, hmetric, hv, hzero, τ, hτ⟩ :=
    exists_normalized_smooth_divisor_residual_sourceTrace omega hu hW
  exact ⟨D, hDI, E, hEW, hmetric, hv,
    smooth_divisor_residual_current_eq hu hW E hEW _ hv, hzero, τ, hτ⟩

end SGPT.Okounkov
