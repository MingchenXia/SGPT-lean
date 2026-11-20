import SGPT.Okounkov.SmoothDivisorTrace
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation

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
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- Every original closed fully positive current internally supplies the
genuine global potential, unit-divisor residual and plain source trace.
No analytic local-potential premise or given global potential is required. -/
theorem exists_original_full_positive_current_residual_sourceTrace
    (omega : KahlerBackground (m + 1) M)
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
      (hu : IsThetaPshPotential θ.val u),
      T = thetaPotentialCurrent θ.val u hu ∧
      let c : ℝ≥0 :=
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
      ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
        ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
          DivisorMetric.IsDivisorMetric D E ∧
        ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
            (extensionAcross W (smoothDivisorOffResidual E c u)),
          thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
            (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
              T - (c : ℝ) • LelongPoincareDivisor.integrationCurrent
                (canonicalBasis (m + 1)) (Nat.succ_pos m) E ∧
          sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
            (extensionAcross W (smoothDivisorOffResidual E c u)) = 0 ∧
          ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW
            (extensionAcross W (smoothDivisorOffResidual E c u)) τ := by
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hclosed h11 hT
  obtain ⟨D, hDI, E, hEW, hmetric, hv, hEq, hzero, τ, hτ⟩ :=
    exists_normalized_smooth_divisor_residual_current_sourceTrace omega hu hW
  refine ⟨θ, u, hu, hread, D, hDI, E, hEW, hmetric, hv, ?_, hzero, τ, hτ⟩
  simpa only [hread] using hEq

end SGPT.Okounkov
