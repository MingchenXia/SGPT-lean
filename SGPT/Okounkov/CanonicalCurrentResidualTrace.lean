import SGPT.Okounkov.OriginalCurrentResidualTrace
import SGPT.Okounkov.ThetaPotentialCurrentReader

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

/-- The original current itself produces the canonical finite attained
divisor coefficient and the whole residual/plain-trace handoff. -/
theorem exists_canonical_original_current_residual_sourceTrace
    (omega : KahlerBackground (m + 1) M)
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ μ : M → ℝ≥0∞, IsOriginalCurrentSourceReader T μ ∧
      (⨅ p : W, μ p) ≠ ⊤ ∧ (∃ p : W, μ p = ⨅ q : W, μ q) ∧
      ∃ (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
        (hu : IsThetaPshPotential θ.val u),
        T = thetaPotentialCurrent θ.val u hu ∧
        μ = (fun p => squaredLogLelongNumber (n := m + 1) u p) ∧
        let c : ℝ≥0 := (⨅ p : W, μ p).toNNReal
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
  obtain ⟨μ, hμ, hinv⟩ :=
    exists_original_full_positive_current_theta_invariant_source_reader T hclosed h11 hT
  obtain ⟨θ, u, hu, hread, hres⟩ :=
    exists_original_full_positive_current_residual_sourceTrace omega T hclosed h11 hT hW
  have hpoint : μ = fun p => squaredLogLelongNumber (n := m + 1) u p :=
    hinv θ.val u hu hread
  have hgeneric : (⨅ p : W, μ p) =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u := by
    exact iInf_congr fun p => congrFun hpoint p
  have hfinite : (⨅ p : W, μ p) ≠ ⊤ := by
    rw [hgeneric]
    exact sourceGeneric_subtype_ne_top hW hu.quasiPshPotential
  obtain ⟨p, hp⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum
    hu.quasiPshPotential.1 hW
  refine ⟨μ, hμ, hfinite, ⟨p, ?_⟩, θ, u, hu, hread, hpoint, ?_⟩
  · rw [hgeneric, congrFun hpoint p]
    exact hp
  · simpa only [hgeneric] using hres

end SGPT.Okounkov
