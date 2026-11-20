import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

set_option autoImplicit false

/-! # The source trace definition on the original compact-domain submanifold -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition

open FirstPass FirstPass.BlowupSequences FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {W : Set M}

/-- The original submanifold internally supplies the complete target geometry. -/
def IsNaturalSourceTraceRepresentative (omega : KahlerBackground n M)
    (hW : IsClosedConnectedSubmanifold n W k) (u : M → EReal) (τ : W → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  IsSourceTraceRepresentativeAlong omega
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
    (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) u τ

/-- Exactly the same existential trace data, with a point zero of the ambient reader. -/
def HasNaturalPointTraceWitness (omega : KahlerBackground n M)
    (hW : IsClosedConnectedSubmanifold n W k) (u : M → EReal) (τ : W → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let omegaW : KahlerBackground k W :=
    SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  ∃ (θ : ClosedRealOneOneForm n M) (ε : ℕ → ℝ) (uSeq : ℕ → M → EReal),
    IsQuasiEquisingularApproximation omega θ u ε uSeq ∧
      ∃ x : W, squaredLogLelongNumber (n := n) u (x : M) = 0 ∧
        ∃ β : KahlerBackground k W,
          IsAdmissibleTraceBackground hι omega θ ε β.form ∧
          ∃ hτ : IsThetaPshPotential β.form.val τ,
            ∃ hterms : ∀ j, IsThetaPshPotential β.form.val (fun y => uSeq j (y : M)),
              Tendsto (fun j => (⟨fun y => uSeq j (y : M), hterms j⟩ : ThetaPshL1 β.form.val))
                atTop (@nhds (ThetaPshL1 β.form.val)
                  (singularityPseudoMetricSpace omegaW β.form
                    (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
                  ⟨τ, hτ⟩)

/-- The actual source minimum and infimum forms retain every trace witness. -/
theorem naturalSourceTrace_iff_pointWitness (omega : KahlerBackground n M)
    (hW : IsClosedConnectedSubmanifold n W k) (u : M → EReal) (τ : W → EReal) :
    IsNaturalSourceTraceRepresentative omega hW u τ ↔
      HasNaturalPointTraceWitness omega hW u τ := by
  classical
  dsimp only [IsNaturalSourceTraceRepresentative, HasNaturalPointTraceWitness]
  unfold IsSourceTraceRepresentativeAlong
  constructor
  · rintro ⟨hzero, θ, ε, uSeq, hqea, β, hβ, hτ, hterms, hlim⟩
    obtain ⟨x, hx⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_zero_of_QEA
      omega θ hqea hW hzero
    exact ⟨θ, ε, uSeq, hqea, x, hx, β, hβ, hτ, hterms, hlim⟩
  · rintro ⟨θ, ε, uSeq, hqea, x, hx, β, hβ, hτ, hterms, hlim⟩
    have hzero : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) u = 0 := by
      apply le_antisymm ?_ bot_le
      unfold sourceGenericLelongNumber
      exact (iInf_le (fun y : W => squaredLogLelongNumber (n := n) u (y : M)) x).trans
        (le_of_eq hx)
    exact ⟨hzero, θ, ε, uSeq, hqea, β, hβ, hτ, hterms, hlim⟩

end
end SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
