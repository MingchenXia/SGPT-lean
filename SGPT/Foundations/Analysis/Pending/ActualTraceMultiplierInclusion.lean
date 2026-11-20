import SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

set_option autoImplicit false

/-! # Actual closed-submanifold trace readers supply every multiplier inclusion -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualTraceMultiplierInclusion

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground FirstPass.BlowupSequences
  FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  TraceRepresentativeConstruction ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  SubmanifoldChartedSpace SubmanifoldIdealRestriction

noncomputable section

variable {n k : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  {W : Set X} [MeasurableSpace W] [BorelSpace W]

/-- The actual closed-submanifold and trace data internally supply every
stage global order and ideal order before genuine openness and OT are consumed. -/
theorem multiplierIdeal_le_restrictIdeal_of_isTraceRepresentativeAlong
    (hW : IsClosedConnectedSubmanifold n W k) (omega : KahlerBackground n X) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI := chartedSpace hk hW.2.2
    haveI := isComplexManifold_chartedSpace hk hW.2.2
    ∀ (omegaW : KahlerBackground k W) {u : X → EReal} {τ : W → EReal},
      IsTraceRepresentativeAlong omega omegaW (contMDiff_val hk hW.2.2) u τ →
      ∀ {c : ℝ}, 0 < c →
        (multiplierIdeal (n := k) c τ).Le
          (restrictIdeal (k := k) (W := W) (multiplierIdeal (n := n) c u)) := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  dsimp only
  intro omegaW u τ htrace c hc
  obtain ⟨_, θ, _, U, happ, β, _, hτ, hterms, hlim⟩ := htrace
  let A : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y : W => U j y.1, hterms j⟩
  have hanti : Antitone (fun j => (A j).val) := fun i j hij y =>
    happ.term_antitone y.1 hij
  have horder (j : ℕ) : SingularGlobalPOrder.SourcePOrder (n := k) τ (fun y : W => U j y.1) :=
    TraceRepresentativeStageGlobalPOrder.sourcePOrder_le_stage_of_antitone_native_limit
      omegaW β.form (isBigClass_kahler β) A ⟨τ, hτ⟩ hanti hlim j
  have hI : ∀ᶠ j in atTop, FirstPass.IEnvelope.IOrderOnManifold (n := k)
      τ (fun y : W => U j y.1) :=
    Filter.Eventually.of_forall fun j =>
      GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder (horder j)
  exact PositiveCurrentTraceMultiplier.multiplierIdeal_le_restrictIdeal_of_eventually_iOrder
    happ hk hW.2.2 hτ.1.quasiPlurisubharmonic hI hc

end

end SGPT.Foundations.Analysis.Pending.ActualTraceMultiplierInclusion
