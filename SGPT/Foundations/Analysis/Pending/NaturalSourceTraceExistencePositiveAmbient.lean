import SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition

set_option autoImplicit false

/-! # Source trace existence from the genuine approximation in positive ambient dimension -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistencePositiveAmbient

open FirstPass FirstPass.BlowupSequences FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The same original approximation produces a source trace and model witness. -/
theorem exists_sourceTrace_of_QEA (hn : n ≠ 0)
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    ∃ τ : V → EReal, IsSourceTraceRepresentativeAlong omega omegaV hι u τ ∧
      ∃ β : KahlerBackground k V, IsModelPotential β.form τ := by
  have hnative := (nativeGeneric_zero_iff_source hn ι u).mpr hgeneric
  obtain ⟨τ, hτ, β, hmodel⟩ :=
    TraceRepresentativeConstruction.exists_of_quasiEquisingularApproximation
      omegaV happ hι hnative
  exact ⟨τ, (isSourceTraceRepresentativeAlong_iff_native hn omega omegaV hι u τ).mpr hτ,
    β, hmodel⟩

variable [CompactSpace M]

/-- The original submanifold internally supplies all required target geometry. -/
theorem exists_naturalSourceTrace_of_QEA (hn : n ≠ 0)
    {omega : KahlerBackground n M} {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W k)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hgeneric : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) u = 0) :
    ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW u τ := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W :=
    SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let omegaW : KahlerBackground k W :=
    SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  obtain ⟨τ, hτ, _⟩ := exists_sourceTrace_of_QEA hn omegaW happ hι hgeneric
  refine ⟨τ, ?_⟩
  change IsSourceTraceRepresentativeAlong omega omegaW hι u τ
  exact hτ

end
end SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistencePositiveAmbient
