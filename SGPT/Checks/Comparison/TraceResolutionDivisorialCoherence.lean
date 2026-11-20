import SGPT.Checks.Comparison.TraceNADivisorialPullback
import SGPT.NAPotential.P5WireNATrace

/-! ACTUAL native divisorial function coherence on an ACTUAL internally
produced common resolution of two original ResolutionTargets.
Only existing accepted resolution theorems are reused.
Blueprint: trace-resolution-divisor-transport.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.PSH.CompactPrimeOver SGPT.Trace.Trace2Resolution
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open AnalyticModificationLocalDiscrepancy SGPT.NAPotential.RIsoB
open SGPT.NAPotential.NATrace SGPT.NAPotential.TraceRes
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
  {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- Given two ORIGINAL actual resolution targets, an ACTUAL internally
constructed common target makes the unchanged actual trace functions
coherent under SAME actual prime composition, all positive REAL weights
and the trivial point. No common-model or function identity certificate
is an input; all target dimensions include zero. -/
theorem exists_nativeDivisorial_commonResolution
    (R₁ R₂ : ResolutionTarget Y) (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R₁.ι Γ) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V)
      (hp₁ : IsAnalyticModification (n := Y.dim) p₁)
      (hp₂ : IsAnalyticModification (n := Y.dim) p₂),
      (∀ w, R₃.ι w = R₁.ι (p₁ w)) ∧ (∀ w, R₃.ι w = R₂.ι (p₂ w)) ∧
      ∀ (κ₁ : SourceKahlerForm Y.dim R₁.V) (κ₂ : SourceKahlerForm Y.dim R₂.V)
        (κ₃ : SourceKahlerForm Y.dim R₃.V),
      (nativeDivisorialFunction
          (naTraceResolution R₃ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₃ Γ hwd)) κ₃ =
        fun v => nativeDivisorialFunction (naTraceResolution R₁ omegaX Γ hwd) κ₁
          (nativeDivisorialPush hp₁ v)) ∧
      (nativeDivisorialFunction
          (naTraceResolution R₃ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₃ Γ hwd)) κ₃ =
        fun v => nativeDivisorialFunction (naTraceResolution R₂ omegaX Γ
          (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd)) κ₂ (nativeDivisorialPush hp₂ v)) := by
  obtain ⟨R₃,p₁,p₂,hp₁,hp₂,hc₁,hc₂,he₁,he₂⟩ :=
    SGPT.NAPotential.P5Wire.naTraceResolution_common R₁ R₂ omegaX Γ hwd
  refine ⟨R₃,p₁,p₂,hp₁,hp₂,hc₁,hc₂,?_⟩
  intro κ₁ κ₂ κ₃
  constructor
  · have he := nativeDivisorialFunction_changeRepresentative
      (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ)
      (sourceNAPullback R₁.kahler hp₁ (naTraceResolution R₁ omegaX Γ hwd)) κ₃
    rw [he₁] at he
    exact he.trans (nativeDivisorialFunction_pullback R₁.kahler hp₁
      (naTraceResolution R₁ omegaX Γ hwd) κ₃ κ₁)
  · have he := nativeDivisorialFunction_changeRepresentative
      (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ)
      (sourceNAPullback R₂.kahler hp₂ (naTraceResolution R₂ omegaX Γ
        (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd))) κ₃
    rw [he₂] at he
    exact he.trans (nativeDivisorialFunction_pullback R₂.kahler hp₂
      (naTraceResolution R₂ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd)) κ₃ κ₂)

end SGPT.NAPotential.TraceComparison
