import SGPT.Checks.Comparison.TraceWholeSourceDefinition
import SGPT.Checks.Comparison.TraceResIntrinsicEquivalent

/-! Remaining ORIGINAL rmk:NApotential:L47 clause: actual singular-Y trace
family commutes with change of representative in GENERAL KAHLER scope.
Original carrier hwd/cutoff, actual NA objects and actual divisorial readers.
No false Kahler pullback, target algebraization or Hironaka development.
Blueprint: trace-family-representative.tex. -/
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
  {θ η : AtlasClosedRealOneOneForm (ofFixedModel n X)}
  (omegaX : KahlerBackground n X)
  (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
    RealBottChern.ofRepresentative (atlasClosedFormToNative η))

include omegaX in
/-- Literal ORIGINAL carrier hwd is unchanged, with R internally chosen. -/
theorem carrierTraceWellDefined_changeRepresentative
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (Γ : SourceNAPotential θ) :
    carrierTraceWellDefined Y (Γ.changeRepresentative hc) ↔ carrierTraceWellDefined Y Γ := by
  let R := resolutionTraceTarget Y omegaX
  exact (traceWellDefined_resolution_iff R (Γ.changeRepresentative hc)).symm.trans
    ((traceWellDefined_changeRepresentative_iff R.ι hc Γ).trans (traceWellDefined_resolution_iff R Γ))

include omegaX in
/-- Literal ORIGINAL carrier cutoff is unchanged at EVERY actual index. -/
theorem carrierTraceCutoff_changeRepresentative
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n X) :
    carrierTraceCutoff Y (Γ.changeRepresentative hc) κ = carrierTraceCutoff Y Γ κ := by
  let R := resolutionTraceTarget Y omegaX
  exact (traceCutoff_resolution_eq R (Γ.changeRepresentative hc) κ).symm.trans
    ((traceCutoff_changeRepresentative R.ι hc Γ κ).trans (traceCutoff_resolution_eq R Γ κ))

/-- Actual NA OBJECT equality for the correct positive-VOLUME geometry,
not the stronger and false Kahler-pullback condition of a resolution. -/
theorem traceRes_changeRepresentative_of_volumePos
    {k : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [CompactSpace V] [ConnectedSpace V]
    [MeasurableSpace V] [BorelSpace V]
    (hk : k ≤ n) (omegaV : KahlerBackground k V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    naTraceRes hk omegaX omegaV hι hvol (Γ.changeRepresentative hc)
        ((traceWellDefined_changeRepresentative_iff ι hc Γ).mpr hwd) =
      (naTraceRes hk omegaX omegaV hι hvol Γ hwd).changeRepresentative
        (nativeHolomorphicPullback_class_eq hι hc) := by
  let κV := sourceKahlerFormOfBackground omegaV
  have horder := Γ.changeRepresentative_POrder_equivalent omegaX hc
  apply BJPrep.eq_of_naDivisorialTransform_eq κV
  · change traceCutoff ι (Γ.changeRepresentative hc) (sourceKahlerFormOfBackground omegaX) =
      traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX)
    exact traceCutoff_changeRepresentative ι hc Γ _
  · intro p t _ht
    have hsame := naTraceRes_divisorial_eq_of_naOrder_equivalent hk omegaX omegaV hι hvol
      horder.1 horder.2 hwd κV p (t : ℝ)
    have htarget := naDivisorialTransform_changeRepresentative
      (nativeHolomorphicPullback_class_eq hι hc) (naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p (t : ℝ)
    exact hsame.symm.trans htarget.symm

/-- CLOSED actual family equality for arbitrary SINGULAR original Y,
all original target choices INTERNAL; no rational/metric assumptions. -/
theorem resolutionTraceFamily_changeRepresentative
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) :
    resolutionTraceFamily Y omegaX (Γ.changeRepresentative hc)
      ((carrierTraceWellDefined_changeRepresentative omegaX hc Y Γ).mpr hwd) =
    fun R => (resolutionTraceFamily Y omegaX Γ hwd R).changeRepresentative
      (nativeHolomorphicPullback_class_eq R.contMDiff hc) := by
  funext R
  exact traceRes_changeRepresentative_of_volumePos omegaX hc Y.dim_le R.kahler R.contMDiff
    (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) Γ (carrierTraceWellDefined_on Y Γ hwd R)

/-- Actual original native divisorial FUNCTIONS are unchanged by changing
representative, at EVERY actual R/index/real weight/trivial point. -/
theorem resolutionTraceFamily_divisorial_changeRepresentative
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) (R : ResolutionTarget Y) (κR : SourceKahlerForm Y.dim R.V) :
    nativeDivisorialFunction (resolutionTraceFamily Y omegaX (Γ.changeRepresentative hc)
      ((carrierTraceWellDefined_changeRepresentative omegaX hc Y Γ).mpr hwd) R) κR =
    nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R) κR := by
  have h := congrFun (resolutionTraceFamily_changeRepresentative omegaX hc Y Γ hwd) R
  rw [h]
  exact nativeDivisorialFunction_changeRepresentative
    (nativeHolomorphicPullback_class_eq R.contMDiff hc) (resolutionTraceFamily Y omegaX Γ hwd R) κR

/-- Closed source-facing REMAINING clause of rmk:NApotential:L47:
original singular-Y trace construction is independent of representative,
as ACTUAL full family/object/function equalities. Other operations of the
remark are already independently proved; no new premise is introduced. -/
theorem source_trace_changeRepresentative
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) :
    let hwd' := (carrierTraceWellDefined_changeRepresentative omegaX hc Y Γ).mpr hwd
    IsOriginalResolutionTraceFamily Y (Γ.changeRepresentative hc)
        (resolutionTraceFamily Y omegaX (Γ.changeRepresentative hc) hwd') ∧
    (∀ κ : SourceKahlerForm n X,
      carrierTraceCutoff Y (Γ.changeRepresentative hc) κ = carrierTraceCutoff Y Γ κ) ∧
    (resolutionTraceFamily Y omegaX (Γ.changeRepresentative hc) hwd' =
      fun R => (resolutionTraceFamily Y omegaX Γ hwd R).changeRepresentative
        (nativeHolomorphicPullback_class_eq R.contMDiff hc)) ∧
    (∀ (R : ResolutionTarget Y) (κR : SourceKahlerForm Y.dim R.V),
      nativeDivisorialFunction (resolutionTraceFamily Y omegaX (Γ.changeRepresentative hc) hwd' R) κR =
        nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R) κR) := by
  dsimp only
  exact ⟨source_naTrace_family Y omegaX (Γ.changeRepresentative hc)
      ((carrierTraceWellDefined_changeRepresentative omegaX hc Y Γ).mpr hwd),
    carrierTraceCutoff_changeRepresentative omegaX hc Y Γ,
    resolutionTraceFamily_changeRepresentative omegaX hc Y Γ hwd,
    resolutionTraceFamily_divisorial_changeRepresentative omegaX hc Y Γ hwd⟩

end SGPT.NAPotential.TraceComparison
