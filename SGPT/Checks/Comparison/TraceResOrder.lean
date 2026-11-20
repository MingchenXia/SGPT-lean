import SGPT.Checks.Comparison.TraceCutoffDecreasingInf

/-! Actual original NA trace order, with actual target volume positivity.
Blueprint: `trace-res-prime-limit.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)

include hvol in
/-- Actual original order gives literal order of the SAME actual original
trace component slices; every representative and ideal comparison is internal. -/
theorem traceComponentSlice_mono_of_naOrder {Γ Δ : SourceNAPotential θ}
    (h : SourceNAPOrder Γ Δ) (κV : SourceKahlerForm k V) {s : ℝ}
    (hs : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) s) :
    traceComponentSlice hk omegaX omegaV hι Γ κV s hs ≤
      traceComponentSlice hk omegaX omegaV hι Δ κV s
        (sliceTraceable_of_naOrder h ι (sourceKahlerFormOfBackground omegaX) hs) := by
  let hs' := sliceTraceable_of_naOrder h ι (sourceKahlerFormOfBackground omegaX) hs
  have hc := (sourceNAPOrder_iff_component Γ Δ (sourceKahlerFormOfBackground omegaX)).mp h
  have hP := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι (traceSlice_spec hk omegaX omegaV hι Γ s hs)
    (traceSlice_spec hk omegaX omegaV hι Δ s hs')
    (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder (hc.slice_le s hs.1))
  obtain ⟨φ, hφ, hE⟩ := TraceRes.exists_goodTraceSlice' hk omegaX omegaV hι hvol Δ κV s hs'
  obtain ⟨ψ, hψ, hF⟩ := TraceRes.exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV s hs
  have hqΓ := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ s hs)
  have hqΔ := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Δ s hs')
  have hI := sourceIOrder_trans hF.1
    (sourceIOrder_trans (sourceIOrder_of_sourcePOrder hqΓ hqΔ hP) hE.2)
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV s hs hF,
    traceComponentSlice_eq hk omegaX omegaV hι Δ κV s hs' hE]
  exact (sourceIOrder_iff_sourceIEnvelope_le (thetaPSH_traceBackground_of_half hι κV hψ)
    (thetaPSH_traceBackground_of_half hι κV hφ)).mp hI

/-- The UNCHANGED actual original NA trace preserves actual intrinsic order.
Upper trace existence and literal slice/cutoff comparison are produced. -/
theorem naTraceRes_mono_of_naOrder {Γ Δ : SourceNAPotential θ} (h : SourceNAPOrder Γ Δ)
    (hwd : TraceWellDefined ι Γ) :
    SourceNAPOrder (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd)
      (TraceRes.naTraceRes hk omegaX omegaV hι hvol Δ (traceWellDefined_of_naOrder h hwd)) := by
  let κV := sourceKahlerFormOfBackground omegaV
  apply (sourceNAPOrder_iff_component _ _ κV).mpr
  apply (sourceTestCurvePOrder_iff (sourceKahlerFormRepresentative κV) _ _).mpr
  have hcut := traceCutoff_mono_of_naOrder h hwd (sourceKahlerFormOfBackground omegaX)
  refine ⟨hcut, fun s hs => ?_⟩
  exact traceComponentSlice_mono_of_naOrder hk omegaX omegaV hι hvol h κV
    (sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs)

end SGPT.NAPotential.TraceComparison
