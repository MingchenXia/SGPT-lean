import SGPT.Checks.Comparison.TraceResActualRepresentatives
import SGPT.NAPotential.ProjectiveLimit

/-! Original cross-background intrinsic equivalence and ACTUAL traced divisorial values.
Blueprint: `trace-res-prime-limit.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)

/-- Mutually ordered ORIGINAL NA curves in possibly DIFFERENT original
backgrounds have identical ACTUAL traced component prime readers. All actual
trace representatives and source/target ideal comparisons are internal. -/
theorem traceRes_slice_reader_eq_of_naOrder_equivalent
    {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (hΓΔ : SourceNAPOrder Γ Δ) (hΔΓ : SourceNAPOrder Δ Γ)
    (hwd : TraceWellDefined ι Γ) (κV : SourceKahlerForm k V) (s : ℝ)
    (hsΓ : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max)
    (hsΔ : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol Δ
      (traceWellDefined_of_naOrder hΓΔ hwd)).component κV).val.max)
    (p : PrimePresentation k V) :
    presentationReader (((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨s,hsΓ⟩) p =
      presentationReader (((TraceRes.naTraceRes hk omegaX omegaV hι hvol Δ
        (traceWellDefined_of_naOrder hΓΔ hwd)).component κV).val.potential ⟨s,hsΔ⟩) p := by
  obtain ⟨ψ,hψ,hTψ,_hIψ,hRψ⟩ := exists_actualTraceComponentRepresentative hk omegaX omegaV hι hvol Γ hwd κV s hsΓ
  obtain ⟨φ,hφ,hTφ,_hIφ,hRφ⟩ := exists_actualTraceComponentRepresentative hk omegaX omegaV hι hvol Δ
    (traceWellDefined_of_naOrder hΓΔ hwd) κV s hsΔ
  let κX := sourceKahlerFormOfBackground omegaX
  have hsXΓ := (sliceTraceable_of_lt_traceCutoff hwd κX hsΓ).1
  have hsXΔ := (sliceTraceable_of_lt_traceCutoff (traceWellDefined_of_naOrder hΓΔ hwd) κX hsΔ).1
  have hIΓΔ := GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
    (((sourceNAPOrder_iff_component Γ Δ κX).mp hΓΔ).slice_le s hsXΓ)
  have hIΔΓ := GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
    (((sourceNAPOrder_iff_component Δ Γ κX).mp hΔΓ).slice_le s hsXΔ)
  have hPψφ := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives
    hk omegaV omegaV hι hTψ hTφ hIΓΔ
  have hPφψ := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives
    hk omegaV omegaV hι hTφ hTψ hIΔΓ
  have hqψ : (ofFixedModel k V).IsQPSH ψ := ⟨_,thetaPSH_traceBackground_of_half hι κV hψ⟩
  have hqφ : (ofFixedModel k V).IsQPSH φ := ⟨_,thetaPSH_traceBackground_of_half hι κV hφ⟩
  have hread : presentationReader ψ p = presentationReader φ p :=
    le_antisymm
      ((sourceIOrder_iff_presentationComparison hqφ hqψ).mp
        (sourceIOrder_of_sourcePOrder hqφ hqψ hPφψ) p)
      ((sourceIOrder_iff_presentationComparison hqψ hqφ).mp
        (sourceIOrder_of_sourcePOrder hqψ hqφ hPψφ) p)
  exact (hRψ p).trans (hread.trans (hRφ p).symm)

/-- The EXISTING original actual native divisorial trace transform is
unchanged under original mutual intrinsic order across DIFFERENT backgrounds. -/
theorem naTraceRes_divisorial_eq_of_naOrder_equivalent
    {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (hΓΔ : SourceNAPOrder Γ Δ) (hΔΓ : SourceNAPOrder Δ Γ)
    (hwd : TraceWellDefined ι Γ) (κV : SourceKahlerForm k V)
    (p : PrimePresentation k V) (c : ℝ) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Δ
        (traceWellDefined_of_naOrder hΓΔ hwd)) κV p c := by
  have hmax : ((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max =
      ((TraceRes.naTraceRes hk omegaX omegaV hι hvol Δ (traceWellDefined_of_naOrder hΓΔ hwd)).component κV).val.max :=
    le_antisymm (traceCutoff_mono_of_naOrder hΓΔ hwd (sourceKahlerFormOfBackground omegaX))
      (traceCutoff_mono_of_naOrder hΔΓ (traceWellDefined_of_naOrder hΓΔ hwd) (sourceKahlerFormOfBackground omegaX))
  unfold BJPrep.naDivisorialTransform BJPrep.curveDivisorialTransform
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => ?_
    have hs' := hmax ▸ hs
    rw [traceRes_slice_reader_eq_of_naOrder_equivalent hk omegaX omegaV hι hvol hΓΔ hΔΓ hwd κV s hs hs' p]
    exact le_iSup_of_le s (le_iSup_of_le hs' le_rfl)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    have hs' := hmax.symm ▸ hs
    rw [← traceRes_slice_reader_eq_of_naOrder_equivalent hk omegaX omegaV hι hvol hΓΔ hΔΓ hwd κV s hs' hs p]
    exact le_iSup_of_le s (le_iSup_of_le hs' le_rfl)

include omegaX in
omit [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The ORIGINAL common-background I-transition leaves the ACTUAL
original trace cutoff unchanged, with no comparison certificate supplied. -/
theorem traceCutoff_transition (Γ : SourceNAPotential θ)
    (hθσ : (atlasClosedFormToNative σ - atlasClosedFormToNative θ).val.IsSemipositive)
    (hwd : TraceWellDefined ι Γ) (κX : SourceKahlerForm n M) :
    traceCutoff ι Γ κX = traceCutoff ι (Γ.transition hθσ) κX := by
  have hT := Γ.transition_POrder_equivalent omegaX hθσ
  exact le_antisymm (traceCutoff_mono_of_naOrder hT.1 hwd κX)
    (traceCutoff_mono_of_naOrder hT.2 (traceWellDefined_of_naOrder hT.1 hwd) κX)

/-- The ORIGINAL actual common-background I-projection leaves the
UNCHANGED actual traced native divisorial transform unchanged. -/
theorem naTraceRes_divisorial_transition (Γ : SourceNAPotential θ)
    (hθσ : (atlasClosedFormToNative σ - atlasClosedFormToNative θ).val.IsSemipositive)
    (hwd : TraceWellDefined ι Γ) (κV : SourceKahlerForm k V)
    (p : PrimePresentation k V) (c : ℝ) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol (Γ.transition hθσ)
        (traceWellDefined_of_naOrder (Γ.transition_POrder_equivalent omegaX hθσ).1 hwd)) κV p c :=
  naTraceRes_divisorial_eq_of_naOrder_equivalent hk omegaX omegaV hι hvol
    (Γ.transition_POrder_equivalent omegaX hθσ).1 (Γ.transition_POrder_equivalent omegaX hθσ).2 hwd κV p c

end SGPT.NAPotential.TraceComparison
