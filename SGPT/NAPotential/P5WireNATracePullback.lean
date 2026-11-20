import SGPT.NAPotential.RIsoBTraceModification
import SGPT.NAPotential.TraceResNATrace

/-! # The non-Archimedean trace and modification pullback on resolution targets

Source `prop:NApotential:L655` (`chapter_NApotential.tex`), the case of the trace operator: for a
modification `π : Y → X` of compact Kähler manifolds, an analytic subset `Z ⊆ X` along which the
trace of `Γ ∈ PSH^NA(X, θ)` is well-defined, the strict transform `W` of `Z` and the strict
transform `Π̃ : W̃ → Z̃` of `Π = π|_W`, `Π̃^* Tr_Z(Γ) = Tr_W(π^*Γ)`.

`SGPT.NAPotential.RIsoB.naTrace_pullback` proves this for smooth `Z`, `W`, given by holomorphic
maps `ι_Z : V_Z → X`, `ι_W : V_W → Y` pulling Kähler forms back to Kähler forms. Its proof uses
that hypothesis only through the construction of the trace (`NATrace.naTrace`) and the existence
of good trace slices (`NATrace.exists_good_traceSlice'`). Replacing them by their versions for
targets whose Kähler pullbacks have positive volume (`TraceRes.naTraceRes`,
`TraceRes.exists_goodTraceSlice'`) gives the statement for such targets (`naTraceRes_pullback`),
in particular for **resolution targets** of singular `Z` and `W` (every resolution target has
Kähler pullbacks of positive volume, `SGPT.Trace.RIsoB.pullbackKahlerVolumePos`, and on it
`naTraceRes` is the trace `TraceRes.naTraceResolution`), with `Π̃` a modification between the
resolving manifolds compatible with `π` (`π ∘ ι_W = ι_Z ∘ Π̃`). The proof below is that of
`RIsoB.naTrace_pullback` with these two replacements.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.P5Wire

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.NAPotential.NATrace SGPT.NAPotential.RIsoB SGPT.NAPotential.TraceRes
open SGPT.Trace.RIsoB (PullbackKahlerVolumePos)
open scoped Manifold ContDiff

universe u

variable {n k : ℕ} {X Y VZ VW : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  [TopologicalSpace VZ] [ChartedSpace (ComplexModel k) VZ] [IsComplexManifold k VZ]
  [MeasurableSpace VZ] [BorelSpace VZ] [CompactSpace VZ] [ConnectedSpace VZ]
  [TopologicalSpace VW] [ChartedSpace (ComplexModel k) VW] [IsComplexManifold k VW]
  [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] [ConnectedSpace VW]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-- **Source `prop:NApotential:L655`, the trace operator, on targets with Kähler pullbacks of
positive volume (in particular on resolution targets of singular `Z`, `W`):**
`Π̃^* Tr_Z(Γ) = Tr_W(π^*Γ)`. Here `π : Y → X` is a modification, `Z`, `W` are read on
`ι_Z : V_Z → X`, `ι_W : V_W → Y` (every Kähler form pulls back to a semipositive form of positive
volume), `Π̃ : V_W → V_Z` is a modification with `π ∘ ι_W = ι_Z ∘ Π̃`, and the trace of `Γ` along
`Z` is well-defined (then so is that of `π^*Γ` along `W`). The left-hand side is read in
`PSH^NA(V_W, ι_W^*π^*θ)` through the canonical bijection of `rmk:NApotential:L47`. -/
theorem naTraceRes_pullback (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ)
    (omegaVW : KahlerBackground k VW) {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    (hvolZ : PullbackKahlerVolumePos (M := X) hιZ)
    {ιW : VW → Y} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hvolW : PullbackKahlerVolumePos (M := Y) hιW)
    (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ιZ Γ) :
    (sourceNAPullback omegaVZ hpt
        (naTraceRes hk omegaX omegaVZ hιZ hvolZ Γ hwd)).changeRepresentative
        (pullback_comm_class_eq hπ.1 hpt.1 hιZ hιW hcomm θ) =
      naTraceRes hk omegaY omegaVW hιW hvolW (sourceNAPullback omegaX hπ Γ)
        ((traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd) := by
  set TZ := naTraceRes hk omegaX omegaVZ hιZ hvolZ Γ hwd with hTZ
  set PΓ := sourceNAPullback omegaX hπ Γ with hPΓ
  have hwdW := (traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd
  set A := sourceNAPullback omegaVZ hpt TZ with hA
  set hcl := pullback_comm_class_eq hπ.1 hpt.1 hιZ hιW hcomm θ
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · change (A.component κ).val.max =
      traceCutoff ιW PΓ (sourceKahlerFormOfBackground omegaY)
    rw [pullback_component_max omegaVZ hpt TZ κ (sourceKahlerFormOfBackground omegaVZ),
      traceCutoff_pullback hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ _
        (sourceKahlerFormOfBackground omegaX)]
    rfl
  · intro r hr hs
    have hτW := sliceTraceable_of_lt_traceCutoff hwdW (sourceKahlerFormOfBackground omegaY)
      (show r < traceCutoff ιW PΓ (sourceKahlerFormOfBackground omegaY) from hs)
    have hτZ : SliceTraceable ιZ Γ (sourceKahlerFormOfBackground omegaX) r :=
      (sliceTraceable_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ _ _ r).mp hτW
    have hL := component_slice_sourceIModel (A.changeRepresentative hcl) κ r hr
    have hspecW := traceSlice_spec hk omegaY omegaVW hιW PΓ r hτW
    have hspecZ := traceSlice_spec hk omegaX omegaVZ hιZ Γ r hτZ
    obtain ⟨-, ⟨κ', hρ⟩, -⟩ := SGPT.Trace.sourceTrace_modification_of_commuting hk hπ hpt omegaX
      omegaY omegaVZ omegaVW hιZ hιW hcomm hspecZ
    have he := pullback_slice_iEquivalent omegaX hπ Γ (sourceKahlerFormOfBackground omegaY) omegaX r
      hτW.1 hτZ.1
    have p1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaVW
      omegaVW hιW hspecW hρ ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1)
    have p2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaVW
      omegaVW hιW hρ hspecW ((sourceIOrder_iff_native he.2.1 he.2.2.1).mp he.2)
    have hqW := isQPSH_of_sourceTrace hιW hspecW
    have hqρ := isQPSH_of_sourceTrace hιW hρ
    have hWZ : sourceIEquivalent (ofFixedModel k VW) (traceSlice hk omegaY omegaVW hιW PΓ r hτW)
        (traceSlice hk omegaX omegaVZ hιZ Γ r hτZ ∘ pt) :=
      ⟨sourceIOrder_of_sourcePOrder hqW hqρ p1, sourceIOrder_of_sourcePOrder hqρ hqW p2⟩
    have hrZ : r < (TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.max := by
      have h0 : r < (A.component κ).val.max := hr
      exact h0.trans_eq (pullback_component_max omegaVZ hpt TZ κ _)
    obtain ⟨φ, hφ, hφE⟩ := TraceRes.exists_goodTraceSlice' hk omegaX omegaVZ hιZ hvolZ Γ
      (sourceKahlerFormOfBackground omegaVZ) r hτZ
    have hTZslice : (TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.potential ⟨r, hrZ⟩ =
        sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hιZ)
          (sourceKahlerFormOfBackground omegaVZ)) φ := by
      change traceComponentSlice hk omegaX omegaVZ hιZ Γ _ r _ = _
      exact traceComponentSlice_eq hk omegaX omegaVZ hιZ Γ _ r _ hφE
    have hZ : sourceIEquivalent (ofFixedModel k VZ) (traceSlice hk omegaX omegaVZ hιZ Γ r hτZ)
        ((TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.potential ⟨r, hrZ⟩) := by
      rw [hTZslice]
      exact sourceIEquivalent_trans (sourceIEquivalent_symm hφE)
        (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half hιZ _ hφ))
    have hZpt := (SGPT.PSH.ModificationOrders.sourceIEquivalent_modification_pullback_iff hpt
      hZ.1.1 hZ.1.2.1).mp hZ
    have hA0 : r < (A.component κ).val.max := hr
    have hAZ := pullback_slice_iEquivalent omegaVZ hpt TZ κ omegaVZ r hA0 hrZ
    have hAA := changeRepresentative_slice_iEquivalent hcl A κ r hA0 hr
    have hchain : sourceIEquivalent (ofFixedModel k VW)
        (traceSlice hk omegaY omegaVW hιW PΓ r hτW)
        (((A.changeRepresentative hcl).component κ).val.potential ⟨r, hr⟩) :=
      sourceIEquivalent_trans hWZ (sourceIEquivalent_trans hZpt
        (sourceIEquivalent_trans (sourceIEquivalent_symm hAZ) hAA))
    change _ = traceComponentSlice hk omegaY omegaVW hιW PΓ κ r hτW
    unfold traceComponentSlice
    rw [sourceIEnvelope_eq_of_equivalent hchain]
    exact hL.2

end SGPT.NAPotential.P5Wire
