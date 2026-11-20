import SGPT.Checks.Comparison.TraceBirationalCompositeResolution
import SGPT.NAPotential.P5WireNATracePullback

/-! Original L655 on the LITERAL internally produced strict transform.
Compatible native resolution and map are produced internally on SAME model.
Original source carrier hwd/cutoff and ACTUAL NA trace family pullback.
No normalization/model/dictionary certificate or Hironaka development.
Blueprint: trace-birational-strict-transform.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.Trace.Trace2Resolution BirationalGeometry SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open AnalyticModificationLocalDiscrepancy SGPT.NAPotential.RIsoB
open SGPT.NAPotential.NATrace SGPT.NAPotential.TraceRes
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n X] [IsComplexManifold n Y]
  [CompactSpace X] [ConnectedSpace X] [CompactSpace Y] [ConnectedSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
variable (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

include omegaY in
/-- Original carrier hwd on literal strict transform is equivalent to
original downstairs condition; all compatible geometry is INTERNAL. -/
theorem originalStrictTransform_traceWellDefined_iff
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π) (Γ : SourceNAPotential θ) :
    carrierTraceWellDefined (originalStrictTransform hπ Z hZ) (sourceNAPullback omegaX hπ Γ) ↔
      carrierTraceWellDefined Z Γ := by
  let W := originalStrictTransform hπ Z hZ
  let RW := resolutionTraceTarget W omegaY
  let RZ := compositeResolutionTarget hπ Z hZ RW
  have hid : IsAnalyticModification (n := W.dim) (id : RW.V → RW.V) :=
    SGPT.Okounkov.isAnalyticModification_identity
  exact (traceWellDefined_resolution_iff RW (sourceNAPullback omegaX hπ Γ)).symm.trans
    ((traceWellDefined_pullback_iff W.dim_le omegaX omegaY RW.kahler hπ hid
      (hπ.1.comp RW.contMDiff) (fun _ => rfl) Γ).trans (traceWellDefined_resolution_iff RZ Γ))

include omegaY in
/-- Literal original carrier cutoffs agree at EVERY original index. -/
theorem originalStrictTransform_traceCutoff_pullback
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π) (Γ : SourceNAPotential θ)
    (κY : SourceKahlerForm n Y) (κX : SourceKahlerForm n X) :
    carrierTraceCutoff (originalStrictTransform hπ Z hZ) (sourceNAPullback omegaX hπ Γ) κY =
      carrierTraceCutoff Z Γ κX := by
  let W := originalStrictTransform hπ Z hZ
  let RW := resolutionTraceTarget W omegaY
  let RZ := compositeResolutionTarget hπ Z hZ RW
  have hid : IsAnalyticModification (n := W.dim) (id : RW.V → RW.V) :=
    SGPT.Okounkov.isAnalyticModification_identity
  exact (traceCutoff_resolution_eq RW (sourceNAPullback omegaX hπ Γ) κY).symm.trans
    ((traceCutoff_pullback W.dim_le omegaX omegaY RW.kahler hπ hid
      (hπ.1.comp RW.contMDiff) (fun _ => rfl) Γ κY κX).trans (traceCutoff_resolution_eq RZ Γ κX))

/-- ACTUAL original NA object equality for EVERY actual upstairs target.
Downstairs target is ACTUALLY constructed on the SAME model and map=id,
so no compatible-target/map/hvol/dimension certificate is a premise. -/
theorem originalStrictTransform_family_pullback
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Z Γ) :
    let W := originalStrictTransform hπ Z hZ
    let PΓ := sourceNAPullback omegaX hπ Γ
    let hwdW := (originalStrictTransform_traceWellDefined_iff hπ omegaX omegaY Z hZ Γ).mpr hwd
    ∀ RW : ResolutionTarget W,
    let RZ := compositeResolutionTarget hπ Z hZ RW
    let hid := SGPT.Okounkov.isAnalyticModification_identity (n := W.dim) (X := RW.V)
    (sourceNAPullback RW.kahler hid (resolutionTraceFamily Z omegaX Γ hwd RZ)).changeRepresentative
      (pullback_comm_class_eq hπ.1 hid.1 (hπ.1.comp RW.contMDiff) RW.contMDiff (fun _ => rfl) θ) =
        resolutionTraceFamily W omegaY PΓ hwdW RW := by
  dsimp only
  intro RW
  let RZ := compositeResolutionTarget hπ Z hZ RW
  have hid := SGPT.Okounkov.isAnalyticModification_identity
    (n := (originalStrictTransform hπ Z hZ).dim) (X := RW.V)
  exact SGPT.NAPotential.P5Wire.naTraceRes_pullback (originalStrictTransform hπ Z hZ).dim_le
    omegaX omegaY RW.kahler RW.kahler hπ hid (hπ.1.comp RW.contMDiff)
    (SGPT.Trace.RIsoB.pullbackKahlerVolumePos RZ) RW.contMDiff
    (SGPT.Trace.RIsoB.pullbackKahlerVolumePos RW) (fun _ => rfl) Γ
    (carrierTraceWellDefined_on Z Γ hwd RZ)

/-- Literal actual divisorial-function consequence on the internally
constructed SAME resolving model/map, every real weight and trivial. -/
theorem originalStrictTransform_family_divisorial_pullback
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Z Γ) :
    let W := originalStrictTransform hπ Z hZ
    let PΓ := sourceNAPullback omegaX hπ Γ
    let hwdW := (originalStrictTransform_traceWellDefined_iff hπ omegaX omegaY Z hZ Γ).mpr hwd
    ∀ (RW : ResolutionTarget W) (κZ κW : SourceKahlerForm W.dim RW.V),
    let RZ := compositeResolutionTarget hπ Z hZ RW
    let hid := SGPT.Okounkov.isAnalyticModification_identity (n := W.dim) (X := RW.V)
    nativeDivisorialFunction (resolutionTraceFamily W omegaY PΓ hwdW RW) κW =
      fun v => nativeDivisorialFunction (k := W.dim) (V := RW.V)
        (resolutionTraceFamily Z omegaX Γ hwd RZ) κZ (nativeDivisorialPush hid v) := by
  dsimp only
  intro RW κZ κW
  let RZ := compositeResolutionTarget hπ Z hZ RW
  have hid := SGPT.Okounkov.isAnalyticModification_identity
    (n := (originalStrictTransform hπ Z hZ).dim) (X := RW.V)
  have he := originalStrictTransform_family_pullback hπ omegaX omegaY Z hZ Γ hwd RW
  have hr := nativeDivisorialFunction_changeRepresentative
    (pullback_comm_class_eq hπ.1 hid.1 (hπ.1.comp RW.contMDiff) RW.contMDiff (fun _ => rfl) θ)
    (sourceNAPullback RW.kahler hid (resolutionTraceFamily Z omegaX Γ hwd RZ)) κW
  rw [he] at hr
  exact hr.trans (nativeDivisorialFunction_pullback RW.kahler hid
    (resolutionTraceFamily Z omegaX Γ hwd RZ) κW κZ)

omit [ConnectedSpace Y] in
/-- CLOSED original trace clause of L655. Original strict transform,
upstairs connectedness, all compatible models/maps and faithful whole
family data are INTERNAL outputs. No normalization/model/dictionary input. -/
theorem source_trace_birational_pullback
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Z Γ) :
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    let W := originalStrictTransform hπ Z hZ
    let PΓ := sourceNAPullback omegaX hπ Γ
    W.carrier = strictTransform n π Z.carrier ∧ W.dim = Z.dim ∧ π '' W.carrier = Z.carrier ∧
    ∃ hwdW : carrierTraceWellDefined W PΓ,
      IsOriginalResolutionTraceFamily Z Γ (resolutionTraceFamily Z omegaX Γ hwd) ∧
      IsOriginalResolutionTraceFamily W PΓ (resolutionTraceFamily W omegaY PΓ hwdW) ∧
      (∀ (κY : SourceKahlerForm n Y) (κX : SourceKahlerForm n X),
        carrierTraceCutoff W PΓ κY = carrierTraceCutoff Z Γ κX) ∧
      (∀ RW : ResolutionTarget W,
        let RZ := compositeResolutionTarget hπ Z hZ RW
        let hid := SGPT.Okounkov.isAnalyticModification_identity (n := W.dim) (X := RW.V)
        (sourceNAPullback RW.kahler hid (resolutionTraceFamily Z omegaX Γ hwd RZ)).changeRepresentative
          (pullback_comm_class_eq hπ.1 hid.1 (hπ.1.comp RW.contMDiff) RW.contMDiff (fun _ => rfl) θ) =
            resolutionTraceFamily W omegaY PΓ hwdW RW) ∧
      (∀ (RW : ResolutionTarget W) (κZ κW : SourceKahlerForm W.dim RW.V),
        let RZ := compositeResolutionTarget hπ Z hZ RW
        let hid := SGPT.Okounkov.isAnalyticModification_identity (n := W.dim) (X := RW.V)
        nativeDivisorialFunction (resolutionTraceFamily W omegaY PΓ hwdW RW) κW =
          fun v => nativeDivisorialFunction (k := W.dim) (V := RW.V)
            (resolutionTraceFamily Z omegaX Γ hwd RZ) κZ (nativeDivisorialPush hid v)) := by
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  dsimp only
  let W := originalStrictTransform hπ Z hZ
  let PΓ := sourceNAPullback omegaX hπ Γ
  have hwdW := (originalStrictTransform_traceWellDefined_iff hπ omegaX omegaY Z hZ Γ).mpr hwd
  exact ⟨originalStrictTransform_carrier hπ Z hZ,originalStrictTransform_dim hπ Z hZ,
    originalStrictTransform_image hπ Z hZ,hwdW,source_naTrace_family Z omegaX Γ hwd,
    source_naTrace_family W omegaY PΓ hwdW,
    originalStrictTransform_traceCutoff_pullback hπ omegaX omegaY Z hZ Γ,
    originalStrictTransform_family_pullback hπ omegaX omegaY Z hZ Γ hwd,
    originalStrictTransform_family_divisorial_pullback hπ omegaX omegaY Z hZ Γ hwd⟩

end SGPT.NAPotential.TraceComparison
