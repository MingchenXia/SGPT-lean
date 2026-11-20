import SGPT.Checks.Comparison.TracePrimeModificationTransport
import SGPT.NAPotential.RIsoBTraceModification

/-! The original NA pullback has the SAME actual divisorial function
under actual native-prime composition. No reader certificate.
Blueprint: trace-resolution-divisor-transport.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open AnalyticModificationLocalDiscrepancy SGPT.NAPotential.RIsoB
open scoped Topology Manifold ContDiff ENNReal

variable {k : ℕ} {V W : Type u} [TopologicalSpace V] [TopologicalSpace W]
  [ChartedSpace (ComplexModel k) V] [ChartedSpace (ComplexModel k) W]
  [IsComplexManifold k V] [IsComplexManifold k W]
  [CompactSpace V] [ConnectedSpace V] [CompactSpace W] [ConnectedSpace W]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  (omegaV : KahlerBackground k V)
  {π : W → V} (hπ : IsAnalyticModification (n := k) π)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k V)}

/-- Literal original slice reader of actual NA pullback equals the
original slice reader on the SAME actually composed prime. -/
theorem naPullback_slice_primePush (Δ : SourceNAPotential θ)
    (κW : SourceKahlerForm k W) (s : ℝ)
    (hs : s < ((sourceNAPullback omegaV hπ Δ).component κW).val.max)
    (hsV : s < (Δ.component (sourceKahlerFormOfBackground omegaV)).val.max)
    (p : PrimePresentation k W) :
    presentationReader (((sourceNAPullback omegaV hπ Δ).component κW).val.potential ⟨s,hs⟩) p =
      presentationReader ((Δ.component (sourceKahlerFormOfBackground omegaV)).val.potential ⟨s,hsV⟩)
        (primePush hπ p) := by
  have hI := pullback_slice_iEquivalent omegaV hπ Δ κW omegaV s hs hsV
  have hR := (sourceIEquivalent_iff_directPrimeEquality hI.1.1 hI.1.2.1).mp hI
    (Quot.mk commonResolutionRelation p)
  rw [directSourceQPSHReader_mk, directSourceQPSHReader_mk] at hR
  exact hR.trans (presentationReader_primePush hπ _ p).symm

/-- Every real-weight ORIGINAL NA transform commutes with the actual
modification pullback and actual same-divisor prime composition. -/
theorem naDivisorialTransform_pullback_primePush (Δ : SourceNAPotential θ)
    (κW : SourceKahlerForm k W) (κV : SourceKahlerForm k V)
    (p : PrimePresentation k W) (c : ℝ) :
    BJPrep.naDivisorialTransform (sourceNAPullback omegaV hπ Δ) κW p c =
      BJPrep.naDivisorialTransform Δ κV (primePush hπ p) c := by
  have hmax := pullback_component_max omegaV hπ Δ κW
    (sourceKahlerFormOfBackground omegaV)
  have hmain : BJPrep.naDivisorialTransform (sourceNAPullback omegaV hπ Δ) κW p c =
      BJPrep.naDivisorialTransform Δ (sourceKahlerFormOfBackground omegaV) (primePush hπ p) c := by
    unfold BJPrep.naDivisorialTransform BJPrep.curveDivisorialTransform
    apply le_antisymm
    · refine iSup_le fun s => iSup_le fun hs => ?_
      have hsV := hmax ▸ hs
      rw [naPullback_slice_primePush omegaV hπ Δ κW s hs hsV p]
      exact le_iSup_of_le s (le_iSup_of_le hsV le_rfl)
    · refine iSup_le fun s => iSup_le fun hsV => ?_
      have hs := hmax.symm ▸ hsV
      rw [← naPullback_slice_primePush omegaV hπ Δ κW s hs hsV p]
      exact le_iSup_of_le s (le_iSup_of_le hs le_rfl)
  exact hmain.trans (BJPrep.naDivisorialTransform_independent Δ
    (sourceKahlerFormOfBackground omegaV) κV (primePush hπ p) c)

/-- Equality of ACTUAL FUNCTIONS on weighted original prime classes and
the trivial point; source/target dimensions zero are retained. -/
theorem nativeDivisorialFunction_pullback (Δ : SourceNAPotential θ)
    (κW : SourceKahlerForm k W) (κV : SourceKahlerForm k V) :
    nativeDivisorialFunction (sourceNAPullback omegaV hπ Δ) κW =
      fun v => nativeDivisorialFunction Δ κV (nativeDivisorialPush hπ v) := by
  funext v
  cases v with
  | none =>
      change (((sourceNAPullback omegaV hπ Δ).component κW).val.max : EReal) =
        ((Δ.component κV).val.max : EReal)
      exact congrArg (fun x : ℝ => (x : EReal)) (pullback_component_max omegaV hπ Δ κW κV)
  | some cp =>
      rcases cp with ⟨c,p⟩
      refine Quot.inductionOn p fun p => ?_
      change directNAPrimeValue (sourceNAPullback omegaV hπ Δ) κW
          (Quot.mk commonResolutionRelation p) c.val =
        directNAPrimeValue Δ κV (Quot.mk commonResolutionRelation (primePush hπ p)) c.val
      rw [directNAPrimeValue_mk, directNAPrimeValue_mk]
      exact naDivisorialTransform_pullback_primePush omegaV hπ Δ κW κV p c.val

section Representative
variable {η : AtlasClosedRealOneOneForm (ofFixedModel k V)}

omit [TopologicalSpace W] [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]
  [CompactSpace W] [ConnectedSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Actual original change of representative leaves the unchanged
native divisorial transform fixed; no reader identity premise. -/
theorem naDivisorialTransform_changeRepresentative
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Δ : SourceNAPotential θ) (κ : SourceKahlerForm k V) (p : PrimePresentation k V) (c : ℝ) :
    BJPrep.naDivisorialTransform (Δ.changeRepresentative hc) κ p c =
      BJPrep.naDivisorialTransform Δ κ p c := by
  unfold BJPrep.naDivisorialTransform
  apply BJPrep.curveDivisorialTransform_congr
    ((Δ.changeRepresentative hc).component κ).val.toSourceTestCurvePredata
    (Δ.component κ).val.toSourceTestCurvePredata p rfl _ c
  intro s hs' hs
  have hI := changeRepresentative_slice_iEquivalent hc Δ κ s hs hs'
  have hR := (sourceIEquivalent_iff_directPrimeEquality hI.1.1 hI.1.2.1).mp hI
    (Quot.mk commonResolutionRelation p)
  rw [directSourceQPSHReader_mk, directSourceQPSHReader_mk] at hR
  exact hR.symm

omit [TopologicalSpace W] [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]
  [CompactSpace W] [ConnectedSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Actual original representative change preserves the actual FUNCTION
on every original weighted prime class and the trivial point. -/
theorem nativeDivisorialFunction_changeRepresentative
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Δ : SourceNAPotential θ) (κ : SourceKahlerForm k V) :
    nativeDivisorialFunction (Δ.changeRepresentative hc) κ = nativeDivisorialFunction Δ κ := by
  funext v
  cases v with
  | none => rfl
  | some cp =>
      rcases cp with ⟨c,p⟩
      refine Quot.inductionOn p fun p => ?_
      change directNAPrimeValue (Δ.changeRepresentative hc) κ (Quot.mk commonResolutionRelation p) c.val =
        directNAPrimeValue Δ κ (Quot.mk commonResolutionRelation p) c.val
      rw [directNAPrimeValue_mk, directNAPrimeValue_mk]
      exact naDivisorialTransform_changeRepresentative hc Δ κ p c.val
end Representative

end SGPT.NAPotential.TraceComparison
