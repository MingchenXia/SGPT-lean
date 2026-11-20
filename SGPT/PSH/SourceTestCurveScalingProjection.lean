import SGPT.PSH.SourceTestCurvePositiveScaling
import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The entire actual atlas form, not only its native coefficients, is retained. -/
theorem sourceAtlasNativeForm_roundTrip (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    nativeClosedFormToAtlas (atlasClosedFormToNative θ) = θ := by
  cases θ
  rfl

/-- Equality elimination transports the SAME actual original curve object. -/
def SourceTestCurve.castBackground (Γ : SourceTestCurve θ) (h : θ = σ) : SourceTestCurve σ :=
  h ▸ Γ

omit [BorelSpace M] [ConnectedSpace M] in
/-- Exact real cutoff survives actual background identification. -/
theorem SourceTestCurve.castBackground_max (Γ : SourceTestCurve θ) (h : θ = σ) :
    (Γ.castBackground h).max = Γ.max := by
  cases h
  rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every actual original slice function survives background identification. -/
theorem SourceTestCurve.castBackground_potential (Γ : SourceTestCurve θ) (h : θ = σ)
    (r : ℝ) (hr : r < Γ.max) (hs : r < (Γ.castBackground h).max) :
    (Γ.castBackground h).potential ⟨r,hs⟩ = Γ.potential ⟨r,hr⟩ := by
  cases h
  rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The TWO actual scaled/enlarged atlas backgrounds are equal as ENTIRE forms. -/
theorem sourceScaledProjectionBackground_eq (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {c : ℝ} (hc : 0 < c) :
    sourceTestCurveEnlargedBackground (KahlerBackground.smul hc omega)
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) =
      nativeClosedFormToAtlas (c • atlasClosedFormToNative (sourceTestCurveEnlargedBackground omega θ)) := by
  apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
  simp only [sourceTestCurveEnlargedBackground_native, sourceNativeAtlasForm_roundTrip,
    KahlerBackground.smul_form, smul_add]

/-- WHOLE original scaling/projection lemma, as equality of ACTUAL original curves. -/
theorem source_test_curve_scaling_projection_compatible (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    ((Γ.positiveScale hc).backgroundProjection (KahlerBackground.smul hc omega)).castBackground
        (sourceScaledProjectionBackground_eq omega θ hc) =
      (Γ.backgroundProjection omega).positiveScale hc := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.backgroundProjection_max,
      SourceTestCurve.positiveScale_max]
  · intro r hr hs
    have hrl : r < ((Γ.positiveScale hc).backgroundProjection (KahlerBackground.smul hc omega)).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr]
    change r < c * Γ.max at hs
    have hsrc : r / c < Γ.max := (div_lt_iff₀ hc).mpr (by nlinarith)
    change sourceSingularityEnvelope
      (sourceTestCurveEnlargedBackground (KahlerBackground.smul hc omega)
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)))
      (fun x => (c : EReal) * Γ.potential ⟨r/c,hsrc⟩ x) =
      fun x => (c : EReal) * sourceSingularityEnvelope
        (sourceTestCurveEnlargedBackground omega θ) (Γ.potential ⟨r/c,hsrc⟩) x
    rw [sourceScaledProjectionBackground_eq omega θ hc, sourceOrdinaryEnvelope_positiveScaling _ hc]

end SGPT.PSH.VariableComplexAtlas
