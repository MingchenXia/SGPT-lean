import SGPT.PSH.SourceTestCurveGeneralSup
import SGPT.PSH.SourceTestCurveJoinProjection

/-! # Projection of the original arbitrary-family test-curve supremum

The actual finite-join homomorphism and the unchanged main increasing
compatibility identify the same original general supremum. No new generic
envelope or model-net producer is required.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual finite original join commutes with every semipositive projection. -/
theorem SourceTestCurve.finiteJoin_semipositiveProjection {I : Type*}
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty) :
    (SourceTestCurve.finiteJoin omega Γ s hs).semipositiveProjection omega η hη =
      SourceTestCurve.finiteJoin omega (fun i => (Γ i).semipositiveProjection omega η hη)
        s hs := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  let : SemilatticeSup (SourceTestCurve (θ.add η)) :=
    sourceTestCurveSemilatticeSup omega (θ.add η)
  exact Finset.apply_sup'_eq_sup'_comp hs
    (fun G : SourceTestCurve θ => G.semipositiveProjection omega η hη)
    (source_test_curve_join_semipositive_projection_compatible omega η hη)

/-- Whole original lma:testcursupcompatible, including zero semipositive addition. -/
theorem source_test_curve_generalSup_semipositive_projection_compatible
    {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.generalSup omega Γ hb).semipositiveProjection omega η hη =
      SourceTestCurve.generalSup omega (fun i => (Γ i).semipositiveProjection omega η hη)
        (sourceTestCurveSemipositiveProjectedFamily_bddAbove omega η hη Γ hb) := by
  have hf : (fun F : SourceTestCurveFiniteIndex I =>
      (sourceTestCurveFiniteJoinFamily omega Γ F).semipositiveProjection omega η hη) =
      sourceTestCurveFiniteJoinFamily omega (fun i => (Γ i).semipositiveProjection omega η hη) := by
    funext F
    exact SourceTestCurve.finiteJoin_semipositiveProjection omega η hη Γ F.1 F.2
  unfold SourceTestCurve.generalSup
  rw [source_test_curve_increasingSup_semipositive_projection_compatible]
  simp only [hf]

/-- The exact original Kähler background projection on the actual general supremum. -/
theorem source_test_curve_generalSup_background_projection_compatible
    {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.generalSup omega Γ hb).backgroundProjection omega =
      SourceTestCurve.generalSup omega (fun i => (Γ i).backgroundProjection omega) hb := by
  have hω : (atlasClosedFormToNative (nativeClosedFormToAtlas omega.form)).val.IsSemipositive := by
    simpa only [sourceNativeAtlasForm_roundTrip] using omega.isSemipositive
  have h := source_test_curve_generalSup_semipositive_projection_compatible omega
    (nativeClosedFormToAtlas omega.form) hω Γ hb
  change @Eq (SourceTestCurve (θ.add (nativeClosedFormToAtlas omega.form))) _ _
  simpa only [SourceTestCurve.semipositiveProjection_kahler_eq_backgroundProjection,
    sourceTestCurveEnlargedBackground] using h

end SGPT.PSH.VariableComplexAtlas
