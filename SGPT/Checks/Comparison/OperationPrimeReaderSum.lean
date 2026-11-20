import SGPT.PSH.SourceMixedIVolumeSemicontinuityTails
import SGPT.PSH.SourceTestCurveSum
import SGPT.Okounkov.FlagLelong

/-! Actual original generic-prime readers of the literal raw convolution.
Blueprint: operation-sum-prime-readers.tex. No supplied reader identity. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open Set Filter SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Additivity of the SAME actual original source prime reader, with
nondegenerate actual pullbacks and common generic minima produced internally. -/
theorem presentationReader_add {u v : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u)
    (hv : (ofFixedModel n X).IsThetaPSH σ v) (p : PrimePresentation n X) :
    presentationReader (fun x => u x + v x) p =
      presentationReader u p + presentationReader v p := by
  have huY := hu.comp_native_analyticModification p.modification
  have hvY := hv.comp_native_analyticModification p.modification
  have h := SGPT.Okounkov.sourceGeneric_subtype_add_eq p.smooth
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp huY).quasiPshPotential
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hvY).quasiPshPotential
  simp_rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf] at h
  simpa only [presentationReader,sourceGenericLelong,sourceLelong_ofFixedModel_eq,
    Function.comp_def] using h

omit [BorelSpace X] in
/-- Actual original all-real raw convolution has the EXACT infimum
formula on the SAME nonempty closed interval, retaining BOTH actual cutoff slices. -/
theorem presentationReader_rawSum (C : SourceTestCurve θ) (D : SourceTestCurve σ)
    {τ : ℝ} (hτ : τ ≤ C.max + D.max) (p : PrimePresentation n X) :
    presentationReader (sourceTestCurveRawSum
      C.toSourceTestCurvePredata D.toSourceTestCurvePredata τ) p =
      ⨅ r : Icc (τ-D.max) C.max,
        presentationReader (sourceTestCurveAt C.toSourceTestCurvePredata r.1) p +
          presentationReader (sourceTestCurveAt D.toSourceTestCurvePredata (τ-r.1)) p := by
  let K := Icc (τ-D.max) C.max
  let : Nonempty K := ⟨⟨C.max, by constructor; linarith; exact le_rfl⟩⟩
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let F : K → X → EReal := fun r x =>
    sourceTestCurveAt C.toSourceTestCurvePredata r.1 x +
      sourceTestCurveAt D.toSourceTestCurvePredata (τ-r.1) x
  have hC (r : K) : (ofFixedModel n X).IsThetaPSH θ
      (sourceTestCurveAt C.toSourceTestCurvePredata r.1) :=
    (source_test_curve_extension_whole C.toSourceTestCurvePredata).2.2.2 r.1 r.2.2
  have hD (r : K) : (ofFixedModel n X).IsThetaPSH σ
      (sourceTestCurveAt D.toSourceTestCurvePredata (τ-r.1)) := by
    apply (source_test_curve_extension_whole D.toSourceTestCurvePredata).2.2.2
    have hr := r.2.1
    linarith
  have hF (r : K) : (ofFixedModel n X).IsThetaPSH T (F r) :=
    sourceIndependentSum_thetaPSH (hC r) (hD r)
  have hB (r : K) (x : X) : F r x ≤ (0 : ℝ) :=
    add_nonpos (C.toSourceTestCurvePredata.at_le_zero r.1 x)
      (D.toSourceTestCurvePredata.at_le_zero (τ-r.1) x)
  have heq : (fun x => ⨆ r : K, F r x) = sourceTestCurveRawSum
      C.toSourceTestCurvePredata D.toSourceTestCurvePredata τ :=
    (sourceTestCurveRawSum_eq_compact C.toSourceTestCurvePredata D.toSourceTestCurvePredata τ).symm
  have hraw := sourceTestCurveRawSum_thetaPSH
    C.toSourceTestCurvePredata D.toSourceTestCurvePredata hτ
  have husc : UpperSemicontinuous (sourceTestCurveRawSum
      C.toSourceTestCurvePredata D.toSourceTestCurvePredata τ) :=
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hraw).1.quasiPlurisubharmonic.upperSemicontinuous
  have hUF : uscSup F = sourceTestCurveRawSum
      C.toSourceTestCurvePredata D.toSourceTestCurvePredata τ := by
    unfold uscSup
    rw [heq,uscRegularization_eq husc]
  rw [← hUF,SGPT.PSH.SourceUSCTailsDraft.presentationReader_uscSup_eq_iInf T F hF hB p]
  apply iInf_congr
  intro r
  exact presentationReader_add (hC r) (hD r) p

end SGPT.NAPotential.OperationComparison
