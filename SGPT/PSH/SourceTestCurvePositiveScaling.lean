import SGPT.PSH.SourceIModelTestCurves
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra
import SGPT.Foundations.Analysis.Pending.ActualMixedMassPositiveScaling
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling
import Mathlib.Analysis.Convex.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

private def scaledParameter (Γ : SourceTestCurvePredata θ) {c : ℝ} (hc : 0 < c)
    (r : Iio (c * Γ.max)) : Iio Γ.max :=
  ⟨r.1 / c, by
    have hr : r.1 < c * Γ.max := r.2
    exact (div_lt_iff₀ hc).mpr (by nlinarith)⟩

private def scaledFamily (Γ : SourceTestCurvePredata θ) {c : ℝ} (hc : 0 < c)
    (r : Iio (c * Γ.max)) : M → EReal :=
  fun x => (c : EReal) * Γ.potential (scaledParameter Γ hc r) x

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem scaledNegativeTrace (Γ : SourceTestCurvePredata θ) {c : ℝ} (hc : 0 < c)
    (x : M) (r : ℝ) :
    sourceTestCurveNegativeTrace (c * Γ.max) (scaledFamily Γ hc) x r =
      (c : EReal) * sourceTestCurveNegativeTrace Γ.max Γ.potential x (r / c) := by
  have hi : r / c < Γ.max ↔ r < c * Γ.max := by
    simpa only [mul_comm] using (div_lt_iff₀ hc : r / c < Γ.max ↔ r < Γ.max * c)
  by_cases hr : r < c * Γ.max
  · simp only [sourceTestCurveNegativeTrace, dif_pos hr, dif_pos (hi.mpr hr),
      scaledFamily, scaledParameter, mul_neg]
  · simp only [sourceTestCurveNegativeTrace, dif_neg hr, dif_neg (mt hi.mp hr),
      EReal.coe_mul_top_of_pos hc]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem scaledTrace_convex (Γ : SourceTestCurvePredata θ) {c : ℝ} (hc : 0 < c)
    (x : M) : SGPT.Convex.IsConvex
      (sourceTestCurveNegativeTrace (c * Γ.max) (scaledFamily Γ hc) x) := by
  let L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := {
    toFun := fun p => (p.1 / c, p.2 / c)
    map_add' := by intro p q; ext <;> simp [add_div]
    map_smul' := by intro a p; ext <;> simp [mul_div_assoc] }
  have heq : SGPT.Convex.epigraph
      (sourceTestCurveNegativeTrace (c * Γ.max) (scaledFamily Γ hc) x) =
      L ⁻¹' SGPT.Convex.epigraph (sourceTestCurveNegativeTrace Γ.max Γ.potential x) := by
    ext p
    change sourceTestCurveNegativeTrace (c * Γ.max) (scaledFamily Γ hc) x p.1 ≤ (p.2 : EReal) ↔
      sourceTestCurveNegativeTrace Γ.max Γ.potential x (p.1 / c) ≤ ((p.2 / c : ℝ) : EReal)
    rw [scaledNegativeTrace Γ hc x p.1]
    have hh : (c : EReal) * ((p.2 / c : ℝ) : EReal) = (p.2 : EReal) := by
      rw [← EReal.coe_mul]
      congr 1
      field_simp
    rw [← hh]
    simpa only [sourcePositiveERealOrderIso, Equiv.coe_fn_mk] using
      ((sourcePositiveERealOrderIso c hc).map_rel_iff'
        (a := sourceTestCurveNegativeTrace Γ.max Γ.potential x (p.1 / c))
        (b := ((p.2 / c : ℝ) : EReal)))
  change Convex ℝ _
  rw [heq]
  exact (Γ.concave x).linear_preimage L

/-- Literal positive scaling in the actual coefficient-scaled background. -/
def SourceTestCurvePredata.positiveScale (Γ : SourceTestCurvePredata θ)
    {c : ℝ} (hc : 0 < c) :
    SourceTestCurvePredata (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) where
  max := c * Γ.max
  potential := scaledFamily Γ hc
  thetaPSH r := sourcePositiveScaling_thetaPSH (Γ.thetaPSH (scaledParameter Γ hc r)) hc
  antitone x := by
    intro r s hrs
    apply (sourcePositiveERealOrderIso c hc).monotone
    exact Γ.antitone x (div_le_div_of_nonneg_right (show r.1 ≤ s.1 from hrs) hc.le)
  concave := scaledTrace_convex Γ hc
  fixedPoint r := by
    rw [show scaledFamily Γ hc r = fun x => (c : EReal) * Γ.potential (scaledParameter Γ hc r) x from rfl,
      sourceOrdinaryEnvelope_positiveScaling _ hc, Γ.fixedPoint]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The printed actual real cutoff is multiplied by the same positive scalar. -/
theorem SourceTestCurvePredata.positiveScale_max (Γ : SourceTestCurvePredata θ)
    {c : ℝ} (hc : 0 < c) : (Γ.positiveScale hc).max = c * Γ.max := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual open slice is exactly c times the original slice at r/c. -/
theorem SourceTestCurvePredata.positiveScale_potential (Γ : SourceTestCurvePredata θ)
    {c : ℝ} (hc : 0 < c) (r : Iio (Γ.positiveScale hc).max) :
    (Γ.positiveScale hc).potential r =
      fun x => (c : EReal) * Γ.potential
        ⟨r.1 / c, by have hr : r.1 < c * Γ.max := r.2
                     exact (div_lt_iff₀ hc).mpr (by nlinarith)⟩ x := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Whole negative-trace covariance retains the top branch and all poles. -/
theorem SourceTestCurvePredata.positiveScale_negativeTrace (Γ : SourceTestCurvePredata θ)
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) :
    sourceTestCurveNegativeTrace (Γ.positiveScale hc).max (Γ.positiveScale hc).potential x r =
      (c : EReal) * sourceTestCurveNegativeTrace Γ.max Γ.potential x (r / c) :=
  scaledNegativeTrace Γ hc x r

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The literal original spatial usc limit scales, including infinite values. -/
theorem SourceTestCurvePredata.positiveScale_limit (Γ : SourceTestCurvePredata θ)
    {c : ℝ} (hc : 0 < c) :
    sourceTestCurveLimit (Γ.positiveScale hc) =
      fun x => (c : EReal) * sourceTestCurveLimit Γ x := by
  have hraw : (fun x => ⨆ r, (Γ.positiveScale hc).potential r x) =
      fun x => (c : EReal) * ⨆ r, Γ.potential r x := by
    funext x
    let e := sourcePositiveERealOrderIso c hc
    change (⨆ r, e (Γ.potential (scaledParameter Γ hc r) x)) = e (⨆ r, Γ.potential r x)
    rw [_root_.map_iSup]
    apply le_antisymm
    · exact iSup_le fun r => le_iSup (fun s => e (Γ.potential s x)) (scaledParameter Γ hc r)
    · apply iSup_le
      intro s
      let r : Iio (c * Γ.max) := ⟨c * s.1, mul_lt_mul_of_pos_left s.2 hc⟩
      have hr : scaledParameter Γ hc r = s := by
        apply Subtype.ext
        change c * s.1 / c = s.1
        field_simp
      simpa only [hr] using
        (le_iSup (fun r => e (Γ.potential (scaledParameter Γ hc r) x)) r)
  change uscRegularization _ = _
  rw [hraw, sourcePositiveScaling_uscRegularization c hc]
  rfl

omit [ConnectedSpace M] in
/-- Actual diagonal non-pluripolar mass homogeneity, including dimension zero. -/
theorem sourcePositiveScaling_actualMass {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {c : ℝ} (hc : 0 < c) :
    sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (fun x => (c : EReal) * u x) (sourcePositiveScaling_thetaPSH hu hc) univ =
      ENNReal.ofReal (c ^ n) * sourcePotentialNonPluripolarMeasure θ u hu univ := by
  rw [← sourceMixedNonPluripolarMass_diagonal, ← sourceMixedNonPluripolarMass_diagonal θ u hu]
  rw [sourceMixedNonPluripolarMass_eq_native, sourceMixedNonPluripolarMass_eq_native]
  simp only [sourceNativeAtlasForm_roundTrip]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (ActualMixedMassPositiveScaling.globalMixedMass_positive_smul
      (θ := fun _ : Fin n => atlasClosedFormToNative θ)
      (u := fun _ : Fin n => u)
      (fun _ => (isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      (c := fun _ : Fin n => c) (fun _ => hc))

omit [ConnectedSpace M] in
/-- Actual ordinary positive models scale without an extra mass or model premise. -/
theorem sourceModelPotential_positiveScale {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) {c : ℝ} (hc : 0 < c) :
    SourceModelPotential (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (fun x => (c : EReal) * φ x) := by
  refine ⟨sourcePositiveScaling_thetaPSH hφ.thetaPSH hc, ?_, ?_⟩
  · rw [sourceOrdinaryEnvelope_positiveScaling _ hc, ← hφ.choose_spec.1]
  · rw [sourcePositiveScaling_actualMass hφ.thetaPSH hc]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hc n), hφ.choose_spec.2⟩

/-- The actual positive-mass limit produces the full positively scaled test curve. -/
def SourceTestCurve.positiveScale (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    SourceTestCurve (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) where
  toSourceTestCurvePredata := Γ.toSourceTestCurvePredata.positiveScale hc
  positiveLimitMass := by
    have h := sourcePositiveScaling_actualMass Γ.toSourceTestCurvePredata.limit_thetaPSH hc
    have hp : 0 < ENNReal.ofReal (c ^ n) *
        sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata)
          Γ.toSourceTestCurvePredata.limit_thetaPSH univ :=
      ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hc n), Γ.positiveLimitMass⟩
    rw [← h] at hp
    simpa only [Γ.toSourceTestCurvePredata.positiveScale_limit hc] using hp

omit [ConnectedSpace M] in
/-- Literal cutoff reader for the full scaled object. -/
theorem SourceTestCurve.positiveScale_max (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    (Γ.positiveScale hc).max = c * Γ.max := rfl

omit [ConnectedSpace M] in
/-- Literal slice reader for the full scaled object. -/
theorem SourceTestCurve.positiveScale_potential (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c)
    (r : Iio (Γ.positiveScale hc).max) :
    (Γ.positiveScale hc).potential r =
      fun x => (c : EReal) * Γ.potential
        ⟨r.1 / c, by have hr : r.1 < c * Γ.max := r.2
                     exact (div_lt_iff₀ hc).mpr (by nlinarith)⟩ x := rfl

omit [ConnectedSpace M] in
/-- Literal actual limit reader for the full scaled object. -/
theorem SourceTestCurve.positiveScale_limit (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    sourceTestCurveLimit (Γ.positiveScale hc).toSourceTestCurvePredata =
      fun x => (c : EReal) * sourceTestCurveLimit Γ.toSourceTestCurvePredata x :=
  Γ.toSourceTestCurvePredata.positiveScale_limit hc

omit [ConnectedSpace M] in
/-- Actual mass of the produced limit, including dimension zero. -/
theorem SourceTestCurve.positiveScale_limit_mass (Γ : SourceTestCurve θ)
    {c : ℝ} (hc : 0 < c) :
    sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (sourceTestCurveLimit (Γ.positiveScale hc).toSourceTestCurvePredata)
      (Γ.positiveScale hc).toSourceTestCurvePredata.limit_thetaPSH univ =
      ENNReal.ofReal (c ^ n) * sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata)
        Γ.toSourceTestCurvePredata.limit_thetaPSH univ := by
  have h := sourcePositiveScaling_actualMass Γ.toSourceTestCurvePredata.limit_thetaPSH hc
  simpa only [Γ.positiveScale_limit hc] using h

omit [ConnectedSpace M] in
/-- Actual basedness is preserved with the genuinely produced scaled positive model. -/
theorem SourceTestCurve.positiveScale_based {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) {c : ℝ} (hc : 0 < c) :
    Γ.positiveScale hc ∈ SourceTestCurvesBased
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (fun x => (c : EReal) * φ x) (sourceModelPotential_positiveScale hφ hc) := by
  change sourceTestCurveLimit _ = _
  rw [Γ.positiveScale_limit hc, show sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ from hΓ]

/-- Every actual native I-model slice remains genuinely I-model after scaling. -/
theorem SourceTestCurve.positiveScale_iModel (Γ : SourceTestCurve θ)
    (hI : SourceTestCurveIsIModel Γ) {c : ℝ} (hc : 0 < c) :
    SourceTestCurveIsIModel (Γ.positiveScale hc) := by
  intro r
  let s : Iio Γ.max := scaledParameter Γ.toSourceTestCurvePredata hc r
  have hs := hI s
  have henv := ActualIEnvelopePositiveScaling.iSingularityEnvelope_smul
    (atlasClosedFormToNative θ) hs.1 hc
  change IEnvelope.IsIModelPotential
    (atlasClosedFormToNative (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))).val
      (fun x => (c : EReal) * Γ.potential s x)
  rw [sourceNativeAtlasForm_roundTrip]
  refine ⟨RestrictedApproximantComparison.isThetaPshPotential_smul hs.1 hc, ?_⟩
  rw [henv, ← hs.2]

/-- Actual based I-model membership with the same produced scaled model. -/
theorem SourceTestCurve.positiveScale_iModel_based {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceIModelTestCurves θ φ hφ) {c : ℝ} (hc : 0 < c) :
    Γ.positiveScale hc ∈ SourceIModelTestCurves
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
      (fun x => (c : EReal) * φ x) (sourceModelPotential_positiveScale hφ hc) :=
  ⟨SourceTestCurve.positiveScale_based hφ hΓ.1 hc, Γ.positiveScale_iModel hΓ.2 hc⟩

/-- The original union over all positive model bases is preserved. -/
theorem SourceTestCurve.positiveScale_iModel_positive (omega : KahlerBackground n M)
    {Γ : SourceTestCurve θ} (hΓ : Γ ∈ SourceIModelTestCurvesPositive θ)
    {c : ℝ} (hc : 0 < c) :
    Γ.positiveScale hc ∈ SourceIModelTestCurvesPositive
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) := by
  apply (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
  exact Γ.positiveScale_iModel
    ((sourceIModelTestCurvesPositive_iff_slices omega Γ).mp hΓ) hc

/-- Whole original positive-scaling proposition, including its I-model clause. -/
theorem source_test_curve_positive_scaling_whole (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    Γ.positiveScale hc ∈ SourceTestCurvesPositive
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) ∧
      (Γ ∈ SourceIModelTestCurvesPositive θ →
        Γ.positiveScale hc ∈ SourceIModelTestCurvesPositive
          (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))) ∧
      sourceTestCurveLimit (Γ.positiveScale hc).toSourceTestCurvePredata =
        fun x => (c : EReal) * sourceTestCurveLimit Γ.toSourceTestCurvePredata x :=
  ⟨(Γ.positiveScale hc).mem_positive omega,
    fun hI => SourceTestCurve.positiveScale_iModel_positive omega hI hc,
    Γ.positiveScale_limit hc⟩

end SGPT.PSH.VariableComplexAtlas
