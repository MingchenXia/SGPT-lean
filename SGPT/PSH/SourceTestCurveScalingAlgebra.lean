import SGPT.PSH.SourceTestCurveScalingProjection
import SGPT.PSH.SourceTestCurveSumIGood
import SGPT.PSH.SourceTestCurveSumTranslation

/-! # Finite positive-scaling algebra of the original test curves
Only the finite clauses of `prop:resclacompat` are addressed here.
The arbitrary-family supremum clause remains separate and unproved.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Distributivity as an equality of entire actual original backgrounds. -/
theorem sourceTCScaledSumBackground_eq
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (c : ℝ) :
    nativeClosedFormToAtlas (c • atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))) =
    nativeClosedFormToAtlas
      (atlasClosedFormToNative (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) +
       atlasClosedFormToNative (nativeClosedFormToAtlas (c • atlasClosedFormToNative σ))) := by
  simp only [sourceNativeAtlasForm_roundTrip, smul_add]

/-- Composition as an equality of entire actual original backgrounds. -/
theorem sourceTCScaledCompositionBackground_eq
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (c d : ℝ) :
    nativeClosedFormToAtlas (c • atlasClosedFormToNative
      (nativeClosedFormToAtlas (d • atlasClosedFormToNative θ))) =
    nativeClosedFormToAtlas ((c*d) • atlasClosedFormToNative θ) := by
  simp only [sourceNativeAtlasForm_roundTrip, smul_smul]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Composition of complete actual curves, with exact whole backgrounds. -/
theorem SourceTestCurve.positiveScale_positiveScale (Γ : SourceTestCurve θ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ((Γ.positiveScale hd).positiveScale hc).castBackground
      (sourceTCScaledCompositionBackground_eq θ c d) =
      Γ.positiveScale (mul_pos hc hd) := by
  apply SourceTestCurve.ext_of_max_potential
  · rw [SourceTestCurve.castBackground_max]
    simp only [SourceTestCurve.positiveScale_max]
    ring
  · intro r hr hs
    rw [SourceTestCurve.castBackground_potential _ _ r
      (by simpa only [SourceTestCurve.castBackground_max] using hr) hr]
    simp only [SourceTestCurve.positiveScale_potential]
    funext x
    have he : (r / c) / d = r / (c*d) := by ring
    simp only [he, ← EReal.coe_mul, ← mul_assoc]

omit [ConnectedSpace M] in
/-- Parameter translation commutes with scaling in the original convention. -/
theorem SourceTestCurve.positiveScale_translate (Γ : SourceTestCurve θ)
    {c : ℝ} (hc : 0 < c) (C : ℝ) :
    (Γ.translate C).positiveScale hc = (Γ.positiveScale hc).translate (c*C) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.positiveScale_max, SourceTestCurve.translate_max]
    ring
  · intro r hr hs
    simp only [SourceTestCurve.positiveScale_potential, SourceTestCurve.translate_potential]
    have he : r / c - C = (r - c*C) / c := by
      field_simp [hc.ne']
    simp only [he]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Scaling the actual raw convolution strictly below its cutoff. All
infinite values are retained; only the established open recovery is used. -/
theorem sourceTestCurveRawSum_positiveScale (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {c : ℝ} (hc : 0 < c) {r : ℝ}
    (hr : r < c * (Γ.max + Δ.max)) :
    sourceTestCurveRawSum (Γ.positiveScale hc) (Δ.positiveScale hc) r =
      fun x => (c : EReal) * sourceTestCurveRawSum Γ Δ (r/c) x := by
  have ho : r/c < Γ.max + Δ.max := (div_lt_iff₀ hc).mpr (by nlinarith)
  have hs : r < (Γ.positiveScale hc).max + (Δ.positiveScale hc).max := by
    change r < c*Γ.max+c*Δ.max
    nlinarith
  rw [sourceTestCurveRawSum_eq_uscSup_open _ _ hs,
    sourceTestCurveRawSum_eq_uscSup_open _ _ ho]
  change uscRegularization (fun x => ⨆ a : Ioo (r-c*Δ.max) (c*Γ.max),
    sourceTestCurveAt (Γ.positiveScale hc) a.1 x +
      sourceTestCurveAt (Δ.positiveScale hc) (r-a.1) x) =
    fun x => (c : EReal) * uscRegularization (fun x =>
      ⨆ b : Ioo (r/c-Δ.max) Γ.max,
        sourceTestCurveAt Γ b.1 x + sourceTestCurveAt Δ (r/c-b.1) x) x
  rw [← sourcePositiveScaling_uscRegularization c hc]
  apply congrArg uscRegularization
  funext x
  let f : Ioo (r-c*Δ.max) (c*Γ.max) → Ioo (r/c-Δ.max) Γ.max := fun a =>
    ⟨a.1/c, by
      constructor
      · apply (lt_div_iff₀ hc).mpr
        have hh : r/c*c = r := div_mul_cancel₀ r hc.ne'
        nlinarith [a.2.1]
      · exact (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using a.2.2)⟩
  have hf (a : Ioo (r-c*Δ.max) (c*Γ.max)) :
      sourceTestCurveAt (Γ.positiveScale hc) a.1 x +
        sourceTestCurveAt (Δ.positiveScale hc) (r-a.1) x =
      (c : EReal) * (sourceTestCurveAt Γ (f a).1 x +
        sourceTestCurveAt Δ (r/c-(f a).1) x) := by
    have ha : a.1 < (Γ.positiveScale hc).max := a.2.2
    have hb : r-a.1 < (Δ.positiveScale hc).max := by
      change r-a.1 < c*Δ.max
      linarith [a.2.1]
    have hbo : r/c-(f a).1 < Δ.max := by
      linarith [(f a).2.1]
    rw [sourceTestCurveAt_of_lt _ ha, sourceTestCurveAt_of_lt _ hb,
      sourceTestCurveAt_of_lt Γ (f a).2.2, sourceTestCurveAt_of_lt Δ hbo]
    simp only [SourceTestCurvePredata.positiveScale_potential]
    rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc.le) (EReal.coe_ne_top c)]
    congr 2
    apply congrArg (fun t : Iio Δ.max => Δ.potential t x)
    apply Subtype.ext
    dsimp [f]
    ring
  rw [show (c : EReal) * (⨆ b : Ioo (r/c-Δ.max) Γ.max,
      sourceTestCurveAt Γ b.1 x + sourceTestCurveAt Δ (r/c-b.1) x) =
      ⨆ b : Ioo (r/c-Δ.max) Γ.max,
        (c : EReal) * (sourceTestCurveAt Γ b.1 x + sourceTestCurveAt Δ (r/c-b.1) x) from
      (sourcePositiveERealOrderIso c hc).map_iSup _]
  apply le_antisymm
  · exact iSup_le fun a => (hf a).le.trans (le_iSup
      (fun b : Ioo (r/c-Δ.max) Γ.max =>
        (c : EReal) * (sourceTestCurveAt Γ b.1 x + sourceTestCurveAt Δ (r/c-b.1) x)) (f a))
  · apply iSup_le
    intro b
    let a : Ioo (r-c*Δ.max) (c*Γ.max) := ⟨c*b.1, by
      constructor
      · have hb := b.2.1
        have hh := (mul_lt_mul_of_pos_left hb hc)
        field_simp [hc.ne'] at hh
        nlinarith
      · exact mul_lt_mul_of_pos_left b.2.2 hc⟩
    have he : f a = b := by
      apply Subtype.ext
      change c*b.1/c = b.1
      field_simp
    simpa only [he] using (hf a).symm.le.trans (le_iSup
      (fun a : Ioo (r-c*Δ.max) (c*Γ.max) =>
        sourceTestCurveAt (Γ.positiveScale hc) a.1 x +
          sourceTestCurveAt (Δ.positiveScale hc) (r-a.1) x) a)

/-- Positive rescaling distributes over the genuine ordinary-envelope sum.
This is only the finite sum clause of the original compound proposition. -/
theorem SourceTestCurve.positiveScale_sum (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) {c : ℝ} (hc : 0 < c) :
    ((SourceTestCurve.sum omega Γ Δ).positiveScale hc).castBackground
      (sourceTCScaledSumBackground_eq θ σ c) =
      SourceTestCurve.sum omega (Γ.positiveScale hc) (Δ.positiveScale hc) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.positiveScale_max,
      SourceTestCurve.sum_max]
    ring
  · intro r hr hs
    have hrl : r < ((SourceTestCurve.sum omega Γ Δ).positiveScale hc).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    have hrr : r < c * (Γ.max + Δ.max) := hrl
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr]
    simp only [SourceTestCurve.positiveScale_potential, SourceTestCurve.sum_potential]
    have hraw : sourceTestCurveRawSum (Γ.positiveScale hc).toSourceTestCurvePredata
        (Δ.positiveScale hc).toSourceTestCurvePredata r =
        fun x => (c : EReal) * sourceTestCurveRawSum Γ.toSourceTestCurvePredata
          Δ.toSourceTestCurvePredata (r/c) x :=
      sourceTestCurveRawSum_positiveScale Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata hc hrr
    rw [hraw]
    exact (sourceOrdinaryEnvelope_positiveScaling
      (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata (r/c)) hc).symm.trans
      (congrArg (fun B => sourceSingularityEnvelope B
        (fun x => (c : EReal) * sourceTestCurveRawSum Γ.toSourceTestCurvePredata
          Δ.toSourceTestCurvePredata (r/c) x)) (sourceTCScaledSumBackground_eq θ σ c))

end SGPT.PSH.VariableComplexAtlas
