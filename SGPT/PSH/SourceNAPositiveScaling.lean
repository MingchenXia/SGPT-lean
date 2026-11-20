import SGPT.PSH.SourceNASumAlgebra
import SGPT.PSH.SourceTestCurvePositiveScaling

/-! # Actual positive rescaling of the original non-Archimedean systems

The existing genuine positive test-curve scaling, I-modelness, envelope and
mass producers supply the component construction. Compatibility is proved
from actual intrinsic P-type and original same-background antisymmetry.
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
  {α β θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual entire original atlas form corresponding to the scaled native form. -/
def sourceNAScaledBackground (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (c : ℝ) :=
  nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)

/-- Division of the actual Kähler form by a positive real number. -/
def sourceNADividedKahlerBackground {c : ℝ} (hc : 0 < c) (omega : KahlerBackground n M) :
    KahlerBackground n M := KahlerBackground.smul (inv_pos.mpr hc) omega

/-- Scaling then dividing the actual Kähler background is literally the identity. -/
theorem sourceNADividedKahlerBackground_scaled {c : ℝ} (hc : 0 < c)
    (omega : KahlerBackground n M) :
    sourceNADividedKahlerBackground hc (KahlerBackground.smul hc omega) = omega := by
  cases omega
  dsimp [sourceNADividedKahlerBackground, KahlerBackground.smul]
  congr 1
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Dividing then scaling the actual Kähler background is literally the identity. -/
theorem sourceNAScaledKahlerBackground_divided {c : ℝ} (hc : 0 < c)
    (omega : KahlerBackground n M) :
    KahlerBackground.smul hc (sourceNADividedKahlerBackground hc omega) = omega := by
  cases omega
  dsimp [sourceNADividedKahlerBackground, KahlerBackground.smul]
  congr 1
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- Exact whole-form calibration at every literal Kähler presentation. -/
theorem sourceNAPositiveScaleBackground_eq (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {c : ℝ} (hc : 0 < c) (omega : KahlerBackground n M) :
    sourceNAScaledBackground
        (sourceTestCurveEnlargedBackground (sourceNADividedKahlerBackground hc omega) θ) c =
      sourceTestCurveEnlargedBackground omega (sourceNAScaledBackground θ c) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNAScaledBackground, sourceNativeAtlasForm_roundTrip,
    sourceTestCurveEnlargedBackground_native, sourceNADividedKahlerBackground,
    KahlerBackground.smul_form, smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- The same exact entire background equality at the geometric component index. -/
theorem sourceNAPositiveScaleComponentBackground_eq
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {c : ℝ} (hc : 0 < c)
    (κ : SourceKahlerForm n M) :
    sourceNAScaledBackground (sourceTestCurveEnlargedBackground
      (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ)) θ) c =
        sourceNAComponentBackground (sourceNAScaledBackground θ c) κ :=
  sourceNAPositiveScaleBackground_eq θ hc (sourceKahlerFormRepresentative κ)

/-- Dividing an actual semipositive form by c remains genuinely semipositive. -/
theorem sourceNADividedBackground_semipositive
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) {c : ℝ} (hc : 0 < c) :
    (atlasClosedFormToNative (sourceNAScaledBackground η c⁻¹)).val.IsSemipositive := by
  simpa only [sourceNAScaledBackground, sourceNativeAtlasForm_roundTrip] using
    KahlerDomination.isSemipositive_smul hη (inv_pos.mpr hc).le

/-- Exact whole-background calibration for independent full background change. -/
theorem sourceNAPositiveScaleChangeBackground_eq
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)) {c : ℝ} (hc : 0 < c) :
    sourceNAScaledBackground (θ.add (sourceNAScaledBackground η c⁻¹)) c =
      (sourceNAScaledBackground θ c).add η := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNAScaledBackground, sourceNativeAtlasForm_roundTrip,
    sourceNativeClosedForm_add, smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Scale the SAME actual existential positive global-P witness. Positivity
of the output masses is manufactured by the existing genuine mass formula. -/
theorem sourcePOrder_positiveScaling {u v : M → EReal}
    (h : GlobalPComparison.sourcePOrder (n := n) u v) {c : ℝ} (hc : 0 < c) :
    GlobalPComparison.sourcePOrder (n := n) (fun x ↦ (c : EReal) * u x)
      (fun x ↦ (c : EReal) * v x) := by
  obtain ⟨T, hu, hv, hup, hvp, hP⟩ := h
  let A := nativeClosedFormToAtlas T
  have huA : (ofFixedModel n M).IsThetaPSH A u :=
    (isThetaPSH_iff_nativeThetaPotential A u).mpr
      (by simpa only [A, sourceNativeAtlasForm_roundTrip] using hu)
  have hvA : (ofFixedModel n M).IsThetaPSH A v :=
    (isThetaPSH_iff_nativeThetaPotential A v).mpr
      (by simpa only [A, sourceNativeAtlasForm_roundTrip] using hv)
  have huc := RestrictedApproximantComparison.isThetaPshPotential_smul hu hc
  have hvc := RestrictedApproximantComparison.isThetaPshPotential_smul hv hc
  have hmu : DiagonalMass.diagonalPotentialMass (c • T) (fun x ↦ (c : EReal) * u x) huc =
      ENNReal.ofReal (c ^ n) * DiagonalMass.diagonalPotentialMass T u hu := by
    simpa only [A, sourcePotentialNonPluripolarMeasure, sourceNativeAtlasForm_roundTrip,
      DiagonalMass.diagonalPotentialMass] using sourcePositiveScaling_actualMass huA hc
  have hmv : DiagonalMass.diagonalPotentialMass (c • T) (fun x ↦ (c : EReal) * v x) hvc =
      ENNReal.ofReal (c ^ n) * DiagonalMass.diagonalPotentialMass T v hv := by
    simpa only [A, sourcePotentialNonPluripolarMeasure, sourceNativeAtlasForm_roundTrip,
      DiagonalMass.diagonalPotentialMass] using sourcePositiveScaling_actualMass hvA hc
  refine ⟨c • T, huc, hvc, ?_, ?_, ?_⟩
  · change 0 < DiagonalMass.diagonalPotentialMass (c • T) _ huc
    rw [hmu]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hc n), hup⟩
  · change 0 < DiagonalMass.diagonalPotentialMass (c • T) _ hvc
    rw [hmv]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hc n), hvp⟩
  · have heu := sourceOrdinaryEnvelope_positiveScaling (θ := A) u hc
    have hev := sourceOrdinaryEnvelope_positiveScaling (θ := A) v hc
    simp only [A, sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] at heu hev
    change singularityEnvelope (c • T).val _ ≤ singularityEnvelope (c • T).val _
    rw [heu, hev]
    intro x
    exact (sourcePositiveERealOrderIso c hc).monotone (hP x)

omit [ConnectedSpace M] in
/-- Actual intrinsic curve order is preserved by positive scaling,
including comparisons across two different original base forms. -/
theorem SourceTestCurvePOrder.positiveScale
    {G : SourceTestCurve θ} {H : SourceTestCurve σ} (h : SourceTestCurvePOrder G H)
    {c : ℝ} (hc : 0 < c) : SourceTestCurvePOrder (G.positiveScale hc) (H.positiveScale hc) := by
  refine ⟨mul_le_mul_of_nonneg_left h.cutoff_le hc.le, ?_⟩
  intro r hr
  have hs : r / c < G.max := (div_lt_iff₀ hc).mpr (by
    change r < c * G.max at hr
    nlinarith)
  simpa only [SourceTestCurve.positiveScale_potential] using
    sourcePOrder_positiveScaling (h.slice_le (r / c) hs) hc

/-- The SAME existing scaled positive curve with its already proved genuine
positive I-model union membership. -/
def SourcePositiveIModelTestCurve.positiveScale (G : SourcePositiveIModelTestCurve θ)
    (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) :
    SourcePositiveIModelTestCurve (sourceNAScaledBackground θ c) :=
  ⟨G.val.positiveScale hc, SourceTestCurve.positiveScale_iModel_positive omega G.property hc⟩

/-- The actual scaled component at the divided original Kähler presentation. -/
def SourceNAPotential.positiveScaleComponent (Γ : SourceNAPotential θ)
    {c : ℝ} (hc : 0 < c) (κ : SourceKahlerForm n M) :
    SourcePositiveIModelTestCurve (sourceNAComponentBackground (sourceNAScaledBackground θ c) κ) :=
  ((Γ.realizedComponent (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ))).positiveScale
    (sourceKahlerFormRepresentative κ) hc).castBackground
      (sourceNAPositiveScaleComponentBackground_eq θ hc κ)

/-- Every component has exactly c times the original common cutoff. -/
theorem SourceNAPotential.positiveScaleComponent_max (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (κ : SourceKahlerForm n M) :
    (Γ.positiveScaleComponent hc κ).val.max = c * sourceNAPotentialCutoff omega Γ := by
  simp only [SourceNAPotential.positiveScaleComponent,
    SourcePositiveIModelTestCurve.castBackground_max, SourcePositiveIModelTestCurve.positiveScale,
    SourceTestCurve.positiveScale_max, SourceNAPotential.realizedComponent_max_eq_cutoff omega]

/-- Independent original readers and genuine scaled curve order give both
intrinsic comparisons between ANY two of the constructed output components. -/
theorem SourceNAPotential.positiveScaleComponent_POrder_equivalent
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (κ ζ : SourceKahlerForm n M) :
    SourceTestCurvePOrder (Γ.positiveScaleComponent hc κ).val (Γ.positiveScaleComponent hc ζ).val ∧
      SourceTestCurvePOrder (Γ.positiveScaleComponent hc ζ).val (Γ.positiveScaleComponent hc κ).val := by
  let omega := sourceKahlerFormRepresentative κ
  let omega' := sourceKahlerFormRepresentative ζ
  let G := Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)
  let H := Γ.realizedComponent (sourceNADividedKahlerBackground hc omega')
  have h := Γ.realizedComponent_POrder_equivalent
    (sourceNADividedKahlerBackground hc omega) (sourceNADividedKahlerBackground hc omega')
  have hk := (G.positiveScale omega hc).castBackground_POrder_equivalent omega
    (sourceNAPositiveScaleComponentBackground_eq θ hc κ)
  have hz := (H.positiveScale omega' hc).castBackground_POrder_equivalent omega
    (sourceNAPositiveScaleComponentBackground_eq θ hc ζ)
  exact ⟨SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hk.2 (h.1.positiveScale hc)) hz.1,
    SourceTestCurvePOrder.trans omega
      (SourceTestCurvePOrder.trans omega hz.2 (h.2.positiveScale hc)) hk.1⟩

/-- The literal original I-transition compatibility is manufactured, not assumed. -/
theorem SourceNAPotential.positiveScaleComponent_compatible
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (κ ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE κ ζ) :
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference (sourceNAScaledBackground θ c) h)
      (Γ.positiveScaleComponent hc κ) = Γ.positiveScaleComponent hc ζ := by
  let omega := sourceKahlerFormRepresentative ζ
  have ht := sourceIModelTestCurveTransition_POrder_equivalent omega
    (sourceNAComponentBackground_difference (sourceNAScaledBackground θ c) h)
    (Γ.positiveScaleComponent hc κ)
  have hs := Γ.positiveScaleComponent_POrder_equivalent hc κ ζ
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omega
    (SourceTestCurvePOrder.trans omega ht.2 hs.1)
    (SourceTestCurvePOrder.trans omega hs.2 ht.1)

/-- The actual full original NA positive rescaling. -/
def SourceNAPotential.positiveScale (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) :
    SourceNAPotential (sourceNAScaledBackground θ c) where
  component κ := Γ.positiveScaleComponent hc κ
  compatible κ ζ h := Γ.positiveScaleComponent_compatible hc κ ζ h

/-- Positive rescaling multiplies the SAME original common real cutoff. -/
theorem sourceNAPotentialCutoff_positiveScale (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) :
    sourceNAPotentialCutoff omega (Γ.positiveScale hc) = c * sourceNAPotentialCutoff omega Γ :=
  Γ.positiveScaleComponent_max omega hc (sourceKahlerFormOfBackground omega)

/-- Any scaled output component has the intrinsic type of the scaled input
reader at ANY independently specified divided literal Kähler presentation. -/
theorem SourceNAPotential.positiveScaleComponent_POrder_equivalent_reader
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (κ : SourceKahlerForm n M)
    (omega : KahlerBackground n M) :
    SourceTestCurvePOrder (Γ.positiveScaleComponent hc κ).val
      ((Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)).positiveScale omega hc).val ∧
    SourceTestCurvePOrder
      ((Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)).positiveScale omega hc).val
      (Γ.positiveScaleComponent hc κ).val := by
  let B := sourceKahlerFormRepresentative κ
  let G := Γ.realizedComponent (sourceNADividedKahlerBackground hc B)
  have h := Γ.realizedComponent_POrder_equivalent
    (sourceNADividedKahlerBackground hc B) (sourceNADividedKahlerBackground hc omega)
  have hk := (G.positiveScale B hc).castBackground_POrder_equivalent omega
    (sourceNAPositiveScaleComponentBackground_eq θ hc κ)
  exact ⟨SourceTestCurvePOrder.trans omega hk.2 (h.1.positiveScale hc),
    SourceTestCurvePOrder.trans omega (h.2.positiveScale hc) hk.1⟩

/-- The ENTIRE original scaled-reader prescription at every literal Kähler
form, as equality of genuine positive I-model curves after whole-form transport. -/
theorem SourceNAPotential.positiveScale_realizedComponent
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (omega : KahlerBackground n M) :
    ((Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)).positiveScale omega hc).castBackground
        (sourceNAPositiveScaleBackground_eq θ hc omega) =
      (Γ.positiveScale hc).realizedComponent omega := by
  let κ := sourceKahlerFormOfBackground omega
  have hs := Γ.positiveScaleComponent_POrder_equivalent_reader hc κ omega
  have hr := (Γ.positiveScale hc).realizedComponent_component_POrder_equivalent omega κ
  have hk := SourcePositiveIModelTestCurve.castBackground_POrder_equivalent omega
    ((Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)).positiveScale omega hc)
    (sourceNAPositiveScaleBackground_eq θ hc omega)
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omega
    (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hk.2 hs.2) hr.2)
    (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hr.1 hs.1) hk.1)

/-- The original reader formula uniquely determines the full scaled system. -/
theorem SourceNAPotential.positiveScale_unique (Γ : SourceNAPotential θ)
    {c : ℝ} (hc : 0 < c) (E : SourceNAPotential (sourceNAScaledBackground θ c))
    (h : ∀ omega : KahlerBackground n M,
      E.realizedComponent omega =
        ((Γ.realizedComponent (sourceNADividedKahlerBackground hc omega)).positiveScale omega hc).castBackground
          (sourceNAPositiveScaleBackground_eq θ hc omega)) : E = Γ.positiveScale hc := by
  apply SourceNAPotential.ext_of_realizedComponent
  intro omega
  exact (h omega).trans (Γ.positiveScale_realizedComponent hc omega)

/-- Full positive NA rescaling genuinely extends the SAME existing positive
I-model test-curve rescaling under the canonical positive inclusion. -/
theorem sourcePositiveTestCurveToNA_positiveScale (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) {c : ℝ} (hc : 0 < c) :
    (sourcePositiveTestCurveToNA G).positiveScale hc =
      sourcePositiveTestCurveToNA (G.positiveScale omega hc) := by
  apply SourceNAPotential.ext
  intro κ
  let B := sourceKahlerFormRepresentative κ
  let Γ := sourcePositiveTestCurveToNA G
  have hs := Γ.positiveScaleComponent_POrder_equivalent_reader hc κ B
  have hG := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent G
    (sourceNADividedKahlerBackground hc B)
  have ht := sourceIModelTestCurveTransition_POrder_equivalent B
    (sourceNAComponentBackground_positive (sourceNAScaledBackground θ c) κ) (G.positiveScale omega hc)
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm B
    (SourceTestCurvePOrder.trans B (SourceTestCurvePOrder.trans B hs.1 (hG.1.positiveScale hc)) ht.1)
    (SourceTestCurvePOrder.trans B (SourceTestCurvePOrder.trans B ht.2 (hG.2.positiveScale hc)) hs.2)

/-- Original cross-background NA order is preserved by positive rescaling.
The actual input comparison itself supplies an actual Kähler index. -/
theorem SourceNAPOrder.positiveScale {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (h : SourceNAPOrder Γ Δ) {c : ℝ} (hc : 0 < c) :
    SourceNAPOrder (Γ.positiveScale hc) (Δ.positiveScale hc) := by
  obtain ⟨κ, hκ⟩ := h
  let B := sourceKahlerFormRepresentative κ
  let D := sourceNADividedKahlerBackground hc B
  have hu := (sourceNAPOrder_iff_realizedComponents Γ Δ D D).mp ⟨κ, hκ⟩
  have hs := Γ.positiveScaleComponent_POrder_equivalent_reader hc κ B
  have ht := Δ.positiveScaleComponent_POrder_equivalent_reader hc κ B
  exact ⟨κ, SourceTestCurvePOrder.trans B
    (SourceTestCurvePOrder.trans B hs.1 (hu.positiveScale hc)) ht.2⟩

/-- WHOLE original L581: arbitrary semipositive FULL NA-to-NA background
change commutes with positive scaling and inverse scaling of the added form. -/
theorem SourceNAPotential.positiveScale_backgroundChange (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (Γ.positiveScale hc).backgroundChange η hη =
      ((Γ.backgroundChange (sourceNAScaledBackground η c⁻¹)
        (sourceNADividedBackground_semipositive η hη hc)).positiveScale hc).castBackground
          (sourceNAPositiveScaleChangeBackground_eq θ η hc) := by
  have hΓ := Γ.backgroundChange_POrder_equivalent omega (sourceNAScaledBackground η c⁻¹)
    (sourceNADividedBackground_semipositive η hη hc)
  have hL := (Γ.positiveScale hc).backgroundChange_POrder_equivalent omega η hη
  have hR := SourceNAPotential.castBackground_POrder_equivalent omega
    ((Γ.backgroundChange (sourceNAScaledBackground η c⁻¹)
      (sourceNADividedBackground_semipositive η hη hc)).positiveScale hc)
    (sourceNAPositiveScaleChangeBackground_eq θ η hc)
  exact SourceNAPOrder.antisymm
    (hL.2.trans ((hΓ.1.positiveScale hc).trans hR.1))
    (hR.2.trans ((hΓ.2.positiveScale hc).trans hL.1))

omit [BorelSpace M] [ConnectedSpace M] in
/-- Equality transport changes no actual positive-curve spatial-limit mass. -/
theorem SourcePositiveIModelTestCurve.castBackground_limit_mass
    (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    sourcePotentialNonPluripolarMeasure β
      (sourceTestCurveLimit (G.castBackground h).val.toSourceTestCurvePredata)
      (G.castBackground h).val.limit_thetaPSH univ =
    sourcePotentialNonPluripolarMeasure α
      (sourceTestCurveLimit G.val.toSourceTestCurvePredata) G.val.limit_thetaPSH univ := by
  cases h
  rfl

/-- Actual component mass at EVERY literal Kähler presentation is c^n
times the SAME original mass at the divided actual Kähler presentation. -/
theorem sourceNAComponentMass_positiveScale_realized
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) (omega : KahlerBackground n M) :
    sourceNAComponentMass (Γ.positiveScale hc) (sourceKahlerFormOfBackground omega) =
      ENNReal.ofReal (c ^ n) * sourceNAComponentMass Γ
        (sourceKahlerFormOfBackground (sourceNADividedKahlerBackground hc omega)) := by
  let D := sourceNADividedKahlerBackground hc omega
  let G := Γ.realizedComponent D
  let S := G.positiveScale omega hc
  let T := sourceTestCurveEnlargedBackground omega (sourceNAScaledBackground θ c)
  have he := Γ.positiveScale_realizedComponent hc omega
  have hm := congrArg (fun K : SourcePositiveIModelTestCurve T ↦
    sourcePotentialNonPluripolarMeasure T
      (sourceTestCurveLimit K.val.toSourceTestCurvePredata) K.val.limit_thetaPSH univ) he
  calc
    sourceNAComponentMass (Γ.positiveScale hc) (sourceKahlerFormOfBackground omega) =
        sourcePotentialNonPluripolarMeasure T
          (sourceTestCurveLimit ((Γ.positiveScale hc).realizedComponent omega).val.toSourceTestCurvePredata)
          ((Γ.positiveScale hc).realizedComponent omega).val.limit_thetaPSH univ :=
      sourceNAComponentMass_realized (Γ.positiveScale hc) omega
    _ = sourcePotentialNonPluripolarMeasure T
        (sourceTestCurveLimit (S.castBackground (sourceNAPositiveScaleBackground_eq θ hc omega)).val.toSourceTestCurvePredata)
        (S.castBackground (sourceNAPositiveScaleBackground_eq θ hc omega)).val.limit_thetaPSH univ := hm.symm
    _ = sourcePotentialNonPluripolarMeasure (sourceNAScaledBackground (sourceTestCurveEnlargedBackground D θ) c)
        (sourceTestCurveLimit S.val.toSourceTestCurvePredata) S.val.limit_thetaPSH univ :=
      S.castBackground_limit_mass (sourceNAPositiveScaleBackground_eq θ hc omega)
    _ = ENNReal.ofReal (c ^ n) * sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground D θ)
        (sourceTestCurveLimit G.val.toSourceTestCurvePredata) G.val.limit_thetaPSH univ :=
      SourceTestCurve.positiveScale_limit_mass G.val hc
    _ = ENNReal.ofReal (c ^ n) * sourceNAComponentMass Γ (sourceKahlerFormOfBackground D) :=
      congrArg (fun q ↦ ENNReal.ofReal (c ^ n) * q) (sourceNAComponentMass_realized Γ D).symm

/-- WHOLE original NA volume rescaling, for the literal actual infimum,
including zero NA volume and dimension zero. No real-volume conversion occurs. -/
theorem sourceNAVolume_positiveScale (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) :
    sourceNAVolume (Γ.positiveScale hc) = ENNReal.ofReal (c ^ n) * sourceNAVolume Γ := by
  let a := ENNReal.ofReal (c ^ n)
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hc n)).ne'
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  apply le_antisymm
  · have hbound (κ : SourceKahlerForm n M) :
        sourceNAVolume (Γ.positiveScale hc) ≤ a * sourceNAComponentMass Γ κ := by
      have hm := sourceNAComponentMass_positiveScale_realized Γ hc
        (KahlerBackground.smul hc (sourceKahlerFormRepresentative κ))
      rw [sourceNADividedKahlerBackground_scaled, sourceKahlerFormRepresentative_class] at hm
      exact (sourceNAVolume_le_component (Γ.positiveScale hc)
        (sourceKahlerFormOfBackground (KahlerBackground.smul hc
          (sourceKahlerFormRepresentative κ)))).trans_eq hm
    calc
      sourceNAVolume (Γ.positiveScale hc) ≤ ⨅ κ : SourceKahlerForm n M,
          a * sourceNAComponentMass Γ κ := le_iInf hbound
      _ = a * sourceNAVolume Γ := by
        simpa only [sourceNAVolume] using
          (ENNReal.mul_iInf_of_ne (f := fun κ : SourceKahlerForm n M ↦ sourceNAComponentMass Γ κ) ha0 hatop).symm
  · change a * sourceNAVolume Γ ≤ ⨅ κ : SourceKahlerForm n M, sourceNAComponentMass (Γ.positiveScale hc) κ
    apply le_iInf
    intro κ
    have hm := sourceNAComponentMass_positiveScale_realized Γ hc (sourceKahlerFormRepresentative κ)
    rw [sourceKahlerFormRepresentative_class] at hm
    rw [hm]
    gcongr
    exact sourceNAVolume_le_component Γ
      (sourceKahlerFormOfBackground (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ)))

end SGPT.PSH.VariableComplexAtlas
