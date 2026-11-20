import SGPT.PSH.SourceIModelTestCurveLimits
import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone

/-! # The original I-envelope of a test curve

Every slice is the original all-competitor I-envelope.  Genuineness,
concavity, ordinary fixedness, positive limit mass and actual basedness
are all proved from the original input curve.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Source positive forms may be semipositive: the same original potential
is genuine in every such actual enlarged background. -/
theorem sourceThetaPSH_add_semipositive
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH (θ.add η) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeClosedForm_add]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hη

omit [ConnectedSpace M] in
/-- Genuine mixed-background monotonicity transfers original mass after
arbitrary semipositive addition, including the zero form and dimension zero. -/
theorem sourcePotentialMass_le_add_semipositive
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure (θ.add η) u
        (sourceThetaPSH_add_semipositive η hη hu) univ := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnew := (isThetaPSH_iff_nativeThetaPotential (θ.add η) u).mp
    (sourceThetaPSH_add_semipositive η hη hu)
  have hnew' : IsThetaPshPotential
      (atlasClosedFormToNative θ + (1 : ℝ) • atlasClosedFormToNative η).val u := by
    simpa only [one_smul, sourceNativeClosedForm_add] using hnew
  change DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ) u _ ≤
    DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative (θ.add η)) u _
  simpa only [one_smul, sourceNativeClosedForm_add] using
    (AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul hη
      (show (0 : ℝ) < 1 by norm_num) hun hnew')

omit [MeasurableSpace M] [BorelSpace M] in
private theorem iEnvelope_genuine {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH σ u) :
    (ofFixedModel n M).IsThetaPSH σ (sourceIEnvelope σ u) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential σ u).mp hu
  apply (isThetaPSH_iff_nativeThetaPotential σ _).mpr
  rw [sourceIEnvelope_eq_native σ u hu]
  exact iSingularityEnvelope_isThetaPshPotential (atlasClosedFormToNative σ).val
    (atlasClosedFormToNative σ).property.1 (atlasClosedFormToNative σ).property.2
    hn.1.hasSmoothLocalPotentials u hn

omit [MeasurableSpace M] [BorelSpace M] in
private theorem iEnvelope_ordinary_fixed {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH σ u) :
    sourceSingularityEnvelope σ (sourceIEnvelope σ u) = sourceIEnvelope σ u := by
  have hn := (isThetaPSH_iff_nativeThetaPotential σ u).mp hu
  rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native σ u hu]
  exact singularityEnvelope_iSingularityEnvelope (atlasClosedFormToNative σ).val
    (atlasClosedFormToNative σ).property.1 (atlasClosedFormToNative σ).property.2
    hn.1.hasSmoothLocalPotentials u hn

omit [MeasurableSpace M] [BorelSpace M] in
private theorem iEnvelope_native_iModel {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH σ u) :
    IEnvelope.IsIModelPotential (atlasClosedFormToNative σ).val (sourceIEnvelope σ u) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential σ u).mp hu
  rw [sourceIEnvelope_eq_native σ u hu]
  exact iSingularityEnvelope_isIModelPotential (atlasClosedFormToNative σ).val
    (atlasClosedFormToNative σ).property.1 (atlasClosedFormToNative σ).property.2
    hn.1.hasSmoothLocalPotentials u hn

omit [MeasurableSpace M] [BorelSpace M] in
private theorem iEnvelope_mono {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH σ u)
    (hv : (ofFixedModel n M).IsThetaPSH σ v) (huv : u ≤ v) :
    sourceIEnvelope σ u ≤ sourceIEnvelope σ v := by
  rw [sourceIEnvelope_eq_native σ u hu, sourceIEnvelope_eq_native σ v hv]
  have hvn := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  exact ActualIEnvelopeOrderInfimum.iSingularityEnvelope_le_of_iOrderOnManifold
    (atlasClosedFormToNative σ) hvn
    (iOrderOnManifold_of_le hvn.1.quasiPlurisubharmonic huv)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem iEnvelope_convexComb_le {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH σ u)
    (hv : (ofFixedModel n M).IsThetaPSH σ v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceIEnvelope σ u) (sourceIEnvelope σ v) ≤
      sourceIEnvelope σ (convexComb t u v) := by
  have hun := (isThetaPSH_iff_nativeThetaPotential σ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  have hcomb := (isThetaPSH_iff_nativeThetaPotential σ _).mpr
    (isThetaPshPotential_convexComb hun hvn ht0 ht1)
  intro x
  change (t : EReal) * sourceIEnvelope σ u x +
      ((1 - t : ℝ) : EReal) * sourceIEnvelope σ v x ≤
    sourceIEnvelope σ (fun y ↦ (t : EReal) * u y + ((1 - t : ℝ) : EReal) * v y) x
  rw [sourceIEnvelope_eq_native σ u hu, sourceIEnvelope_eq_native σ v hv,
    sourceIEnvelope_eq_native σ
      (fun y ↦ (t : EReal) * u y + ((1 - t : ℝ) : EReal) * v y) hcomb]
  simpa only [sub_sub_cancel] using
    (ActualIEnvelopeAdditionConcavity.iSingularityEnvelope_convexCombination_le
      hun hvn (sub_pos.mpr ht1) (sub_lt_self 1 ht0) x)

omit [MeasurableSpace M] [BorelSpace M] in
/-- All original preliminary clauses for the literal I-envelope family in
any actual background in which the original slices are genuine. -/
def sourceTestCurveIEnvelopePredata (Γ : SourceTestCurvePredata θ)
    (σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hσ : ∀ r, (ofFixedModel n M).IsThetaPSH σ (Γ.potential r)) :
    SourceTestCurvePredata σ where
  max := Γ.max
  potential r := sourceIEnvelope σ (Γ.potential r)
  thetaPSH r := iEnvelope_genuine (hσ r)
  antitone x a b hab := iEnvelope_mono (hσ b) (hσ a)
    (fun y ↦ Γ.antitone y hab) x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords
    intro p q t ht0 ht1 y
    have hcomb := (isThetaPSH_iff_nativeThetaPotential σ _).mpr
      (isThetaPshPotential_convexComb
        ((isThetaPSH_iff_nativeThetaPotential σ _).mp (hσ p))
        ((isThetaPSH_iff_nativeThetaPotential σ _).mp (hσ q)) ht0 ht1)
    exact (iEnvelope_convexComb_le (hσ p) (hσ q) ht0 ht1 y).trans
      (iEnvelope_mono hcomb (hσ _) (Γ.convexComb_le p q ht0 ht1) y)
  fixedPoint r := iEnvelope_ordinary_fixed (hσ r)

/-- Genuine increasing I-envelope continuity identifies the actual entire
limit; the hypotheses concern the original input in the chosen background. -/
theorem sourceTestCurveIEnvelopePredata_limit (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ)
    (hσ : ∀ r, (ofFixedModel n M).IsThetaPSH σ (Γ.potential r))
    (hlim : (ofFixedModel n M).IsThetaPSH σ (sourceTestCurveLimit Γ))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure σ (sourceTestCurveLimit Γ) hlim univ) :
    sourceTestCurveLimit (sourceTestCurveIEnvelopePredata Γ σ hσ) =
      sourceIEnvelope σ (sourceTestCurveLimit Γ) := by
  let H := sourceTestCurveIEnvelopePredata Γ σ hσ
  have hbig := sourcePositiveMass_isBig omega hlim hpos
  have hu := (isThetaPSH_iff_nativeThetaPotential σ _).mp hlim
  have hv (j : ℕ) : IsThetaPshPotential (atlasClosedFormToNative σ).val
      (Γ.potential (sourceTestCurveExhaustingParameter Γ j)) :=
    (isThetaPSH_iff_nativeThetaPotential σ _).mp (hσ _)
  have hid := IEnvelopeIncreasingRegularizedSupremum.iSingularityEnvelope_regularized_iSup_eq
    omega (atlasClosedFormToNative σ) hbig hv Γ.exhaustingPotential_monotone hu
    Γ.exhaustingPotential_regularized_eq hpos
  rw [sourceIEnvelope_eq_native σ (sourceTestCurveLimit Γ) hlim]
  rw [← H.exhaustingPotential_regularized_eq]
  convert hid using 1
  apply congrArg uscRegularization
  apply iSup_congr
  intro j
  exact sourceIEnvelope_eq_native σ _ (hσ _)

private theorem sourceTestCurveIEnvelope_limit_positive (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ)
    (hσ : ∀ r, (ofFixedModel n M).IsThetaPSH σ (Γ.potential r))
    (hlim : (ofFixedModel n M).IsThetaPSH σ (sourceTestCurveLimit Γ))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure σ (sourceTestCurveLimit Γ) hlim univ) :
    0 < sourcePotentialNonPluripolarMeasure σ
      (sourceTestCurveLimit (sourceTestCurveIEnvelopePredata Γ σ hσ))
      (sourceTestCurveIEnvelopePredata Γ σ hσ).limit_thetaPSH univ := by
  have hle : sourceTestCurveLimit Γ ≤
      sourceTestCurveLimit (sourceTestCurveIEnvelopePredata Γ σ hσ) := by
    apply uscRegularization_mono
    intro x
    apply iSup_mono
    intro r
    exact le_sourceIEnvelope (hσ r) (Γ.le_zero r)
      (sourceIEquivalent_refl ⟨σ, hσ r⟩) x
  exact hpos.trans_le (sourcePotentialNonPluripolarMass_mono omega hlim
    (sourceTestCurveIEnvelopePredata Γ σ hσ).limit_thetaPSH
    (MoreSingularOn.of_le fun x _ ↦ hle x))

/-- The literal original I-envelope is an actual test curve with all fields
produced from its original input. -/
def SourceTestCurve.iEnvelope (omega : KahlerBackground n M) (Γ : SourceTestCurve θ) :
    SourceTestCurve θ where
  toSourceTestCurvePredata := sourceTestCurveIEnvelopePredata
    Γ.toSourceTestCurvePredata θ Γ.thetaPSH
  positiveLimitMass := sourceTestCurveIEnvelope_limit_positive omega
    Γ.toSourceTestCurvePredata Γ.thetaPSH Γ.limit_thetaPSH Γ.positiveLimitMass

theorem SourceTestCurve.iEnvelope_max (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : (Γ.iEnvelope omega).max = Γ.max := rfl

theorem SourceTestCurve.iEnvelope_potential (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.iEnvelope omega).potential r = sourceIEnvelope θ (Γ.potential r) := rfl

/-- The literal spatial limit uses the same original I-envelope and input. -/
theorem SourceTestCurve.iEnvelope_limit (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.iEnvelope omega).toSourceTestCurvePredata =
      sourceIEnvelope θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata) :=
  sourceTestCurveIEnvelopePredata_limit omega Γ.toSourceTestCurvePredata
    Γ.thetaPSH Γ.limit_thetaPSH Γ.positiveLimitMass

/-- Every actual output slice is genuinely I-model, with no such input field. -/
theorem SourceTestCurve.iEnvelope_isIModel (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : SourceTestCurveIsIModel (Γ.iEnvelope omega) :=
  fun r ↦ iEnvelope_native_iModel (Γ.thetaPSH r)

/-- Original basedness identifies the new actual positive model base. -/
theorem source_test_curve_i_envelope_based (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    ∃ hmodel : SourceModelPotential θ (sourceIEnvelope θ φ),
      Γ.iEnvelope omega ∈ SourceIModelTestCurves θ (sourceIEnvelope θ φ) hmodel := by
  have heq : sourceTestCurveLimit (Γ.iEnvelope omega).toSourceTestCurvePredata =
      sourceIEnvelope θ φ := (Γ.iEnvelope_limit omega).trans (congrArg (sourceIEnvelope θ) hbased)
  have hm : SourceModelPotential θ (sourceIEnvelope θ φ) :=
    heq ▸ (Γ.iEnvelope omega).limit_model omega
  exact ⟨hm, heq, Γ.iEnvelope_isIModel omega⟩

/-- The generalized original definition in an arbitrary semipositive enlarged
background; the ambient Kähler metric is independent of the added form. -/
def SourceTestCurve.iEnvelopeBackgroundProjection (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) :
    SourceTestCurve (θ.add η) where
  toSourceTestCurvePredata := sourceTestCurveIEnvelopePredata Γ.toSourceTestCurvePredata
    (θ.add η) (fun r ↦ sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))
  positiveLimitMass := sourceTestCurveIEnvelope_limit_positive omega Γ.toSourceTestCurvePredata
    (fun r ↦ sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))
    (sourceThetaPSH_add_semipositive η hη Γ.limit_thetaPSH)
    (Γ.positiveLimitMass.trans_le (sourcePotentialMass_le_add_semipositive η hη Γ.limit_thetaPSH))

theorem SourceTestCurve.iEnvelopeBackgroundProjection_max (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) : (Γ.iEnvelopeBackgroundProjection omega η hη).max = Γ.max := rfl

theorem SourceTestCurve.iEnvelopeBackgroundProjection_potential
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.iEnvelopeBackgroundProjection omega η hη).potential r =
      sourceIEnvelope (θ.add η) (Γ.potential r) := rfl

/-- The whole actual enlarged-background limit identity on the original input. -/
theorem SourceTestCurve.iEnvelopeBackgroundProjection_limit (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.iEnvelopeBackgroundProjection omega η hη).toSourceTestCurvePredata =
      sourceIEnvelope (θ.add η)
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) :=
  sourceTestCurveIEnvelopePredata_limit omega Γ.toSourceTestCurvePredata
    (fun r ↦ sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))
    (sourceThetaPSH_add_semipositive η hη Γ.limit_thetaPSH)
    (Γ.positiveLimitMass.trans_le (sourcePotentialMass_le_add_semipositive η hη Γ.limit_thetaPSH))

/-- Genuine enlarged-background output slice I-model fields are produced. -/
theorem SourceTestCurve.iEnvelopeBackgroundProjection_isIModel
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : SourceTestCurve θ) :
    SourceTestCurveIsIModel (Γ.iEnvelopeBackgroundProjection omega η hη) :=
  fun r ↦ iEnvelope_native_iModel (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))

/-- The second entire original transitionPI assertion, including its
produced same-function ordinary positive model base. -/
theorem source_test_curve_i_envelope_background_based (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    ∃ hmodel : SourceModelPotential (θ.add η) (sourceIEnvelope (θ.add η) φ),
      Γ.iEnvelopeBackgroundProjection omega η hη ∈
        SourceIModelTestCurves (θ.add η) (sourceIEnvelope (θ.add η) φ) hmodel := by
  have heq : sourceTestCurveLimit
      (Γ.iEnvelopeBackgroundProjection omega η hη).toSourceTestCurvePredata =
      sourceIEnvelope (θ.add η) φ :=
    (Γ.iEnvelopeBackgroundProjection_limit omega η hη).trans
      (congrArg (sourceIEnvelope (θ.add η)) hbased)
  have hm : SourceModelPotential (θ.add η) (sourceIEnvelope (θ.add η) φ) :=
    heq ▸ (Γ.iEnvelopeBackgroundProjection omega η hη).limit_model omega
  exact ⟨hm, heq, Γ.iEnvelopeBackgroundProjection_isIModel omega η hη⟩

end SGPT.PSH.VariableComplexAtlas
