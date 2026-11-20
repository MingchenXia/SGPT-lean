import SGPT.PSH.SourceTestCurveIEnvelope
import SGPT.PSH.SourceTestCurveScalingProjection
import SGPT.Foundations.Analysis.FirstPass.GeometricForms

/-! # Genuine original non-Archimedean inverse systems

The index is the existing geometric-form quotient restricted to Kähler
forms. Every component is an actual positive I-model test curve. Transitions
use the original all-competitor I-envelope; compatibility and the positive
test-curve embedding are proved from the genuine existing projection.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Exactly the existing geometric Kähler forms, identifying arbitrary
off-target coefficient extensions before forming the index. -/
abbrev SourceKahlerForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :=
  {ω : GeometricRealForm n M 2 // ω.IsKahler}

/-- Any actual native Kähler background determines its geometric form. -/
def sourceKahlerFormOfBackground (ω : KahlerBackground n M) : SourceKahlerForm n M :=
  ⟨GeometricRealForm.ofRepresentative ω.form.val, ω.isKahler⟩

/-- A representative supplies only the chartwise coefficients required by
the existing producers; the index itself remains the geometric form. -/
def sourceKahlerFormRepresentative (ω : SourceKahlerForm n M) : KahlerBackground n M := by
  let a : SmoothRealForm n M 2 := Quotient.out ω.val
  have ha : GeometricRealForm.ofRepresentative a = ω.val := Quotient.out_eq ω.val
  have hK : a.IsKahler := by
    apply (GeometricRealForm.isKahler_ofRepresentative a).mp
    rw [ha]
    exact ω.property
  exact ⟨⟨a, hK.2, fun e z hz ↦ (hK.1 e z hz).1⟩, hK⟩

/-- The chosen representative represents precisely the same geometric form. -/
theorem sourceKahlerFormRepresentative_class (ω : SourceKahlerForm n M) :
    sourceKahlerFormOfBackground (sourceKahlerFormRepresentative ω) = ω := by
  apply Subtype.ext
  exact Quotient.out_eq ω.val

/-- Choosing a representative of a given background changes no coefficient
on an actual open chart target. -/
theorem sourceKahlerFormRepresentative_geometricallyEq (ω : KahlerBackground n M) :
    (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground ω)).form.val.GeometricallyEq
      ω.form.val := by
  apply (GeometricRealForm.ofRepresentative_eq_iff _ _).mp
  exact congrArg Subtype.val
    (sourceKahlerFormRepresentative_class (sourceKahlerFormOfBackground ω))

/-- The original positive order on geometric Kähler forms, tested only on
the actual tangent lines of chart targets. -/
def sourceKahlerFormLE (ω η : SourceKahlerForm n M) : Prop :=
  ((sourceKahlerFormRepresentative η).form -
    (sourceKahlerFormRepresentative ω).form).val.IsSemipositive

private theorem closedDifference_geometricallyEq
    {a a' b b' : ClosedRealOneOneForm n M}
    (ha : a.val.GeometricallyEq a'.val) (hb : b.val.GeometricallyEq b'.val) :
    (b - a).val.GeometricallyEq (b' - a').val := by
  intro e z hz
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ha e hz, hb e hz]

private theorem closedDifference_semipositive_refl (a : ClosedRealOneOneForm n M) :
    (a - a).val.IsSemipositive := by
  rw [sub_self]
  intro e z hz v
  exact le_rfl

private theorem closedDifference_semipositive_trans
    {a b c : ClosedRealOneOneForm n M}
    (hab : (b - a).val.IsSemipositive) (hbc : (c - b).val.IsSemipositive) :
    (c - a).val.IsSemipositive := by
  have heq : c - a = (c - b) + (b - a) := by abel
  rw [heq]
  intro e z hz v
  simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
    add_nonneg (hbc e z hz v) (hab e z hz v)

private theorem closedDifference_semipositive_of_geometricallyEq
    {a b : ClosedRealOneOneForm n M} (h : a.val.GeometricallyEq b.val) :
    (b - a).val.IsSemipositive :=
  (closedDifference_geometricallyEq (SmoothRealForm.GeometricallyEq.refl a.val)
    h.symm).isSemipositive_iff.mpr (closedDifference_semipositive_refl a)

/-- The geometric index order is precisely the original difference cone,
independently of all chosen off-target coefficient extensions. -/
theorem sourceKahlerFormLE_ofBackground_iff (ω η : KahlerBackground n M) :
    sourceKahlerFormLE (sourceKahlerFormOfBackground ω) (sourceKahlerFormOfBackground η) ↔
      (η.form - ω.form).val.IsSemipositive :=
  (closedDifference_geometricallyEq (sourceKahlerFormRepresentative_geometricallyEq ω)
    (sourceKahlerFormRepresentative_geometricallyEq η)).isSemipositive_iff

theorem sourceKahlerFormLE_refl (ω : SourceKahlerForm n M) : sourceKahlerFormLE ω ω :=
  closedDifference_semipositive_refl _

theorem sourceKahlerFormLE_trans {ω η ζ : SourceKahlerForm n M}
    (hωη : sourceKahlerFormLE ω η) (hηζ : sourceKahlerFormLE η ζ) :
    sourceKahlerFormLE ω ζ := closedDifference_semipositive_trans hωη hηζ

/-- A common larger physical form, used for cutoff comparison only. -/
def sourceKahlerFormCommonUpper (ω η : SourceKahlerForm n M) : SourceKahlerForm n M :=
  sourceKahlerFormOfBackground
    ((sourceKahlerFormRepresentative ω).add (sourceKahlerFormRepresentative η))

theorem sourceKahlerFormLE_commonUpper_left (ω η : SourceKahlerForm n M) :
    sourceKahlerFormLE ω (sourceKahlerFormCommonUpper ω η) := by
  have h : (((sourceKahlerFormRepresentative ω).add
      (sourceKahlerFormRepresentative η)).form -
        (sourceKahlerFormRepresentative ω).form).val.IsSemipositive := by
    simpa only [KahlerBackground.add_form, add_sub_cancel_left] using
      (sourceKahlerFormRepresentative η).isSemipositive
  simpa only [sourceKahlerFormRepresentative_class, sourceKahlerFormCommonUpper] using
    (sourceKahlerFormLE_ofBackground_iff (sourceKahlerFormRepresentative ω)
      ((sourceKahlerFormRepresentative ω).add (sourceKahlerFormRepresentative η))).mpr h

theorem sourceKahlerFormLE_commonUpper_right (ω η : SourceKahlerForm n M) :
    sourceKahlerFormLE η (sourceKahlerFormCommonUpper ω η) := by
  have h : (((sourceKahlerFormRepresentative ω).add
      (sourceKahlerFormRepresentative η)).form -
        (sourceKahlerFormRepresentative η).form).val.IsSemipositive := by
    simpa only [KahlerBackground.add_form, add_sub_cancel_right] using
      (sourceKahlerFormRepresentative ω).isSemipositive
  simpa only [sourceKahlerFormRepresentative_class, sourceKahlerFormCommonUpper] using
    (sourceKahlerFormLE_ofBackground_iff (sourceKahlerFormRepresentative η)
      ((sourceKahlerFormRepresentative ω).add (sourceKahlerFormRepresentative η))).mpr h

/-- Geometric equality identifies the full genuine source theta-PSH domain. -/
theorem sourceThetaPSH_geometricallyEq
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (h : (atlasClosedFormToNative α).val.GeometricallyEq
      (atlasClosedFormToNative β).val) (u : M → EReal) :
    (ofFixedModel n M).IsThetaPSH α u ↔ (ofFixedModel n M).IsThetaPSH β u :=
  (isThetaPSH_iff_nativeThetaPotential α u).trans
    ((h.thetaPshPotential_iff u).trans (isThetaPSH_iff_nativeThetaPotential β u).symm)

/-- Every normalized original competitor is unchanged by off-target
coefficient choices, so the actual entire I-envelope is unchanged. -/
theorem sourceIEnvelope_geometricallyEq
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (h : (atlasClosedFormToNative α).val.GeometricallyEq
      (atlasClosedFormToNative β).val) (u : M → EReal) :
    sourceIEnvelope α u = sourceIEnvelope β u := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : sourceICompetitors β u ↦ w.val x)
      ⟨v.val, (sourceThetaPSH_geometricallyEq h v.val).mp v.property.1,
        v.property.2.1, v.property.2.2⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : sourceICompetitors α u ↦ w.val x)
      ⟨v.val, (sourceThetaPSH_geometricallyEq h v.val).mpr v.property.1,
        v.property.2.1, v.property.2.2⟩

private theorem sourceTransitionBackground_eq
    (α β : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    α.add (nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)) =
      β := by
  apply Function.LeftInverse.injective (fun θ ↦ sourceAtlasNativeForm_roundTrip θ)
  simp only [sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]
  abel

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β γ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual original positive union, used as a subtype rather than
replaced by a new weaker curve predicate. -/
abbrev SourcePositiveIModelTestCurve (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) :=
  {Γ : SourceTestCurve α // Γ ∈ SourceIModelTestCurvesPositive α}

omit [BorelSpace M] [ConnectedSpace M] in
private theorem castBackground_isIModel (Γ : SourceTestCurve α)
    (hΓ : SourceTestCurveIsIModel Γ) (h : α = β) :
    SourceTestCurveIsIModel (Γ.castBackground h) := by
  cases h
  exact hΓ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Semipositivity of the actual difference keeps the same genuine original
potential in the target background. -/
theorem sourceThetaPSH_of_semipositive_difference
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u) :
    (ofFixedModel n M).IsThetaPSH β u := by
  have hη : (atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α))).val.IsSemipositive := by
    simpa only [sourceNativeAtlasForm_roundTrip] using hαβ
  simpa only [sourceTransitionBackground_eq] using
    sourceThetaPSH_add_semipositive
      (nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)) hη hu

/-- The actual transition to any ordered closed background. Every genuine
output field is manufactured by the existing semipositive I-projection. -/
def sourceIModelTestCurveTransition (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) : SourcePositiveIModelTestCurve β := by
  let η := nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)
  have hη : (atlasClosedFormToNative η).val.IsSemipositive := by
    simpa only [η, sourceNativeAtlasForm_roundTrip] using hαβ
  let Δ := Γ.val.iEnvelopeBackgroundProjection omega η hη
  have hform : α.add η = β := sourceTransitionBackground_eq α β
  refine ⟨Δ.castBackground hform, ?_⟩
  apply (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
  exact castBackground_isIModel Δ
    (Γ.val.iEnvelopeBackgroundProjection_isIModel omega η hη) hform

/-- Every transition retains the exact original finite real cutoff. -/
theorem sourceIModelTestCurveTransition_max (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) :
    (sourceIModelTestCurveTransition omega hαβ Γ).val.max = Γ.val.max := by
  simp only [sourceIModelTestCurveTransition, SourceTestCurve.castBackground_max,
    SourceTestCurve.iEnvelopeBackgroundProjection_max]

/-- Every open slice is the literal original all-competitor I-envelope. -/
theorem sourceIModelTestCurveTransition_potential (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) (r : ℝ) (hr : r < Γ.val.max)
    (hs : r < (sourceIModelTestCurveTransition omega hαβ Γ).val.max) :
    (sourceIModelTestCurveTransition omega hαβ Γ).val.potential ⟨r, hs⟩ =
      sourceIEnvelope β (Γ.val.potential ⟨r, hr⟩) := by
  let η := nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)
  have hη : (atlasClosedFormToNative η).val.IsSemipositive := by
    simpa only [η, sourceNativeAtlasForm_roundTrip] using hαβ
  let Δ := Γ.val.iEnvelopeBackgroundProjection omega η hη
  have hform : α.add η = β := sourceTransitionBackground_eq α β
  change (Δ.castBackground hform).potential ⟨r, hs⟩ = _
  rw [SourceTestCurve.castBackground_potential Δ hform r hr hs]
  change sourceIEnvelope
    (α.add (nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)))
    (Γ.val.potential ⟨r, hr⟩) = _
  rw [sourceTransitionBackground_eq]

/-- The identity transition is the same entire original I-model curve. -/
theorem sourceIModelTestCurveTransition_refl (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve α) :
    sourceIModelTestCurveTransition omega
      (closedDifference_semipositive_refl (atlasClosedFormToNative α)) Γ = Γ := by
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact sourceIModelTestCurveTransition_max omega _ Γ
  · intro r hr hs
    rw [sourceIModelTestCurveTransition_potential omega _ Γ r hs hr]
    exact ((sourceIModel_iff_native α _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices omega Γ.val).mp Γ.property)
        ⟨r, hs⟩)).2.symm

/-- Composition is proved through actual multiplier equivalence and the
full normalized competitor families, without a composition certificate. -/
theorem sourceIModelTestCurveTransition_comp (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (hβγ : (atlasClosedFormToNative γ - atlasClosedFormToNative β).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) :
    sourceIModelTestCurveTransition omega hβγ
      (sourceIModelTestCurveTransition omega hαβ Γ) =
    sourceIModelTestCurveTransition omega
      (closedDifference_semipositive_trans hαβ hβγ) Γ := by
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · simp only [sourceIModelTestCurveTransition_max]
  · intro r hr hs
    have hrΓ : r < Γ.val.max := by
      simpa only [sourceIModelTestCurveTransition_max] using hs
    have hrβ : r < (sourceIModelTestCurveTransition omega hαβ Γ).val.max := by
      simpa only [sourceIModelTestCurveTransition_max] using hrΓ
    rw [sourceIModelTestCurveTransition_potential omega hβγ _ r hrβ hr,
      sourceIModelTestCurveTransition_potential omega hαβ Γ r hrΓ hrβ,
      sourceIModelTestCurveTransition_potential omega _ Γ r hrΓ hs]
    exact (sourceIEnvelope_eq_of_equivalent
      (sourceIEquivalent_iEnvelope
        (sourceThetaPSH_of_semipositive_difference hαβ (Γ.val.thetaPSH ⟨r, hrΓ⟩)))).symm

/-- A change of geometric presentation leaves every original open slice
function unchanged, including its extended-real poles. -/
theorem sourceIModelTestCurveTransition_potential_of_geometricallyEq
    (omega : KahlerBackground n M)
    (h : (atlasClosedFormToNative α).val.GeometricallyEq (atlasClosedFormToNative β).val)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) (r : ℝ) (hr : r < Γ.val.max)
    (hs : r < (sourceIModelTestCurveTransition omega hαβ Γ).val.max) :
    (sourceIModelTestCurveTransition omega hαβ Γ).val.potential ⟨r, hs⟩ =
      Γ.val.potential ⟨r, hr⟩ := by
  rw [sourceIModelTestCurveTransition_potential omega hαβ Γ r hr hs,
    ← sourceIEnvelope_geometricallyEq h]
  exact ((sourceIModel_iff_native α _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices omega Γ.val).mp Γ.property)
      ⟨r, hr⟩)).2.symm

/-- The auxiliary Kähler proof resource changes no transition data. -/
theorem sourceIModelTestCurveTransition_ambient_independent
    (omega omega' : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) :
    sourceIModelTestCurveTransition omega hαβ Γ =
      sourceIModelTestCurveTransition omega' hαβ Γ := by
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · simp only [sourceIModelTestCurveTransition_max]
  · intro r hr hs
    have hrΓ : r < Γ.val.max := by
      simpa only [sourceIModelTestCurveTransition_max] using hr
    rw [sourceIModelTestCurveTransition_potential omega hαβ Γ r hrΓ hr,
      sourceIModelTestCurveTransition_potential omega' hαβ Γ r hrΓ hs]

/-- Geometrically equal presentations give canonical inverse bijections of
the actual positive I-model curve classes. -/
def sourceIModelTestCurvePresentationEquiv (omega : KahlerBackground n M)
    (h : (atlasClosedFormToNative α).val.GeometricallyEq
      (atlasClosedFormToNative β).val) :
    SourcePositiveIModelTestCurve α ≃ SourcePositiveIModelTestCurve β where
  toFun := sourceIModelTestCurveTransition omega
    (closedDifference_semipositive_of_geometricallyEq h)
  invFun := sourceIModelTestCurveTransition omega
    (closedDifference_semipositive_of_geometricallyEq h.symm)
  left_inv Γ := by
    rw [sourceIModelTestCurveTransition_comp, sourceIModelTestCurveTransition_refl]
  right_inv Γ := by
    rw [sourceIModelTestCurveTransition_comp, sourceIModelTestCurveTransition_refl]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem castBackground_limit (Γ : SourceTestCurve α) (h : α = β) :
    sourceTestCurveLimit (Γ.castBackground h).toSourceTestCurvePredata =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata := by
  cases h
  rfl

/-- The actual entire spatial limit is the I-envelope of the same original
limit function, with its genuine positive mass already produced. -/
theorem sourceIModelTestCurveTransition_limit (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourcePositiveIModelTestCurve α) :
    sourceTestCurveLimit (sourceIModelTestCurveTransition omega hαβ Γ).val.toSourceTestCurvePredata =
      sourceIEnvelope β (sourceTestCurveLimit Γ.val.toSourceTestCurvePredata) := by
  let η := nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)
  have hη : (atlasClosedFormToNative η).val.IsSemipositive := by
    simpa only [η, sourceNativeAtlasForm_roundTrip] using hαβ
  let Δ := Γ.val.iEnvelopeBackgroundProjection omega η hη
  have hform : α.add η = β := sourceTransitionBackground_eq α β
  change sourceTestCurveLimit (Δ.castBackground hform).toSourceTestCurvePredata = _
  rw [castBackground_limit]
  exact (Γ.val.iEnvelopeBackgroundProjection_limit omega η hη).trans
    (congrArg (fun σ ↦ sourceIEnvelope σ
      (sourceTestCurveLimit Γ.val.toSourceTestCurvePredata)) hform)

/-- The actual enlarged background at a geometric Kähler index. -/
def sourceNAComponentBackground (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : SourceKahlerForm n M) : AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  sourceTestCurveEnlargedBackground (sourceKahlerFormRepresentative ω) θ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The chosen component background has precisely the original full sum. -/
theorem sourceNAComponentBackground_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (ω : SourceKahlerForm n M) :
    atlasClosedFormToNative (sourceNAComponentBackground θ ω) =
      atlasClosedFormToNative θ + (sourceKahlerFormRepresentative ω).form :=
  sourceTestCurveEnlargedBackground_native _ _

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Every original augmentation is semipositive relative to the base. -/
theorem sourceNAComponentBackground_positive
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (ω : SourceKahlerForm n M) :
    (atlasClosedFormToNative (sourceNAComponentBackground θ ω) -
      atlasClosedFormToNative θ).val.IsSemipositive := by
  rw [sourceNAComponentBackground_native, add_sub_cancel_left]
  exact (sourceKahlerFormRepresentative ω).isSemipositive

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The index order is the actual semipositive difference of the two
augmented backgrounds, retaining the entire base form. -/
theorem sourceNAComponentBackground_difference
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {ω η : SourceKahlerForm n M} (h : sourceKahlerFormLE ω η) :
    (atlasClosedFormToNative (sourceNAComponentBackground θ η) -
      atlasClosedFormToNative (sourceNAComponentBackground θ ω)).val.IsSemipositive := by
  rw [sourceNAComponentBackground_native, sourceNAComponentBackground_native]
  have heq : (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative η).form) -
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative ω).form) =
      (sourceKahlerFormRepresentative η).form - (sourceKahlerFormRepresentative ω).form := by
    abel
  rw [heq]
  exact h

/-- Whole original set-valued inverse-system definition. The common cutoff
is proved below, rather than imposed as an additional input field. -/
structure SourceNAPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) where
  component : ∀ ω : SourceKahlerForm n M,
    SourcePositiveIModelTestCurve (sourceNAComponentBackground θ ω)
  compatible : ∀ (ω η : SourceKahlerForm n M) (h : sourceKahlerFormLE ω η),
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative η)
      (sourceNAComponentBackground_difference θ h) (component ω) = component η

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Equality of the actual component curves identifies inverse-system
elements; there is no separate quotient or extra geometric certificate. -/
@[ext] theorem SourceNAPotential.ext {Γ Δ : SourceNAPotential θ}
    (h : ∀ ω : SourceKahlerForm n M, Γ.component ω = Δ.component ω) : Γ = Δ := by
  cases Γ with
  | mk c hc =>
    cases Δ with
    | mk d hd =>
      have hcd : c = d := funext h
      subst d
      rfl

/-- Actual compatibility with a common larger physical form proves the
original cutoff is independent of the Kähler index. -/
theorem SourceNAPotential.component_max_eq (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm n M) : (Γ.component ω).val.max = (Γ.component η).val.max := by
  let ζ := sourceKahlerFormCommonUpper ω η
  have hω := congrArg (fun Δ ↦ Δ.val.max)
    (Γ.compatible ω ζ (sourceKahlerFormLE_commonUpper_left ω η))
  have hη := congrArg (fun Δ ↦ Δ.val.max)
    (Γ.compatible η ζ (sourceKahlerFormLE_commonUpper_right ω η))
  simp only [sourceIModelTestCurveTransition_max] at hω hη
  exact hω.trans hη.symm

/-- Read the original common real cutoff using any supplied Kähler form. -/
def sourceNAPotentialCutoff (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) : ℝ :=
  (Γ.component (sourceKahlerFormOfBackground omega)).val.max

theorem sourceNAPotentialCutoff_eq_component (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n M) :
    sourceNAPotentialCutoff omega Γ = (Γ.component ω).val.max :=
  Γ.component_max_eq _ _

theorem sourceNAPotentialCutoff_independent (omega omega' : KahlerBackground n M)
    (Γ : SourceNAPotential θ) : sourceNAPotentialCutoff omega Γ = sourceNAPotentialCutoff omega' Γ :=
  Γ.component_max_eq _ _

/-- The original natural map manufactures every actual positive I-model
component and its whole inverse-system compatibility. -/
def sourcePositiveTestCurveToNA (Γ : SourcePositiveIModelTestCurve θ) : SourceNAPotential θ where
  component ω := sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) Γ
  compatible ω η h := by
    rw [sourceIModelTestCurveTransition_ambient_independent
      (sourceKahlerFormRepresentative ω) (sourceKahlerFormRepresentative η)
      (sourceNAComponentBackground_positive θ ω) Γ]
    exact sourceIModelTestCurveTransition_comp (sourceKahlerFormRepresentative η)
      (sourceNAComponentBackground_positive θ ω) (sourceNAComponentBackground_difference θ h) Γ

/-- Every image component retains the original exact real cutoff. -/
theorem sourcePositiveTestCurveToNA_max (Γ : SourcePositiveIModelTestCurve θ)
    (ω : SourceKahlerForm n M) : ((sourcePositiveTestCurveToNA Γ).component ω).val.max = Γ.val.max :=
  sourceIModelTestCurveTransition_max (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) Γ

/-- The whole original displayed component formula, at every original open
parameter and every original spatial point, including poles. -/
theorem sourcePositiveTestCurveToNA_potential (Γ : SourcePositiveIModelTestCurve θ)
    (ω : SourceKahlerForm n M) (r : ℝ) (hr : r < Γ.val.max)
    (hs : r < ((sourcePositiveTestCurveToNA Γ).component ω).val.max) :
    ((sourcePositiveTestCurveToNA Γ).component ω).val.potential ⟨r, hs⟩ =
      sourceIEnvelope (sourceNAComponentBackground θ ω) (Γ.val.potential ⟨r, hr⟩) :=
  sourceIModelTestCurveTransition_potential (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) Γ r hr hs

theorem sourcePositiveTestCurveToNA_cutoff (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA Γ) = Γ.val.max :=
  sourcePositiveTestCurveToNA_max Γ _

omit [BorelSpace M] [ConnectedSpace M] in
private theorem curve_potential_eq_of_eq {Γ Δ : SourceTestCurve α} (h : Γ = Δ)
    (r : ℝ) (hr : r < Γ.max) (hs : r < Δ.max) :
    Γ.potential ⟨r, hr⟩ = Δ.potential ⟨r, hs⟩ := by
  cases h
  rfl

/-- Equality at a single actual Kähler component already identifies the
whole original positive I-model test curves. -/
theorem sourcePositiveTestCurveToNA_component_injective (ω : SourceKahlerForm n M) :
    Function.Injective (fun Γ : SourcePositiveIModelTestCurve θ ↦
      (sourcePositiveTestCurveToNA Γ).component ω) := by
  intro Γ Δ h
  apply Subtype.ext
  have hmax : Γ.val.max = Δ.val.max := by
    have hcut := congrArg (fun C ↦ C.val.max) h
    simpa only [sourcePositiveTestCurveToNA_max] using hcut
  apply SourceTestCurve.ext_of_max_potential Γ.val Δ.val hmax
  intro r hr hs
  have hrΓ : r < ((sourcePositiveTestCurveToNA Γ).component ω).val.max := by
    rwa [sourcePositiveTestCurveToNA_max]
  have hrΔ : r < ((sourcePositiveTestCurveToNA Δ).component ω).val.max := by
    rwa [sourcePositiveTestCurveToNA_max]
  have hpot := curve_potential_eq_of_eq (congrArg Subtype.val h) r hrΓ hrΔ
  rw [sourcePositiveTestCurveToNA_potential Γ ω r hr hrΓ,
    sourcePositiveTestCurveToNA_potential Δ ω r hs hrΔ] at hpot
  have hΓ := sourceIEquivalent_iEnvelope
    (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ ω)
      (Γ.val.thetaPSH ⟨r, hr⟩))
  have hΔ := sourceIEquivalent_iEnvelope
    (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ ω)
      (Δ.val.thetaPSH ⟨r, hs⟩))
  rw [hpot] at hΓ
  have hI := sourceIEquivalent_trans hΓ (sourceIEquivalent_symm hΔ)
  have hmΓ := (sourceIModel_iff_native θ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative ω) Γ.val).mp
      Γ.property) ⟨r, hr⟩)
  have hmΔ := (sourceIModel_iff_native θ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative ω) Δ.val).mp
      Δ.property) ⟨r, hs⟩)
  exact hmΓ.2.trans ((sourceIEnvelope_eq_of_equivalent hI).trans hmΔ.2.symm)

/-- Whole original prop:NAposNAemb. The original Kähler standing geometry
supplies one actual index at which to evaluate the manufactured system. -/
theorem sourcePositiveTestCurveToNA_injective (omega : KahlerBackground n M) :
    Function.Injective (sourcePositiveTestCurveToNA (θ := θ)) := by
  intro Γ Δ h
  exact sourcePositiveTestCurveToNA_component_injective (sourceKahlerFormOfBackground omega)
    (congrArg (fun Ξ ↦ Ξ.component (sourceKahlerFormOfBackground omega)) h)

end SGPT.PSH.VariableComplexAtlas
