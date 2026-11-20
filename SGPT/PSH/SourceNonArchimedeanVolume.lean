import SGPT.PSH.SourceNonArchimedeanPotentials
import SGPT.PSH.SourceIModelGood
import SGPT.PSH.SourceIGoodBackground
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.Foundations.Analysis.Pending.AnalyticGluingProof
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Actual volume of every original non-Archimedean potential

The complete mathematical route is `source-non-archimedean-volume.tex`.
The geometric index and original inverse-system objects are unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] in
/-- Equality of actual potential functions retains the same genuine measure. -/
theorem sourcePotentialMass_congr {u v : M → EReal} (h : u = v)
    (hu : (ofFixedModel n M).IsThetaPSH α u)
    (hv : (ofFixedModel n M).IsThetaPSH α v) :
    sourcePotentialNonPluripolarMeasure α u hu univ =
      sourcePotentialNonPluripolarMeasure α v hv univ := by
  cases h
  rfl

/-- Geometric presentation changes preserve the actual diagonal mass.
The existing full measure representative-change theorem is used with zero correction. -/
theorem sourcePotentialMass_geometricallyEq
    (h : (atlasClosedFormToNative α).val.GeometricallyEq
      (atlasClosedFormToNative β).val)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u)
    (hv : (ofFixedModel n M).IsThetaPSH β u) :
    sourcePotentialNonPluripolarMeasure β u hv univ =
      sourcePotentialNonPluripolarMeasure α u hu univ := by
  have he : ∀ (_i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → (atlasClosedFormToNative β).val.coeff e z =
        (atlasClosedFormToNative α).val.coeff e z + smoothDDC (fun _ => (0 : ℝ)) z := by
    intro _ e z hz
    rw [GlobalPotentialTransforms.smoothDDC_const, add_zero]
    exact (h e hz).symm
  have hm := MixedMass.globalMixedMass_changeRepresentative
    (θ := fun _ : Fin n => atlasClosedFormToNative α)
    (η := fun _ => atlasClosedFormToNative β) (u := fun _ => u)
    (f := fun _ _ => (0 : ℝ)) (fun _ _ => contDiffOn_const) he
    (fun _ => ((isThetaPSH_iff_nativeThetaPotential α u).mp hu).1)
  simpa only [EReal.coe_zero, sub_zero, sourcePotentialNonPluripolarMeasure,
    diagonalPotentialMeasure, MixedMass.globalMixedMass] using hm

/-- Adding an actual closed semipositive difference increases the same genuine mass. -/
theorem sourcePotentialMass_mono_background
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u) :
    sourcePotentialNonPluripolarMeasure α u hu univ ≤
      sourcePotentialNonPluripolarMeasure β u
        (sourceThetaPSH_of_semipositive_difference hαβ hu) univ := by
  have hform : atlasClosedFormToNative α +
      (1 : ℝ) • (atlasClosedFormToNative β - atlasClosedFormToNative α) =
        atlasClosedFormToNative β := by module
  have hv : IsThetaPshPotential (atlasClosedFormToNative α +
      (1 : ℝ) • (atlasClosedFormToNative β - atlasClosedFormToNative α)).val u := by
    rw [hform]
    exact (isThetaPSH_iff_nativeThetaPotential β u).mp
      (sourceThetaPSH_of_semipositive_difference hαβ hu)
  have hm := AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
    hαβ zero_lt_one ((isThetaPSH_iff_nativeThetaPotential α u).mp hu) hv
  simpa only [hform, sourcePotentialNonPluripolarMeasure, diagonalPotentialMass] using hm

variable [ConnectedSpace M]

/-- Genuine positive I-models retain the literal ordinary/I envelope identity
and the same actual larger-background mass under every ordered transition. -/
theorem sourceIModel_transition_envelope_and_mass (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    {u : M → EReal} (hu : sourceIModel α u)
    (hp : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ) :
    sourceSingularityEnvelope β u = sourceIEnvelope β u ∧
      sourcePotentialNonPluripolarMeasure β (sourceIEnvelope β u)
          (isThetaPSH_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference hαβ hu.1))
          univ =
        sourcePotentialNonPluripolarMeasure β u
          (sourceThetaPSH_of_semipositive_difference hαβ hu.1) univ := by
  have hv := sourceThetaPSH_of_semipositive_difference hαβ hu.1
  have hp' := hp.trans_le (sourcePotentialMass_mono_background hαβ hu.1)
  have hg := (sourceIGoodWith_iff_positive_background omega hu.1 hv hp hp').mp
    (sourceIModel_positive_iGood α u hu hp).1
  refine ⟨hg.2, ?_⟩
  exact (sourcePotentialMass_congr hg.2.symm _ (sourceOrdinaryEnvelope_genuine hv)).trans
    (sourceOrdinaryEnvelope_diagonalMass_eq omega hv)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The literal chosen background has the same geometric coefficients as θ+ω. -/
theorem sourceNAComponentBackground_geometricallyEq (ω : KahlerBackground n M) :
    (atlasClosedFormToNative
      (sourceNAComponentBackground θ (sourceKahlerFormOfBackground ω))).val.GeometricallyEq
      (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω θ)).val := by
  rw [sourceNAComponentBackground_native, sourceTestCurveEnlargedBackground_native]
  intro e z hz
  simp only [ClosedRealOneOneForm.coeff_add,
    sourceKahlerFormRepresentative_geometricallyEq ω e hz]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem realizedDifference (ω : KahlerBackground n M) :
    (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω θ) -
      atlasClosedFormToNative (sourceNAComponentBackground θ
        (sourceKahlerFormOfBackground ω))).val.IsSemipositive := by
  intro e z hz v
  have h := sourceNAComponentBackground_geometricallyEq (θ := θ) ω e hz
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, h, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply]
  exact le_of_eq (add_neg_cancel _).symm

/-- An actual component in the literal full native background θ+ω.
Only the existing canonical presentation equivalence is used. -/
def SourceNAPotential.realizedComponent (Γ : SourceNAPotential θ) (ω : KahlerBackground n M) :
    SourcePositiveIModelTestCurve (sourceTestCurveEnlargedBackground ω θ) :=
  sourceIModelTestCurvePresentationEquiv ω (sourceNAComponentBackground_geometricallyEq ω)
    (Γ.component (sourceKahlerFormOfBackground ω))

theorem SourceNAPotential.realizedComponent_max (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) :
    (Γ.realizedComponent ω).val.max =
      (Γ.component (sourceKahlerFormOfBackground ω)).val.max :=
  sourceIModelTestCurveTransition_max ω (realizedDifference ω) _

/-- Every open function is unchanged by the genuine presentation transport. -/
theorem SourceNAPotential.realizedComponent_potential (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (r : ℝ)
    (hr : r < (Γ.component (sourceKahlerFormOfBackground ω)).val.max)
    (hs : r < (Γ.realizedComponent ω).val.max) :
    (Γ.realizedComponent ω).val.potential ⟨r, hs⟩ =
      (Γ.component (sourceKahlerFormOfBackground ω)).val.potential ⟨r, hr⟩ :=
  sourceIModelTestCurveTransition_potential_of_geometricallyEq ω
    (sourceNAComponentBackground_geometricallyEq ω) (realizedDifference ω) _ r hr hs

/-- The spatial limit is the same actual function, including all poles. -/
theorem SourceNAPotential.realizedComponent_limit (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) :
    sourceTestCurveLimit (Γ.realizedComponent ω).val.toSourceTestCurvePredata =
      sourceTestCurveLimit
        (Γ.component (sourceKahlerFormOfBackground ω)).val.toSourceTestCurvePredata := by
  rw [show sourceTestCurveLimit (Γ.realizedComponent ω).val.toSourceTestCurvePredata =
    sourceIEnvelope (sourceTestCurveEnlargedBackground ω θ)
      (sourceTestCurveLimit
        (Γ.component (sourceKahlerFormOfBackground ω)).val.toSourceTestCurvePredata) from
      sourceIModelTestCurveTransition_limit ω (realizedDifference ω) _]
  rw [← sourceIEnvelope_geometricallyEq (sourceNAComponentBackground_geometricallyEq ω)]
  exact ((Γ.component (sourceKahlerFormOfBackground ω)).val.limit_iModel ω
    ((sourceIModelTestCurvesPositive_iff_slices ω _).mp
      (Γ.component (sourceKahlerFormOfBackground ω)).property)).2.symm

/-- The original actual component-limit mass at a geometric Kähler index. -/
def sourceNAComponentMass (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n M) : ℝ≥0∞ :=
  sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ ω)
    (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata)
    (Γ.component ω).val.limit_thetaPSH univ

theorem sourceNAComponentMass_positive (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n M) : 0 < sourceNAComponentMass Γ ω :=
  (Γ.component ω).val.positiveLimitMass

theorem sourceNAComponentMass_lt_top (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n M) : sourceNAComponentMass Γ ω < ⊤ :=
  MixedMass.globalMixedMass_lt_top omega
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential _ _).mp
      (Γ.component ω).val.limit_thetaPSH).1)

/-- Chosen geometric representatives and literal θ+ω give the SAME actual mass. -/
theorem sourceNAComponentMass_realized (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) :
    sourceNAComponentMass Γ (sourceKahlerFormOfBackground ω) =
      sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ω θ)
        (sourceTestCurveLimit (Γ.realizedComponent ω).val.toSourceTestCurvePredata)
        (Γ.realizedComponent ω).val.limit_thetaPSH univ := by
  unfold sourceNAComponentMass
  exact (sourcePotentialMass_geometricallyEq (sourceNAComponentBackground_geometricallyEq ω)
    (Γ.component (sourceKahlerFormOfBackground ω)).val.limit_thetaPSH
    ((Γ.realizedComponent_limit ω) ▸ (Γ.realizedComponent ω).val.limit_thetaPSH)).symm.trans
      (sourcePotentialMass_congr (Γ.realizedComponent_limit ω).symm _ _)

/-- Whole original prop:testcminftyPrela for the same actual component limits. -/
theorem SourceNAPotential.component_limit_transition (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm n M} (h : sourceKahlerFormLE ω η) :
    sourceSingularityEnvelope (sourceNAComponentBackground θ η)
        (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) =
      sourceIEnvelope (sourceNAComponentBackground θ η)
        (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) ∧
    sourceIEnvelope (sourceNAComponentBackground θ η)
        (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) =
      sourceTestCurveLimit (Γ.component η).val.toSourceTestCurvePredata := by
  have hm := (Γ.component ω).val.limit_iModel (sourceKahlerFormRepresentative η)
    ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative η) _).mp
      (Γ.component ω).property)
  refine ⟨(sourceIModel_transition_envelope_and_mass (sourceKahlerFormRepresentative η)
    (sourceNAComponentBackground_difference θ h) hm (Γ.component ω).val.positiveLimitMass).1, ?_⟩
  rw [← Γ.compatible ω η h]
  exact (sourceIModelTestCurveTransition_limit _ _ _).symm

/-- The actual component-limit masses are monotone in the physical Kähler order. -/
theorem sourceNAComponentMass_mono (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm n M} (h : sourceKahlerFormLE ω η) :
    sourceNAComponentMass Γ ω ≤ sourceNAComponentMass Γ η := by
  have hi := (Γ.component ω).val.limit_iModel (sourceKahlerFormRepresentative η)
    ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative η) _).mp
      (Γ.component ω).property)
  have he := (sourceIModel_transition_envelope_and_mass (sourceKahlerFormRepresentative η)
    (sourceNAComponentBackground_difference θ h) hi (Γ.component ω).val.positiveLimitMass).2
  have hlim := (Γ.component_limit_transition h).2
  have hmass := sourcePotentialMass_mono_background
    (sourceNAComponentBackground_difference θ h) hi.1
  exact hmass.trans_eq (he.symm.trans (sourcePotentialMass_congr hlim _ _))

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Actual common physical lower forms make the original reverse index directed. -/
theorem sourceKahlerForm_commonLower (ω η : SourceKahlerForm n M) :
    ∃ ζ : SourceKahlerForm n M, sourceKahlerFormLE ζ ω ∧ sourceKahlerFormLE ζ η := by
  obtain ⟨ζ, hω, hη⟩ := AnalyticGluingProof.exists_kahlerBackground_le_both
    (sourceKahlerFormRepresentative ω) (sourceKahlerFormRepresentative η)
  refine ⟨sourceKahlerFormOfBackground ζ, ?_, ?_⟩
  · simpa only [sourceKahlerFormRepresentative_class] using
      (sourceKahlerFormLE_ofBackground_iff ζ (sourceKahlerFormRepresentative ω)).mpr hω
  · simpa only [sourceKahlerFormRepresentative_class] using
      (sourceKahlerFormLE_ofBackground_iff ζ (sourceKahlerFormRepresentative η)).mpr hη

/-- Precisely the existing physical geometric order, used to name the original net. -/
@[instance_reducible]
def sourceKahlerFormPreorder : Preorder (SourceKahlerForm n M) where
  le := sourceKahlerFormLE
  le_refl := sourceKahlerFormLE_refl
  le_trans := fun _ _ _ => sourceKahlerFormLE_trans

/-- The original filter tending to smaller physical Kähler forms. -/
def sourceNAKahlerFilter : Filter (SourceKahlerForm n M) :=
  @Filter.atBot _ sourceKahlerFormPreorder

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Standing Kähler geometry and actual common lower forms make this a genuine net filter. -/
theorem sourceNAKahlerFilter_neBot (omega : KahlerBackground n M) :
    (sourceNAKahlerFilter (n := n) (M := M)).NeBot := by
  let := sourceKahlerFormPreorder (n := n) (M := M)
  exact Filter.atBot_neBot_iff.mpr
    ⟨⟨sourceKahlerFormOfBackground omega⟩, ⟨fun ω η => sourceKahlerForm_commonLower ω η⟩⟩

/-- Original volume on ALL existing systems; zero is permitted and no metric is appended. -/
def sourceNAVolume (Γ : SourceNAPotential θ) : ℝ≥0∞ := ⨅ ω, sourceNAComponentMass Γ ω

theorem sourceNAVolume_le_component (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n M) :
    sourceNAVolume Γ ≤ sourceNAComponentMass Γ ω := iInf_le _ ω

/-- Actual compact Kähler mass finiteness puts the all-system volume in [0,∞). -/
theorem sourceNAVolume_lt_top (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) :
    sourceNAVolume Γ < ⊤ :=
  (sourceNAVolume_le_component Γ (sourceKahlerFormOfBackground omega)).trans_lt
    (sourceNAComponentMass_lt_top omega Γ _)

/-- The entire original decreasing net converges to this finite all-index infimum. -/
theorem sourceNAVolume_original_net (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) :
    (sourceNAKahlerFilter (n := n) (M := M)).NeBot ∧
      sourceNAVolume Γ < ⊤ ∧
      Tendsto (sourceNAComponentMass Γ) sourceNAKahlerFilter (𝓝 (sourceNAVolume Γ)) := by
  refine ⟨sourceNAKahlerFilter_neBot omega, sourceNAVolume_lt_top omega Γ, ?_⟩
  let := sourceKahlerFormPreorder (n := n) (M := M)
  exact tendsto_atBot_iInf (fun _ _ h => sourceNAComponentMass_mono Γ h)

/-- Image-component mass is the mass of the SAME original limit in that background. -/
theorem sourceNAComponentMass_embedding (G : SourcePositiveIModelTestCurve θ)
    (ω : SourceKahlerForm n M) :
    sourceNAComponentMass (sourcePositiveTestCurveToNA G) ω =
      sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ ω)
        (sourceTestCurveLimit G.val.toSourceTestCurvePredata)
        (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ ω)
          G.val.limit_thetaPSH) univ := by
  have hi := G.val.limit_iModel (sourceKahlerFormRepresentative ω)
    ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative ω) _).mp G.property)
  have hm := (sourceIModel_transition_envelope_and_mass (sourceKahlerFormRepresentative ω)
    (sourceNAComponentBackground_positive θ ω) hi G.val.positiveLimitMass).2
  exact (sourcePotentialMass_congr
    (sourceIModelTestCurveTransition_limit (sourceKahlerFormRepresentative ω)
      (sourceNAComponentBackground_positive θ ω) G) _ _).trans hm

/-- In a literal θ+ω presentation the same image mass is still the original limit mass. -/
theorem sourceNAComponentMass_embedding_literal (G : SourcePositiveIModelTestCurve θ)
    (ω : KahlerBackground n M) :
    sourceNAComponentMass (sourcePositiveTestCurveToNA G) (sourceKahlerFormOfBackground ω) =
      sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ω θ)
        (sourceTestCurveLimit G.val.toSourceTestCurvePredata)
        (sourceThetaPSH_add_kahler ω G.val.limit_thetaPSH) univ := by
  exact (sourceNAComponentMass_embedding G _).trans
    (sourcePotentialMass_geometricallyEq (sourceNAComponentBackground_geometricallyEq ω)
      (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ _)
        G.val.limit_thetaPSH) (sourceThetaPSH_add_kahler ω G.val.limit_thetaPSH)).symm

omit [BorelSpace M] [ConnectedSpace M] in
private theorem positiveCurve_potential_congr {C D : SourceTestCurve α} (h : C = D)
    (r : ℝ) (hr : r < C.max) (hs : r < D.max) :
    C.potential ⟨r, hr⟩ = D.potential ⟨r, hs⟩ := by
  cases h
  rfl

/-- Actual compatibility is retained in literal θ+ω backgrounds, at every open slice. -/
theorem SourceNAPotential.realizedComponent_potential_transition (Γ : SourceNAPotential θ)
    {ω η : KahlerBackground n M} (h : (η.form - ω.form).val.IsSemipositive)
    (r : ℝ) (hr : r < (Γ.realizedComponent ω).val.max)
    (hs : r < (Γ.realizedComponent η).val.max) :
    (Γ.realizedComponent η).val.potential ⟨r, hs⟩ =
      sourceIEnvelope (sourceTestCurveEnlargedBackground η θ)
        ((Γ.realizedComponent ω).val.potential ⟨r, hr⟩) := by
  have hωη := (sourceKahlerFormLE_ofBackground_iff ω η).mpr h
  have hrω : r < (Γ.component (sourceKahlerFormOfBackground ω)).val.max := by
    simpa only [Γ.realizedComponent_max] using hr
  have hrη : r < (Γ.component (sourceKahlerFormOfBackground η)).val.max := by
    simpa only [Γ.realizedComponent_max] using hs
  have hrT : r < (sourceIModelTestCurveTransition
      (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground η))
      (sourceNAComponentBackground_difference θ hωη)
      (Γ.component (sourceKahlerFormOfBackground ω))).val.max := by
    simpa only [sourceIModelTestCurveTransition_max] using hrω
  have he := positiveCurve_potential_congr
    (congrArg Subtype.val (Γ.compatible _ _ hωη)) r hrT hrη
  rw [sourceIModelTestCurveTransition_potential _ _ _ r hrω hrT] at he
  rw [Γ.realizedComponent_potential η r hrη hs,
    Γ.realizedComponent_potential ω r hrω hr,
    ← sourceIEnvelope_geometricallyEq (sourceNAComponentBackground_geometricallyEq η)]
  exact he.symm

/-- The same exact compatibility holds for the actual spatial supremum limits. -/
theorem SourceNAPotential.realizedComponent_limit_transition (Γ : SourceNAPotential θ)
    {ω η : KahlerBackground n M} (h : (η.form - ω.form).val.IsSemipositive) :
    sourceTestCurveLimit (Γ.realizedComponent η).val.toSourceTestCurvePredata =
      sourceIEnvelope (sourceTestCurveEnlargedBackground η θ)
        (sourceTestCurveLimit (Γ.realizedComponent ω).val.toSourceTestCurvePredata) := by
  rw [Γ.realizedComponent_limit η, Γ.realizedComponent_limit ω,
    ← sourceIEnvelope_geometricallyEq (sourceNAComponentBackground_geometricallyEq η)]
  exact (Γ.component_limit_transition ((sourceKahlerFormLE_ofBackground_iff ω η).mpr h)).2.symm

/-- Any literal presentation reads exactly the original common real cutoff. -/
theorem SourceNAPotential.realizedComponent_max_eq_cutoff (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : KahlerBackground n M) :
    (Γ.realizedComponent ω).val.max = sourceNAPotentialCutoff omega Γ :=
  (Γ.realizedComponent_max ω).trans (sourceNAPotentialCutoff_eq_component omega Γ _).symm

/-- The actual realized open slices, reindexed only by the proved common real cutoff. -/
def sourceNACommonSlice (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) : M → EReal :=
  (Γ.realizedComponent ω).val.potential
    ⟨τ.val, by rw [Γ.realizedComponent_max_eq_cutoff omega ω]; exact τ.property⟩

theorem sourceNACommonSlice_thetaPSH (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    (ofFixedModel n M).IsThetaPSH (sourceTestCurveEnlargedBackground ω θ)
      (sourceNACommonSlice omega Γ ω τ) :=
  (Γ.realizedComponent ω).val.thetaPSH _

theorem sourceNACommonSlice_model (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    SourceModelPotential (sourceTestCurveEnlargedBackground ω θ)
      (sourceNACommonSlice omega Γ ω τ) :=
  (Γ.realizedComponent ω).val.slice_model omega _

theorem sourceNACommonSlice_iModel (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIModel (sourceTestCurveEnlargedBackground ω θ) (sourceNACommonSlice omega Γ ω τ) :=
  (sourceIModel_iff_native _ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices omega _).mp
      (Γ.realizedComponent ω).property) _)

theorem sourceNACommonSlice_transition (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {ω η : KahlerBackground n M} (h : (η.form - ω.form).val.IsSemipositive)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceNACommonSlice omega Γ η τ =
      sourceIEnvelope (sourceTestCurveEnlargedBackground η θ)
        (sourceNACommonSlice omega Γ ω τ) :=
  Γ.realizedComponent_potential_transition h τ.val _ _

/-- Whole original prop:PSHNApvolGamma, using the SAME actual original spatial limit mass. -/
theorem sourceNAVolume_positiveTestCurve (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) :
    sourceNAVolume (sourcePositiveTestCurveToNA G) =
      sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit G.val.toSourceTestCurvePredata)
        G.val.limit_thetaPSH univ := by
  let L := sourceTestCurveLimit G.val.toSourceTestCurvePredata
  have hu := (isThetaPSH_iff_nativeThetaPotential θ L).mp G.val.limit_thetaPSH
  apply le_antisymm
  · let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have hp (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hlim : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hLj (j : ℕ) : IsThetaPshPotential
        (atlasClosedFormToNative θ + ε j • omega.form).val L :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (hp j).le)
    have hc := TraceFreeLimit.tendsto_diagonalPotentialMass_add_smul omega hu hp hlim hLj
    have hbound (j : ℕ) : sourceNAVolume (sourcePositiveTestCurveToNA G) ≤
        diagonalPotentialMass (atlasClosedFormToNative θ + ε j • omega.form) L (hLj j) := by
      let ωj := KahlerBackground.smul (hp j) omega
      have h := (sourceNAVolume_le_component (sourcePositiveTestCurveToNA G)
        (sourceKahlerFormOfBackground ωj)).trans_eq (sourceNAComponentMass_embedding_literal G ωj)
      simpa only [sourcePotentialNonPluripolarMeasure,
        sourceTestCurveEnlargedBackground_native, KahlerBackground.smul_form,
        diagonalPotentialMass, ωj, L] using h
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hc (Eventually.of_forall hbound)
  · exact le_iInf fun ω =>
      (sourcePotentialMass_mono_background (sourceNAComponentBackground_positive θ ω)
        G.val.limit_thetaPSH).trans_eq (sourceNAComponentMass_embedding G ω).symm

/-- Every actual image of the original positive curve domain has positive system volume. -/
theorem sourceNAVolume_positiveTestCurve_pos (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve θ) :
    0 < sourceNAVolume (sourcePositiveTestCurveToNA G) := by
  rw [sourceNAVolume_positiveTestCurve omega G]
  exact G.val.positiveLimitMass

end SGPT.PSH.VariableComplexAtlas
