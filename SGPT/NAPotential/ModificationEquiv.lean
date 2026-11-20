import SGPT.NAPotential.ModificationPullback
import SGPT.NAPotential.SemipositiveVolume
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

/-! Genuine inverse and whole-source NA modification bijection.
Positive volume, original compatibility and connectedness of the source
of the modification are all manufactured by existing geometric producers. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open DiagonalMass

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {π : Y → X}

/-- The actual pulled smooth Kähler form; only semipositivity is asserted. -/
def pulledKahlerAtlas (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) : AtlasClosedRealOneOneForm (ofFixedModel n Y) :=
  (nativeClosedFormToAtlas omegaX.form).nativeHolomorphicPullback hπ.1

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
theorem pulledKahlerAtlas_semipositive (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) :
    (atlasClosedFormToNative (pulledKahlerAtlas hπ omegaX)).val.IsSemipositive := by
  simp only [pulledKahlerAtlas, AtlasClosedRealOneOneForm.nativeHolomorphicPullback,
    sourceNativeAtlasForm_roundTrip]
  exact ClosedRealOneOneForm.pullback_isSemipositive hπ.1 omegaX.isSemipositive

omit [ConnectedSpace X] [ConnectedSpace Y] in
/-- Its volume is the actual downstairs smooth Kähler volume, in every
source dimension including zero. It is a conclusion, not an input. -/
theorem pulledKahlerAtlas_mass (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) :
    diagonalPotentialMass (atlasClosedFormToNative (pulledKahlerAtlas hπ omegaX))
      (fun _ => 0) ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (pulledKahlerAtlas_semipositive hπ omegaX)) =
    diagonalPotentialMass omegaX.form (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr omegaX.isSemipositive) := by
  let α := nativeClosedFormToAtlas omegaX.form
  have hu : (ofFixedModel n X).IsThetaPSH α (fun _ => 0) := by
    apply (isThetaPSH_iff_nativeThetaPotential α _).mpr
    simpa only [α, sourceNativeAtlasForm_roundTrip] using
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr omegaX.isSemipositive)
  have hup := hu.comp_native_analyticModification hπ
  have hm := sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ α hu hup
  simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass, α,
    sourceNativeAtlasForm_roundTrip, pulledKahlerAtlas, Function.comp_def] using hm

omit [ConnectedSpace Y] in
theorem pulledKahlerAtlas_volume_pos (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) :
    0 < diagonalPotentialMass (atlasClosedFormToNative (pulledKahlerAtlas hπ omegaX))
      (fun _ => 0) ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (pulledKahlerAtlas_semipositive hπ omegaX)) := by
  rw [pulledKahlerAtlas_mass]
  exact KahlerVolumePositive.diagonalPotentialMass_zero_pos omegaX

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- Literal entire background calibration, not equality only off exceptional
sets or an assumed cohomology representative. -/
private theorem pulledComponentBackground_eq (hπ : IsAnalyticModification (n := n) π)
    (κ : SourceKahlerForm n X) :
    (sourceNAComponentBackground θ κ).nativeHolomorphicPullback hπ.1 =
      (θ.nativeHolomorphicPullback hπ.1).add
        (pulledKahlerAtlas hπ (sourceKahlerFormRepresentative κ)) := by
  apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback,
    sourceNativeAtlasForm_roundTrip, sourceNativeClosedForm_add,
    sourceNAComponentBackground_native, pulledKahlerAtlas]
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- Descend an ACTUAL positive I-model test curve with exactly a pulled whole
background. Original positive mass and I-model slice reflection are producers. -/
def positiveCurveModificationDescent (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    {α : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (H : SourcePositiveIModelTestCurve (α.nativeHolomorphicPullback hπ.1)) :
    SourcePositiveIModelTestCurve α := by
  let G := H.val.modificationDescent hπ
  refine ⟨G, ?_⟩
  apply (sourceIModelTestCurvesPositive_iff_slices omegaX G).mpr
  apply (G.modificationPullback_isIModel_iff hπ).mp
  have he : G.modificationPullback hπ = H.val :=
    (sourceTestCurveModificationEquiv hπ α).apply_symm_apply H.val
  rw [he]
  exact (sourceIModelTestCurvesPositive_iff_slices omegaY H.val).mp H.property

theorem positiveCurveModificationDescent_pullback
    (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    {α : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (H : SourcePositiveIModelTestCurve (α.nativeHolomorphicPullback hπ.1)) :
    (positiveCurveModificationDescent hπ omegaX omegaY H).val.modificationPullback hπ = H.val :=
  (sourceTestCurveModificationEquiv hπ α).apply_symm_apply H.val

/-- Recover the actual positive curve at the pulled semipositive index and
then descend. All its positivity data are manufactured from smooth Kähler
volume; callers supply neither a recovered curve nor an admissibility field. -/
def sourceNADescentComponent (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1)) (κ : SourceKahlerForm n X) :
    SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) :=
  positiveCurveModificationDescent hπ omegaX omegaY
    ((semipositivePositiveVolumeReader omegaY Δ
      (pulledKahlerAtlas hπ (sourceKahlerFormRepresentative κ))
      (pulledKahlerAtlas_semipositive hπ (sourceKahlerFormRepresentative κ))
      (pulledKahlerAtlas_volume_pos hπ (sourceKahlerFormRepresentative κ))).castBackground
      (pulledComponentBackground_eq (θ := θ) hπ κ).symm)

/-- Each recovered reader and ANY actual original upstairs literal reader
have the same original intrinsic curve type. -/
private theorem recoveredReader_POrder_equivalent
    {β : AtlasClosedRealOneOneForm (ofFixedModel n Y)}
    (omegaY : KahlerBackground n Y) (Δ : SourceNAPotential β)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hvol : 0 < diagonalPotentialMass (atlasClosedFormToNative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hη))
    (B : KahlerBackground n Y) :
    SourceTestCurvePOrder (semipositivePositiveVolumeReader omegaY Δ η hη hvol).val
      (Δ.realizedComponent B).val ∧
    SourceTestCurvePOrder (Δ.realizedComponent B).val
      (semipositivePositiveVolumeReader omegaY Δ η hη hvol).val := by
  let R := semipositivePositiveVolumeReader omegaY Δ η hη hvol
  have hr := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent R B
  rw [semipositivePositiveVolumeReader_embedding] at hr
  have hb := Δ.backgroundChange_POrder_equivalent omegaY η hη
  have hb₁ := (sourceNAPOrder_iff_realizedComponents _ _ B B).mp hb.1
  have hb₂ := (sourceNAPOrder_iff_realizedComponents _ _ B B).mp hb.2
  exact ⟨SourceTestCurvePOrder.trans omegaY hr.2 hb₂,
    SourceTestCurvePOrder.trans omegaY hb₁ hr.1⟩

/-- Pulling back any new downstairs component recovers the intrinsic type of
any original upstairs reader. This is an internally proved descent law. -/
theorem sourceNADescentComponent_pullback_POrder_equivalent
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1))
    (κ : SourceKahlerForm n X) (B : KahlerBackground n Y) :
    SourceTestCurvePOrder ((sourceNADescentComponent omegaX omegaY hπ Δ κ).val.modificationPullback hπ)
      (Δ.realizedComponent B).val ∧
    SourceTestCurvePOrder (Δ.realizedComponent B).val
      ((sourceNADescentComponent omegaX omegaY hπ Δ κ).val.modificationPullback hπ) := by
  let η := pulledKahlerAtlas hπ (sourceKahlerFormRepresentative κ)
  let R := semipositivePositiveVolumeReader omegaY Δ η
    (pulledKahlerAtlas_semipositive hπ (sourceKahlerFormRepresentative κ))
    (pulledKahlerAtlas_volume_pos hπ (sourceKahlerFormRepresentative κ))
  have hR := recoveredReader_POrder_equivalent omegaY Δ η
    (pulledKahlerAtlas_semipositive hπ (sourceKahlerFormRepresentative κ))
    (pulledKahlerAtlas_volume_pos hπ (sourceKahlerFormRepresentative κ)) B
  have hc := R.castBackground_POrder_equivalent omegaY
    (pulledComponentBackground_eq (θ := θ) hπ κ).symm
  have he := positiveCurveModificationDescent_pullback hπ omegaX omegaY
    (R.castBackground (pulledComponentBackground_eq (θ := θ) hπ κ).symm)
  have he' : (sourceNADescentComponent omegaX omegaY hπ Δ κ).val.modificationPullback hπ =
      (R.castBackground (pulledComponentBackground_eq (θ := θ) hπ κ).symm).val := he
  rw [he']
  exact ⟨SourceTestCurvePOrder.trans omegaY hc.2 hR.1,
    SourceTestCurvePOrder.trans omegaY hR.2 hc.1⟩

/-- All independently recovered downstairs components agree intrinsically,
by genuine modification reflection. -/
theorem sourceNADescentComponent_POrder_equivalent
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1))
    (κ ζ : SourceKahlerForm n X) :
    SourceTestCurvePOrder (sourceNADescentComponent omegaX omegaY hπ Δ κ).val
      (sourceNADescentComponent omegaX omegaY hπ Δ ζ).val ∧
    SourceTestCurvePOrder (sourceNADescentComponent omegaX omegaY hπ Δ ζ).val
      (sourceNADescentComponent omegaX omegaY hπ Δ κ).val := by
  have hk := sourceNADescentComponent_pullback_POrder_equivalent omegaX omegaY hπ Δ κ omegaY
  have hz := sourceNADescentComponent_pullback_POrder_equivalent omegaX omegaY hπ Δ ζ omegaY
  exact ⟨(curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mpr
      (SourceTestCurvePOrder.trans omegaY hk.1 hz.2),
    (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mpr
      (SourceTestCurvePOrder.trans omegaY hz.1 hk.2)⟩

/-- Manufacture the ORIGINAL downstairs transition compatibility. -/
theorem sourceNADescentComponent_compatible
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1))
    (κ ζ : SourceKahlerForm n X) (h : sourceKahlerFormLE κ ζ) :
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference θ h)
      (sourceNADescentComponent omegaX omegaY hπ Δ κ) =
      sourceNADescentComponent omegaX omegaY hπ Δ ζ := by
  have ht := sourceIModelTestCurveTransition_POrder_equivalent (sourceKahlerFormRepresentative ζ)
    (sourceNAComponentBackground_difference θ h) (sourceNADescentComponent omegaX omegaY hπ Δ κ)
  have hc := sourceNADescentComponent_POrder_equivalent omegaX omegaY hπ Δ κ ζ
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omegaX
    (SourceTestCurvePOrder.trans omegaX ht.2 hc.1)
    (SourceTestCurvePOrder.trans omegaX hc.2 ht.1)

/-- The actual original inverse system on X, without a supplied descent law. -/
def sourceNADescent (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1)) : SourceNAPotential θ where
  component κ := sourceNADescentComponent omegaX omegaY hπ Δ κ
  compatible κ ζ h := sourceNADescentComponent_compatible omegaX omegaY hπ Δ κ ζ h

/-- Every genuine upstairs system is the pullback of the manufactured descent. -/
theorem sourceNAPullback_descent (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hπ.1)) :
    sourceNAPullback omegaX hπ (sourceNADescent omegaX omegaY hπ Δ) = Δ := by
  let E := sourceNADescent omegaX omegaY hπ Δ
  let κ := sourceKahlerFormOfBackground omegaX
  have hr := E.realizedComponent_component_POrder_equivalent omegaX κ
  have hp := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.1
  have hq := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.2
  have hd := sourceNADescentComponent_pullback_POrder_equivalent omegaX omegaY hπ Δ κ omegaY
  apply SourceNAPotential.ext
  intro ζ
  have hf := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ E ζ omegaX
  have hΔ := Δ.realizedComponent_component_POrder_equivalent omegaY ζ
  apply Subtype.ext
  apply SourceTestCurvePOrder.antisymm omegaY
  · exact SourceTestCurvePOrder.trans omegaY hf.1
      (SourceTestCurvePOrder.trans omegaY hp (SourceTestCurvePOrder.trans omegaY hd.1 hΔ.1))
  · exact SourceTestCurvePOrder.trans omegaY hΔ.2
      (SourceTestCurvePOrder.trans omegaY hd.2 (SourceTestCurvePOrder.trans omegaY hq hf.2))

/-- Exact whole-source `cor:PSHNAbimero`; original NA systems in every dimension. -/
theorem sourceNAPullback_bijective (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    Function.Bijective (sourceNAPullback (θ := θ) omegaX hπ) :=
  ⟨sourceNAPullback_injective omegaX omegaY hπ,
    fun Δ => ⟨sourceNADescent omegaX omegaY hπ Δ, sourceNAPullback_descent omegaX omegaY hπ Δ⟩⟩

/-- The exact actual source bijection, whose forward map is the pullback. -/
def sourceNAPotentialModificationEquiv
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    SourceNAPotential θ ≃ SourceNAPotential (θ.nativeHolomorphicPullback hπ.1) where
  toFun := sourceNAPullback omegaX hπ
  invFun := sourceNADescent omegaX omegaY hπ
  left_inv Γ := (sourceNAPullback_injective omegaX omegaY hπ)
    (sourceNAPullback_descent omegaX omegaY hπ (sourceNAPullback omegaX hπ Γ))
  right_inv := sourceNAPullback_descent omegaX omegaY hπ

omit [ConnectedSpace Y] in
/-- Whole ambient source corollary: upstairs connectedness is a consequence
of the genuine modification, not an extra caller hypothesis. -/
theorem sourceNAPullback_bijective_whole
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    Function.Bijective (sourceNAPullback (θ := θ) omegaX hπ) := by
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  exact sourceNAPullback_bijective omegaX omegaY hπ

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA
