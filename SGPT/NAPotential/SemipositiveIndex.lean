import SGPT.NAPotential.SemipositiveVolume
import SGPT.NAPotential.ProjectiveLimit
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

/-! Genuine geometric semipositive positive-volume indices for the WHOLE
source prop:PSHNAreform1. No target readers or
compatibility conclusions are stored in the index. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Exactly smooth closed semipositive geometric (1,1)-forms of positive
smooth top-wedge volume. Existence of a native representative is geometric
data only: it contains no original NA system or requested conclusion. -/
def HasPositiveSemipositiveRepresentative (η : GeometricRealForm n M 2) : Prop :=
  ∃ a : ClosedRealOneOneForm n M, ∃ ha : a.val.IsSemipositive,
    GeometricRealForm.ofRepresentative a.val = η ∧
    0 < diagonalPotentialMass a (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff a).mpr ha)

abbrev Index (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] :=
  {η : GeometricRealForm n M 2 // HasPositiveSemipositiveRepresentative η}

/-- The same quotient-out smooth tensor used by the existing Kähler index. -/
def representative (η : Index n M) : ClosedRealOneOneForm n M := by
  let a : SmoothRealForm n M 2 := Quotient.out η.val
  have hprops : a.IsClosed ∧ a.IsTypeOneOne := by
    obtain ⟨b, hb, hclass, hmass⟩ := η.property
    have hg : a.GeometricallyEq b.val :=
      (GeometricRealForm.ofRepresentative_eq_iff _ _).mp
        ((Quotient.out_eq η.val).trans hclass.symm)
    exact ⟨hg.isClosed_iff.mpr b.property.1, hg.isTypeOneOne_iff.mpr b.property.2⟩
  exact ⟨a, hprops⟩

theorem representative_class (η : Index n M) :
    GeometricRealForm.ofRepresentative (representative η).val = η.val :=
  Quotient.out_eq η.val

theorem representative_geometricallyEq (η : Index n M) (a : ClosedRealOneOneForm n M)
    (hclass : GeometricRealForm.ofRepresentative a.val = η.val) :
    (representative η).val.GeometricallyEq a.val :=
  (GeometricRealForm.ofRepresentative_eq_iff _ _).mp
    ((representative_class η).trans hclass.symm)

theorem representative_semipositive (η : Index n M) :
    (representative η).val.IsSemipositive := by
  obtain ⟨a, ha, hclass, hmass⟩ := η.property
  exact (representative_geometricallyEq η a hclass).isSemipositive_iff.mpr ha

omit [ConnectedSpace M] in
/-- Smooth top mass is a geometric invariant, with both zero-PSH inputs
manufactured from the genuine semipositivity hypotheses. -/
theorem zero_mass_geometricallyEq {a b : ClosedRealOneOneForm n M}
    (hg : a.val.GeometricallyEq b.val) (ha : a.val.IsSemipositive) (hb : b.val.IsSemipositive) :
    diagonalPotentialMass a (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff a).mpr ha) =
    diagonalPotentialMass b (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff b).mpr hb) := by
  let α := nativeClosedFormToAtlas a
  let β := nativeClosedFormToAtlas b
  have hu : (ofFixedModel n M).IsThetaPSH α (fun _ => 0) := by
    apply (isThetaPSH_iff_nativeThetaPotential α _).mpr
    simpa only [α, sourceNativeAtlasForm_roundTrip] using
      ((LocalPotentials.isThetaPshPotential_zero_iff a).mpr ha)
  have hv : (ofFixedModel n M).IsThetaPSH β (fun _ => 0) := by
    apply (isThetaPSH_iff_nativeThetaPotential β _).mpr
    simpa only [β, sourceNativeAtlasForm_roundTrip] using
      ((LocalPotentials.isThetaPshPotential_zero_iff b).mpr hb)
  have h := sourcePotentialMass_geometricallyEq
    (by simpa only [α, β, sourceNativeAtlasForm_roundTrip] using hg) hu hv
  simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass,
    α, β, sourceNativeAtlasForm_roundTrip] using h.symm

theorem representative_volume_pos (η : Index n M) :
    0 < diagonalPotentialMass (representative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (representative_semipositive η)) := by
  obtain ⟨a, ha, hclass, hmass⟩ := η.property
  rw [zero_mass_geometricallyEq (representative_geometricallyEq η a hclass)
    (representative_semipositive η) ha]
  exact hmass

/-- The actual original Kähler inclusion into the geometric positive-volume cone. -/
def ofKahler (κ : SourceKahlerForm n M) : Index n M := by
  refine ⟨κ.val, (sourceKahlerFormRepresentative κ).form,
    (sourceKahlerFormRepresentative κ).isSemipositive, ?_, ?_⟩
  · exact congrArg Subtype.val (sourceKahlerFormRepresentative_class κ)
  · exact KahlerVolumePositive.diagonalPotentialMass_zero_pos (sourceKahlerFormRepresentative κ)

theorem ofKahler_injective : Function.Injective (ofKahler (n := n) (M := M)) := by
  intro κ ζ h
  apply Subtype.ext
  exact congrArg (fun η : Index n M => η.val) h

/-- Exact calibration: both constructions choose the identical quotient-out
smooth tensor; all closedness and type proofs are irrelevant. -/
theorem representative_ofKahler (κ : SourceKahlerForm n M) :
    representative (ofKahler κ) = (sourceKahlerFormRepresentative κ).form := by
  apply Subtype.ext
  rfl

/-- Physical semipositive-difference order, independent of off-target values. -/
def IndexLE (η ζ : Index n M) : Prop :=
  (representative ζ - representative η).val.IsSemipositive

theorem IndexLE.refl (η : Index n M) : IndexLE η η := by
  unfold IndexLE
  rw [sub_self]
  intro e z hz v
  exact le_rfl

theorem IndexLE.trans {η ζ ν : Index n M} (h : IndexLE η ζ) (k : IndexLE ζ ν) : IndexLE η ν := by
  have he : representative ν - representative η =
      (representative ν - representative ζ) + (representative ζ - representative η) := by abel
  unfold IndexLE
  rw [he]
  intro e z hz v
  simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
    add_nonneg (k e z hz v) (h e z hz v)

@[instance_reducible]
def indexPreorder : Preorder (Index n M) where
  le := IndexLE
  le_refl := IndexLE.refl
  le_trans := fun _ _ _ => IndexLE.trans

theorem ofKahler_le_iff (κ ζ : SourceKahlerForm n M) :
    IndexLE (ofKahler κ) (ofKahler ζ) ↔ sourceKahlerFormLE κ ζ := by
  simp only [IndexLE, representative_ofKahler, sourceKahlerFormLE]

/-- Actual compact domination produces a Kähler upper index, for arbitrary
geometric positive-volume inputs and every dimension, without adding them
inside a supplied subset S. -/
theorem exists_kahler_commonUpper (omega : KahlerBackground n M) (η ζ : Index n M) :
    ∃ κ : SourceKahlerForm n M, IndexLE η (ofKahler κ) ∧ IndexLE ζ (ofKahler κ) := by
  obtain ⟨A, hA, h⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega
    (-representative η - representative ζ)
  let W := KahlerBackground.smul hA omega
  refine ⟨sourceKahlerFormOfBackground W, ?_, ?_⟩
  · unfold IndexLE
    rw [representative_ofKahler]
    intro e z hz v
    have hg := sourceKahlerFormRepresentative_geometricallyEq W e hz
    have hh := h e z hz v
    have hz' := representative_semipositive ζ e z hz v
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hh
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, hg, W, KahlerBackground.smul_form,
      ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith
  · unfold IndexLE
    rw [representative_ofKahler]
    intro e z hz v
    have hg := sourceKahlerFormRepresentative_geometricallyEq W e hz
    have hh := h e z hz v
    have hz' := representative_semipositive η e z hz v
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hh
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, hg, W, KahlerBackground.smul_form,
      ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith

/-- Actual augmented whole background at any genuine index. -/
def background (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (η : Index n M) :=
  θ.add (nativeClosedFormToAtlas (representative η))

theorem background_native (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (η : Index n M) :
    atlasClosedFormToNative (background θ η) = atlasClosedFormToNative θ + representative η := by
  simp only [background, sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]

theorem background_ofKahler (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (κ : SourceKahlerForm n M) :
    background θ (ofKahler κ) = sourceNAComponentBackground θ κ := by
  apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
  rw [background_native, representative_ofKahler, sourceNAComponentBackground_native]

theorem background_difference (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {η ζ : Index n M} (h : IndexLE η ζ) :
    (atlasClosedFormToNative (background θ ζ) - atlasClosedFormToNative (background θ η)).val.IsSemipositive := by
  rw [background_native, background_native, add_sub_add_left_eq_sub]
  exact h

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective
