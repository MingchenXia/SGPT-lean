import SGPT.Hodge.SourceCurrentCorrespondence
import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra
import SGPT.PSH.SourceTestCurveScalingProjection

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceIntersection
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Genuine original selected presentations, with their actual source PSH predicate. -/
theorem presentationPSH (T : ClosedPositive (n := n) (X := X)) :
    (ofFixedModel n X).IsThetaPSH (currentPresentationBackground T)
      (currentPresentationPotential T) :=
  (isThetaPSH_iff_nativeThetaPotential _ _).mpr (currentPresentation_isPresentation T).choose

/-- Actual original mixed current I-volume in every dimension, retaining the actual empty tuple. -/
def currentMixedIVolumeAny (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) : ENNReal :=
  sourceGeneralMixedIVolume ω (fun i => currentPresentationBackground (T i))
    (fun i => currentPresentationPotential (T i)) (fun i => presentationPSH (T i))

/-- The positive-dimensional reader is the already defined ORIGINAL whole-current mixed volume. -/
theorem currentMixedIVolumeAny_eq_existing {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]
    [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ω : KahlerBackground (m+1) Y) (T : Fin (m+1) → ClosedPositive (n := m+1) (X := Y)) :
    currentMixedIVolumeAny ω T = sourceCurrentMixedIVolume ω
      (fun i => (toBookCurrent (T i)).current)
      (fun i => (toBookCurrent (T i)).isClosed)
      (fun i => (toBookCurrent (T i)).isTypeOneOne)
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent (T i))).2.2) := by
  let θ := fun i => atlasClosedFormToNative (currentPresentationBackground (T i))
  let v := fun i => currentPresentationPotential (T i)
  have hp i := (isPresentationAny_iff_book (T i) (θ i) (v i)).mp
    (currentPresentation_isPresentation (T i))
  obtain h := sourceCurrentMixedIVolume_eq_representation ω _ _ _ _ θ v
    (fun i => (hp i).choose) (fun i => (hp i).choose_spec)
  symm
  simpa only [θ, v, sourceAtlasNativeForm_roundTrip, currentMixedIVolumeAny] using h

/-- Same-class original I-order controls the actual mixed value, without a flag. -/
theorem currentMixedIVolumeAny_mono_IOrder (ω : KahlerBackground n X)
    (T S : Fin n → ClosedPositive (n := n) (X := X))
    (hclass : ∀ i, currentClassAny (T i) = currentClassAny (S i))
    (hI : ∀ i, currentIOrderAny (T i) (S i)) :
    currentMixedIVolumeAny ω T ≤ currentMixedIVolumeAny ω S := by
  cases n with
  | zero =>
    have heq : T = S := funext fun i => Fin.elim0 i
    subst S
    exact le_rfl
  | succ m =>
    apply sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω
      (fun i => currentPresentationBackground (T i))
      (fun i => currentPresentationBackground (S i))
      (fun i => currentPresentationPotential (T i))
      (fun i => currentPresentationPotential (S i))
      (fun i => presentationPSH (T i)) (fun i => presentationPSH (S i))
    · intro i
      obtain ⟨hu, hT⟩ := (isPresentationAny_iff_book (T i) _ _).mp
        (currentPresentation_isPresentation (T i))
      obtain ⟨hv, hS⟩ := (isPresentationAny_iff_book (S i) _ _).mp
        (currentPresentation_isPresentation (S i))
      have hTc : toBookCurrent (T i) = SGPT.PSH.BookCurrent.thetaPositiveCurrent _ _ hu :=
        SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext hT
      have hSc : toBookCurrent (S i) = SGPT.PSH.BookCurrent.thetaPositiveCurrent _ _ hv :=
        SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext hS
      have hc := hclass i
      change SGPT.PSH.BookCurrent.currentClass (toBookCurrent (T i)) =
        SGPT.PSH.BookCurrent.currentClass (toBookCurrent (S i)) at hc
      simpa only [hTc, hSc, SGPT.PSH.BookCurrent.currentClass_thetaPositiveCurrent] using hc
    · intro i
      obtain ⟨hu, hT⟩ := (isPresentationAny_iff_book (T i) _ _).mp
        (currentPresentation_isPresentation (T i))
      obtain ⟨hv, hS⟩ := (isPresentationAny_iff_book (S i) _ _).mp
        (currentPresentation_isPresentation (S i))
      apply (sourceIOrder_iff_native
        ⟨currentPresentationBackground (T i), presentationPSH (T i)⟩
        ⟨currentPresentationBackground (S i), presentationPSH (S i)⟩).mpr
      exact (sourceCurrentIOrder_iff_of_representation ω hu hv hT hS).mp
        ((currentIOrderAny_iff_existing (T i) (S i)).mp (hI i))

theorem currentMixedIVolumeAny_eq_of_IEquivalent (ω : KahlerBackground n X)
    (T S : Fin n → ClosedPositive (n := n) (X := X))
    (hclass : ∀ i, currentClassAny (T i) = currentClassAny (S i))
    (hI : ∀ i, currentIOrderAny (T i) (S i) ∧ currentIOrderAny (S i) (T i)) :
    currentMixedIVolumeAny ω T = currentMixedIVolumeAny ω S :=
  le_antisymm (currentMixedIVolumeAny_mono_IOrder ω T S hclass (fun i => (hI i).1))
    (currentMixedIVolumeAny_mono_IOrder ω S T (fun i => (hclass i).symm) (fun i => (hI i).2))

theorem currentMixedIVolumeAny_kahler_independent (ω κ : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) :
    currentMixedIVolumeAny ω T = currentMixedIVolumeAny κ T :=
  sourceGeneralMixedIVolume_kahler_independent ω κ _ _ _

/-- Exactly all original big nef compatible book-model families, without a fixed root restriction. -/
def BigNefFamily := {D : WeilFamilyAny (ModelSystem.blowup n X) //
  0 < volumeAny D ∧ IsNefAny D}

def familyRoot (D : BigNefFamily (n := n) (X := X)) : RealBottChern n X :=
  D.val.val ModelSystem.Model.root

def asRootFamily (D : BigNefFamily (n := n) (X := X)) :
    BigNefRoot (n := n) (X := X) (familyRoot D) := ⟨D.val, D.property.1, D.property.2, rfl⟩

/-- Actual original representatives are manufactured by the proved natural correspondence. -/
def realizingCurrent (ω : KahlerBackground n X) (D : BigNefFamily (n := n) (X := X)) :
    GCurrent (n := n) (X := X) (familyRoot D) :=
  (exists_gCurrent_realizing ω _ (asRootFamily D)).choose

theorem realizingCurrent_class (ω : KahlerBackground n X) (D : BigNefFamily (n := n) (X := X)) :
    currentClassAny (realizingCurrent ω D).val = D.val.val ModelSystem.Model.root :=
  (realizingCurrent ω D).property.1

theorem realizingCurrent_family (ω : KahlerBackground n X) (D : BigNefFamily (n := n) (X := X)) :
    currentBDivisorAnyOn (ModelSystem.blowup n X) (realizingCurrent ω D).val = D.val :=
  congrArg Subtype.val (exists_gCurrent_realizing ω _ (asRootFamily D)).choose_spec

/-- ORIGINAL def:DF_ext2, with existence and all choices produced internally. -/
def bigNefIntersection (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) : ENNReal :=
  currentMixedIVolumeAny ω (fun i => (realizingCurrent ω (D i)).val)

/-- EVERY original realizing tuple computes the SAME value; its nondivisoriality is internally proved. -/
theorem bigNefIntersection_eq_of_realization (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X))
    (T : Fin n → ClosedPositive (n := n) (X := X))
    (hclass : ∀ i, currentClassAny (T i) = (D i).val.val ModelSystem.Model.root)
    (hfamily : ∀ i, currentBDivisorAnyOn (ModelSystem.blowup n X) (T i) = (D i).val) :
    bigNefIntersection ω D = currentMixedIVolumeAny ω T := by
  apply currentMixedIVolumeAny_eq_of_IEquivalent
  · intro i
    exact (realizingCurrent_class ω (D i)).trans (hclass i).symm
  · intro i
    apply currentIEquivalent_of_currentBDivisorAnyOn_eq
      (realizingCurrent ω (D i)).property.2.1
      (current_eq_regular_of_root_eq_class (T i) (by rw [hfamily i]; exact (hclass i).symm))
      ((realizingCurrent_class ω (D i)).trans (hclass i).symm)
    exact (realizingCurrent_family ω (D i)).trans (hfamily i).symm

/-- Every background computes the same original big-nef intersection, with no supplied representatives. -/
theorem bigNefIntersection_kahler_independent (ω κ : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    bigNefIntersection ω D = bigNefIntersection κ D :=
  (bigNefIntersection_eq_of_realization ω D (fun i => (realizingCurrent κ (D i)).val)
    (fun i => realizingCurrent_class κ (D i)) (fun i => realizingCurrent_family κ (D i))).trans
    (currentMixedIVolumeAny_kahler_independent ω κ _)

/-- Genuine finiteness, produced for every actual input tuple. -/
theorem currentMixedIVolumeAny_lt_top (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) : currentMixedIVolumeAny ω T < ⊤ :=
  sourceGeneralMixedIVolume_lt_top ω _ _ _

theorem bigNefIntersection_lt_top (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) : bigNefIntersection ω D < ⊤ :=
  currentMixedIVolumeAny_lt_top ω _

/-- The literal original universal representative formula determines ONE value,
with nonempty realization produced inside the uniqueness proof. -/
theorem exists_unique_bigNefIntersection (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    ∃! I : ENNReal, ∀ T : Fin n → ClosedPositive (n := n) (X := X),
      (∀ i, currentClassAny (T i) = (D i).val.val ModelSystem.Model.root) →
      (∀ i, currentBDivisorAnyOn (ModelSystem.blowup n X) (T i) = (D i).val) →
      I = currentMixedIVolumeAny ω T := by
  refine ⟨bigNefIntersection ω D, bigNefIntersection_eq_of_realization ω D, ?_⟩
  intro I hI
  exact hI (fun i => (realizingCurrent ω (D i)).val)
    (fun i => realizingCurrent_class ω (D i)) (fun i => realizingCurrent_family ω (D i))

end SGPT.Hodge.BDivChain.SourceIntersection
