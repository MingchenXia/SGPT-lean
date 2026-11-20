import SGPT.Hodge.SourceBigNefIntersection
import SGPT.PSH.SourceCurrentFinitePolarization
import SGPT.IGood.LogVolume

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X]

local notation "Pos" => (sourcePositiveCurrentCone (m := m) (M := X))
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- The genuine whole-current cone has an actual source current, not a reader certificate. -/
def coneActualCurrent (T : Pos) : ClosedPositive (n := m+1) (X := X) :=
  ofBookCurrent (SGPT.Siu.toBookCurrent T.val T.property)

omit [CompactSpace X] in
@[simp] theorem coneActualCurrent_read (T : Pos) :
    (toBookCurrent (coneActualCurrent T)).current=T.val := by
  rw [coneActualCurrent,toBookCurrent_ofBookCurrent]
  rfl

/-- The accepted actual current-family map is additive on its genuine cone. -/
def coneExistingFamilyHom : Pos →+ WeilBDivisorOn Sys (Nat.succ_pos m) where
  toFun T := currentBDivisorOn Sys T.val T.property
  map_add' A B := currentBDivisorOn_add Sys A.property B.property (A+B).property
  map_zero' := by
    let Z : WeilBDivisorOn Sys (Nat.succ_pos m) :=
      currentBDivisorOn Sys (0 : Pos).val (0 : Pos).property
    have h : Z=Z+Z := by
      simpa only [Z,AddSubmonoid.coe_zero,zero_add] using
        (currentBDivisorOn_add Sys (0 : Pos).property (0 : Pos).property (0+0 : Pos).property)
    exact add_left_cancel (h.symm.trans (add_zero Z).symm)

/-- The positive and dimension-uniform families retain the same model classes. -/
def fromExistingLinear (S : ModelSystem (m+1) X) :
    WeilBDivisorOn S (Nat.succ_pos m) →ₗ[ℝ] WeilFamilyAny S where
  toFun := fromExisting S (Nat.succ_pos m)
  map_add' A B := by apply Subtype.ext; rfl
  map_smul' c A := by apply Subtype.ext; rfl

/-- Actual positive currents produce actual compatible families additively. -/
def coneFamilyHom : Pos →+ WeilFamilyAny Sys :=
  (fromExistingLinear Sys).toAddMonoidHom.comp coneExistingFamilyHom

theorem coneFamilyHom_eq_current (T : Pos) :
    coneFamilyHom T=currentBDivisorAnyOn Sys (coneActualCurrent T) := by
  apply family_eq_of_toExisting_eq (Nat.succ_pos m)
  change toExisting Sys (Nat.succ_pos m)
    (fromExisting Sys (Nat.succ_pos m) (currentBDivisorOn Sys T.val T.property)) = _
  rw [toExisting_fromExisting,currentBDivisorAnyOn_eq_existing]
  exact currentBDivisorOn_congr Sys (coneActualCurrent_read T).symm _ _

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

theorem coneMixed_read (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → Pos) :
    (currentMixedIVolumeAny ω (fun i => coneActualCurrent (T i))).toReal =
      sourcePositiveCurrentMixedReal ω T := by
  rw [currentMixedIVolumeAny_eq_existing]
  simp only [coneActualCurrent_read]
  rfl

/-- The actual original diagonal equals the independent pure family volume. -/
theorem coneDiagonal_read (ω : KahlerBackground (m+1) X) (T : Pos) :
    sourcePositiveCurrentMixedReal ω (fun _ => T) =
      (volumeAny (coneFamilyHom T)).toReal := by
  rw [← coneMixed_read]
  have hd : currentMixedIVolumeAny ω (fun _ : Fin (m+1) => coneActualCurrent T)=
      currentIVolumeAny (coneActualCurrent T) :=
    sourceGeneralMixedIVolume_diagonal ω (presentationPSH (coneActualCurrent T))
  rw [hd,currentIVolumeAny_eq_bdivisorVolume ω,coneFamilyHom_eq_current]

/-- Genuine finite polarization read entirely in original pure b-divisor volumes. -/
theorem factorial_mul_currentMixed_eq_family_polarization
    (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → Pos) :
    ((m+1).factorial : ℝ) *
        (currentMixedIVolumeAny ω (fun i => coneActualCurrent (T i))).toReal =
      ∑ S : Finset (Fin (m+1)), (-1 : ℝ)^((m+1)-S.card) *
        (volumeAny (∑ j ∈ S, coneFamilyHom (T j))).toReal := by
  rw [coneMixed_read]
  have h := factorial_mul_sourcePositiveCurrentMixedReal_eq_diagonal_polarization ω T
  simp_rw [coneDiagonal_read,map_sum] at h
  exact h

/-- The same original current belongs to the already accepted genuine additive cone. -/
def actualCurrentCone (T : ClosedPositive (n := m+1) (X := X)) : Pos :=
  ⟨(toBookCurrent T).current,SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)⟩

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem coneActualCurrent_actualCurrentCone (T : ClosedPositive (n := m+1) (X := X)) :
    coneActualCurrent (actualCurrentCone T)=T := by
  rw [coneActualCurrent]
  have h : SGPT.Siu.toBookCurrent (actualCurrentCone T).val (actualCurrentCone T).property=
      toBookCurrent T := SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext rfl
  rw [h,ofBookCurrent_toBookCurrent]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem coneFamilyHom_actualCurrentCone (T : ClosedPositive (n := m+1) (X := X)) :
    coneFamilyHom (actualCurrentCone T)=currentBDivisorAnyOn Sys T := by
  rw [coneFamilyHom_eq_current,coneActualCurrent_actualCurrentCone]

/-- Every original big-nef tuple satisfies finite pure-volume polarization,
with all its actual realizing currents produced internally. -/
theorem factorial_mul_bigNefIntersection_eq_polarization_pos
    (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → BigNefFamily (n := m+1) (X := X)) :
    ((m+1).factorial : ℝ) * (bigNefIntersection ω D).toReal =
      ∑ S : Finset (Fin (m+1)), (-1 : ℝ)^((m+1)-S.card) *
        (volumeAny (∑ j ∈ S, (D j).val)).toReal := by
  have h := factorial_mul_currentMixed_eq_family_polarization ω
    (fun i => actualCurrentCone (realizingCurrent ω (D i)).val)
  simp_rw [coneActualCurrent_actualCurrentCone,coneFamilyHom_actualCurrentCone,
    realizingCurrent_family] at h
  exact h

end SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
