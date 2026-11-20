import SGPT.Hodge.SourceAugmentedCurrentCorrespondence
import SGPT.Hodge.SourceNefProjective

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.BDivisor.PrimePushforward
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Smooth semipositive addition preserves every actual generic prime coefficient. -/
theorem semipositiveShiftCurrent_coeff (T : ClosedPositive (n := n) (X := X))
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    currentCoefficientAny (semipositiveShiftCurrent T σ hσ)=currentCoefficientAny T := by
  funext D
  cases n with
  | zero => exact isEmptyElim D
  | succ m =>
    let hz := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
    let Z := thetaPotentialCurrent σ.val (fun _ : X => (0 : EReal)) hz
    let hZ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent σ.val (fun _ => 0) hz
    let hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)
    have hZ0 : SGPT.Siu.currentGenericLelong Z hZ D=0 := by
      obtain ⟨x,hx⟩ := D.nonempty
      refine le_antisymm ((SGPT.Siu.currentGenericLelong_le hZ D hx).trans (le_of_eq ?_)) bot_le
      rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hZ (rfl : Z=Z)]
      exact SGPT.Okounkov.squaredLogLelongNumber_zero x
    change (SGPT.Siu.bookGenericLelong (toBookCurrent (semipositiveShiftCurrent T σ hσ)) D).toReal =
      (SGPT.Siu.bookGenericLelong (toBookCurrent T) D).toReal
    rw [SGPT.Siu.bookGenericLelong_eq,SGPT.Siu.bookGenericLelong_eq]
    have he : SGPT.Siu.currentGenericLelong (toBookCurrent (semipositiveShiftCurrent T σ hσ)).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent (semipositiveShiftCurrent T σ hσ))) D =
        SGPT.Siu.currentGenericLelong ((toBookCurrent T).current+Z) (hT.add hZ) D := by
      congr 1
      exact semipositiveShiftCurrent_book_add T σ hσ
    rw [he,currentGenericLelong_add hT hZ _ D,hZ0,add_zero]

/-- Actual full augmented shift: same entire family plus the actual root Cartier,
and exactly the same original coefficient family. -/
def augmentedSemipositiveShift (ω : KahlerBackground n X) (A : AugmentedNefAny n X)
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) : AugmentedNefAny n X :=
  ⟨A.bdiv+rootCartierAny (RealBottChern.ofRepresentative σ),
    isNefAny_add_root_semipositive ω A.bdiv A.isNef σ hσ,
    A.coeff,A.coeff_nonneg,A.summable⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem augmentedSemipositiveShift_class (ω : KahlerBackground n X) (A : AugmentedNefAny n X)
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    (augmentedSemipositiveShift ω A σ hσ).cohomologyClass=
      A.cohomologyClass+RealBottChern.ofRepresentative σ := by
  change (show RealBottChern n X from
    (A.bdiv+rootCartierAny (RealBottChern.ofRepresentative σ)).val ModelSystem.Model.root)+
      A.divisorClass=A.cohomologyClass+RealBottChern.ofRepresentative σ
  change (show RealBottChern n X from A.bdiv.val ModelSystem.Model.root)+
    (show RealBottChern n X from
      (rootCartierAny (RealBottChern.ofRepresentative σ)).val ModelSystem.Model.root)+
      A.divisorClass=A.cohomologyClass+RealBottChern.ofRepresentative σ
  rw [rootCartierAny_root]
  unfold AugmentedNefAny.cohomologyClass
  abel

theorem currentToAugmented_smoothShift (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X)) (σ : ClosedRealOneOneForm n X)
    (hσ : σ.val.IsSemipositive) :
    currentToAugmented ω (semipositiveShiftCurrent T σ hσ)=
      augmentedSemipositiveShift ω (currentToAugmented ω T) σ hσ := by
  apply AugmentedNefAny.ext
  · exact semipositiveShiftCurrent_bdivisor T σ hσ
  · exact semipositiveShiftCurrent_coeff T σ hσ

/-- Actual smooth addition on the WHOLE original positive-volume current source. -/
def positiveCurrentSmoothShift (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : PositiveClassCurrent ω α) (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    PositiveClassCurrent ω (α+RealBottChern.ofRepresentative σ) :=
  ⟨semipositiveShiftCurrent T.val σ hσ,by rw [semipositiveShiftCurrent_class,T.property.1],by
    rw [currentIVolumeAny_eq_bdivisorVolume ω,semipositiveShiftCurrent_bdivisor]
    have hp := T.property.2
    rw [currentIVolumeAny_eq_bdivisorVolume ω] at hp
    exact hp.trans_le (volumeAny_le_add_root_semipositive ω _
      (DTUniformDraft.currentBDivisorAnyOn_isNef ω T.val) σ hσ)⟩

/-- Genuine physical T↦T+ζ−κ transition on all original positive-volume currents. -/
def positiveCurrentTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : PositiveClassCurrent ω (α+indexClass κ)) : PositiveClassCurrent ω (α+indexClass ζ) :=
  let S := positiveCurrentSmoothShift ω (α+indexClass κ) T (indexDifference κ ζ) hκζ
  ⟨S.val,by rw [S.property.1,indexDifference_class]; abel,S.property.2⟩

/-- The exact matching original augmented transition, with every coefficient unchanged. -/
def positiveAugmentedTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (A : PositiveAugmentedRoot (α+indexClass κ)) : PositiveAugmentedRoot (α+indexClass ζ) :=
  ⟨augmentedSemipositiveShift ω A.val (indexDifference κ ζ) hκζ,by
    exact A.property.1.trans_le (volumeAny_le_add_root_semipositive ω _ A.val.isNef _ hκζ),by
    exact (augmentedSemipositiveShift_class ω A.val (indexDifference κ ζ) hκζ).trans
      ((congrArg₂ (fun x y : RealBottChern n X => x+y) A.property.2
        (indexDifference_class κ ζ)).trans (by abel))⟩

/-- The newly proved whole correspondence respects actual physical current transitions. -/
theorem positiveCurrentToAugmentedRoot_transition (ω : KahlerBackground n X)
    (α : RealBottChern n X) {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : PositiveClassCurrent ω (α+indexClass κ)) :
    positiveCurrentToAugmentedRoot ω (α+indexClass ζ) (positiveCurrentTransition ω α hκζ T)=
      positiveAugmentedTransition ω α hκζ (positiveCurrentToAugmentedRoot ω (α+indexClass κ) T) := by
  apply Subtype.ext
  exact currentToAugmented_smoothShift ω T.val (indexDifference κ ζ) hκζ

def positiveQuotientTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ) :
    Quotient (positiveCurrentISetoid ω (α+indexClass κ)) →
      Quotient (positiveCurrentISetoid ω (α+indexClass ζ)) := fun q =>
  (sourceAugmentedCurrentEquiv ω (α+indexClass ζ)).symm
    (positiveAugmentedTransition ω α hκζ (sourceAugmentedCurrentEquiv ω (α+indexClass κ) q))

/-- Exact original quotient-generator readback; no diagram certificate is assumed. -/
theorem positiveQuotientTransition_mk (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : PositiveClassCurrent ω (α+indexClass κ)) :
    positiveQuotientTransition ω α hκζ (Quotient.mk _ T)=
      Quotient.mk _ (positiveCurrentTransition ω α hκζ T) := by
  apply (sourceAugmentedCurrentEquiv ω (α+indexClass ζ)).injective
  rw [positiveQuotientTransition,Equiv.apply_symm_apply]
  exact (positiveCurrentToAugmentedRoot_transition ω α hκζ T).symm

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
