import SGPT.Hodge.SourceAugmentedCurrentObjects
import SGPT.BDivisor.BlowupModelModifiedNef

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Literal original augmented nef b-divisor in every natural dimension:
the original full model family and original nonnegative, class-summable prime coefficients. -/
structure AugmentedNefAny (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] where
  bdiv : WeilFamilyAny (ModelSystem.blowup n X)
  isNef : IsNefAny bdiv
  coeff : SGPT.PSH.GeometricPrimeCarrier n X → ℝ
  coeff_nonneg : ∀ D, 0 ≤ coeff D
  summable : ∃ β, HasDivisorClassSumAny coeff β

namespace AugmentedNefAny

theorem ext {A B : AugmentedNefAny n X} (hD : A.bdiv=B.bdiv) (hc : A.coeff=B.coeff) : A=B := by
  cases A
  cases B
  cases hD
  cases hc
  rfl

def divisorClass (A : AugmentedNefAny n X) : RealBottChern n X := A.summable.choose

theorem hasSum_divisorClass (A : AugmentedNefAny n X) : HasDivisorClassSumAny A.coeff A.divisorClass :=
  A.summable.choose_spec

theorem divisorClass_eq (A : AugmentedNefAny n X) {β : RealBottChern n X}
    (hβ : HasDivisorClassSumAny A.coeff β) : A.divisorClass=β := by
  let := SGPT.BDivisor.euclideanTopology (RealBottChern n X)
  have := SGPT.BDivisor.t2Space_euclideanTopology (RealBottChern n X)
  exact HasSum.unique A.hasSum_divisorClass hβ

def cohomologyClass (A : AugmentedNefAny n X) : RealBottChern n X :=
  (show RealBottChern n X from A.bdiv.val ModelSystem.Model.root) + A.divisorClass

def vol [ConnectedSpace X] (A : AugmentedNefAny n X) : ℝ≥0∞ := volumeAny A.bdiv

end AugmentedNefAny

section Existing
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- Exact same-family/same-coefficient bridge to the ORIGINAL existing positive-dimensional object. -/
def augmentedToExisting (A : AugmentedNefAny (m+1) M) : BlowupAugmentedNefBDivisor m M (Nat.succ_pos m) :=
  ⟨toExisting _ _ A.bdiv,(isNefAny_iff_existing (Nat.succ_pos m) A.bdiv).mp A.isNef,
    A.coeff,A.coeff_nonneg,A.summable⟩

def augmentedFromExisting (A : BlowupAugmentedNefBDivisor m M (Nat.succ_pos m)) : AugmentedNefAny (m+1) M :=
  ⟨fromExisting _ _ A.bdiv,(isNefAny_iff_existing (Nat.succ_pos m) _).mpr
    (by simpa only [toExisting_fromExisting] using A.isNef),
    A.coeff,A.coeff_nonneg,A.summable⟩

theorem augmentedToExisting_from (A : BlowupAugmentedNefBDivisor m M (Nat.succ_pos m)) :
    augmentedToExisting (augmentedFromExisting A)=A := by
  cases A
  simp only [augmentedToExisting,augmentedFromExisting,toExisting_fromExisting]

theorem augmentedFromExisting_to (A : AugmentedNefAny (m+1) M) :
    augmentedFromExisting (augmentedToExisting A)=A := by
  apply AugmentedNefAny.ext
  · exact fromExisting_toExisting _ _ _
  · rfl

def augmentedExistingEquiv : AugmentedNefAny (m+1) M ≃ BlowupAugmentedNefBDivisor m M (Nat.succ_pos m) where
  toFun := augmentedToExisting
  invFun := augmentedFromExisting
  left_inv := augmentedFromExisting_to
  right_inv := augmentedToExisting_from

theorem augmentedToExisting_cohomologyClass (A : AugmentedNefAny (m+1) M) :
    (augmentedToExisting A).cohomologyClass=A.cohomologyClass := rfl

theorem augmentedToExisting_volume [ConnectedSpace M] (A : AugmentedNefAny (m+1) M) :
    (augmentedToExisting A).vol=A.vol := (volumeAny_eq_existing (Nat.succ_pos m) A.bdiv).symm
end Existing

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- WHOLE original source current set, with positive original current I-volume. -/
def PositiveClassCurrent (_ω : KahlerBackground n X) (α : RealBottChern n X) :=
  {T : ClosedPositive (n := n) (X := X) // currentClassAny T=α ∧ 0<currentIVolumeAny T}

/-- Restrict exactly the original multiplier-equivalence setoid. -/
def positiveCurrentISetoid (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Setoid (PositiveClassCurrent ω α) := (currentISetoid ω).comap Subtype.val

/-- Entire original target with positive volume and prescribed total cohomology class. -/
def PositiveAugmentedRoot (α : RealBottChern n X) :=
  {A : AugmentedNefAny n X // 0<A.vol ∧ A.cohomologyClass=α}

/-- The canonical source map is the actual original D(T) and actual original generic coefficients. -/
def currentToAugmented (ω : KahlerBackground n X) (T : ClosedPositive (n := n) (X := X)) :
    AugmentedNefAny n X :=
  ⟨currentBDivisorAnyOn (ModelSystem.blowup n X) T,DTUniformDraft.currentBDivisorAnyOn_isNef ω T,
    currentCoefficientAny T,currentCoefficientAny_nonneg T,
    ⟨currentClassAny (divisorCurrentAny T),hasDivisorClassSumAny_divisorCurrent ω T⟩⟩

theorem currentToAugmented_class (ω : KahlerBackground n X) (T : ClosedPositive (n := n) (X := X)) :
    (currentToAugmented ω T).cohomologyClass=currentClassAny T := by
  have hsum := hasDivisorClassSumAny_divisorCurrent ω T
  have hd : (currentToAugmented ω T).divisorClass=currentClassAny (divisorCurrentAny T) :=
    AugmentedNefAny.divisorClass_eq _ hsum
  have hr : (currentBDivisorAnyOn (ModelSystem.blowup n X) T).val ModelSystem.Model.root =
      currentClassAny (regularCurrentAny T) := by
    rw [←SourceReg.currentBDivisorAnyOn_regular_eq T]
    exact currentBDivisorAnyOn_root_of_regular _ (regularCurrentAny_idempotent T)
  change (show RealBottChern n X from
    (currentBDivisorAnyOn (ModelSystem.blowup n X) T).val ModelSystem.Model.root) +
    (currentToAugmented ω T).divisorClass = _
  rw [hr,hd]
  exact (currentClassAny_decomposition T).symm

theorem currentToAugmented_volume (ω : KahlerBackground n X) (T : ClosedPositive (n := n) (X := X)) :
    (currentToAugmented ω T).vol=currentIVolumeAny T :=
  (currentIVolumeAny_eq_bdivisorVolume ω T).symm

def positiveCurrentToAugmentedRoot (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : PositiveClassCurrent ω α) : PositiveAugmentedRoot α :=
  ⟨currentToAugmented ω T.val,by rw [currentToAugmented_volume]; exact T.property.2,
    (currentToAugmented_class ω T.val).trans T.property.1⟩

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
