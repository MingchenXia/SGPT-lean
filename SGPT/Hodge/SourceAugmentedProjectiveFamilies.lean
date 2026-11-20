import SGPT.Hodge.SourceAugmentedSmoothShift

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
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The ENTIRE original augmented nef target, with no volume restriction. -/
def AugmentedRoot (α : RealBottChern n X) := {A : AugmentedNefAny n X // A.cohomologyClass=α}

/-- Every literal geometric Kähler form is an index; transitions preserve the whole
original coefficient family and add the actual smooth root Cartier family. -/
def AugmentedPositiveLimit (ω : KahlerBackground n X) (α : RealBottChern n X) :=
  {F : ∀ κ : SourceKahlerForm n X, PositiveAugmentedRoot (α+indexClass κ) //
    ∀ (κ ζ : SourceKahlerForm n X) (h : sourceKahlerFormLE κ ζ),
      positiveAugmentedTransition ω α h (F κ)=F ζ}

def augmentedRootComponent (ω : KahlerBackground n X) (α : RealBottChern n X)
    (A : AugmentedRoot α) (κ : SourceKahlerForm n X) : PositiveAugmentedRoot (α+indexClass κ) :=
  ⟨augmentedSemipositiveShift ω A.val (sourceKahlerFormRepresentative κ).form
    (sourceKahlerFormRepresentative κ).isSemipositive,
    volumeAny_pos_add_rootKahler ω A.val.bdiv A.val.isNef (sourceKahlerFormRepresentative κ),by
      rw [augmentedSemipositiveShift_class,A.property]
      rfl⟩

def augmentedRootToPositiveLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (A : AugmentedRoot α) : AugmentedPositiveLimit ω α :=
  ⟨fun κ => augmentedRootComponent ω α A κ,by
    intro κ ζ h
    apply Subtype.ext
    apply AugmentedNefAny.ext
    · change A.val.bdiv+indexCartier κ+
        rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ))=A.val.bdiv+indexCartier ζ
      rw [indexDifference_cartier]
      abel
    · rfl⟩

/-- A coefficient family is recovered internally; the next theorem proves it
is exactly the coefficient family at EVERY original Kähler-form index. -/
def recoverCoefficient (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) : SGPT.PSH.GeometricPrimeCarrier n X → ℝ :=
  (F.val (sourceKahlerFormOfBackground ω)).val.coeff

omit [MeasurableSpace X] [BorelSpace X] in
theorem recoverCoefficient_eq_at_every_index (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) (κ : SourceKahlerForm n X) :
    recoverCoefficient ω α F=(F.val κ).val.coeff := by
  let κ₀ := sourceKahlerFormOfBackground ω
  let ζ := sourceKahlerFormCommonUpper κ₀ κ
  have h₀ := congrArg (fun A : PositiveAugmentedRoot (α+indexClass ζ) => A.val.coeff)
    (F.property κ₀ ζ (sourceKahlerFormLE_commonUpper_left κ₀ κ))
  have hκ := congrArg (fun A : PositiveAugmentedRoot (α+indexClass ζ) => A.val.coeff)
    (F.property κ ζ (sourceKahlerFormLE_commonUpper_right κ₀ κ))
  exact h₀.trans hκ.symm

def recoverDivisorClass (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) : RealBottChern n X :=
  (F.val (sourceKahlerFormOfBackground ω)).val.divisorClass

omit [MeasurableSpace X] [BorelSpace X] in
theorem recoverDivisorClass_eq_at_every_index (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) (κ : SourceKahlerForm n X) :
    (F.val κ).val.divisorClass=recoverDivisorClass ω α F := by
  apply AugmentedNefAny.divisorClass_eq
  have h := (F.val (sourceKahlerFormOfBackground ω)).val.hasSum_divisorClass
  have hc := recoverCoefficient_eq_at_every_index ω α F κ
  change (F.val (sourceKahlerFormOfBackground ω)).val.coeff=(F.val κ).val.coeff at hc
  rw [hc] at h
  exact h

/-- The underlying ENTIRE compatible big-nef family in the internally recovered
root class. The actual coefficient class sum is proved independent of every index. -/
def augmentedLimitToBigLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) : BigNefProjectiveLimit ω (α-recoverDivisorClass ω α F) :=
  ⟨fun κ => ⟨(F.val κ).val.bdiv,(F.val κ).property.1,(F.val κ).val.isNef,by
      have h := (F.val κ).property.2
      change (show RealBottChern n X from (F.val κ).val.bdiv.val ModelSystem.Model.root)+
        (F.val κ).val.divisorClass=α+indexClass κ at h
      rw [recoverDivisorClass_eq_at_every_index ω α F κ] at h
      calc
        _ = ((show RealBottChern n X from
            (F.val κ).val.bdiv.val ModelSystem.Model.root)+recoverDivisorClass ω α F)-
            recoverDivisorClass ω α F := by module
        _ = (α+indexClass κ)-recoverDivisorClass ω α F :=
          congrArg (fun η : RealBottChern n X => η-recoverDivisorClass ω α F) h
        _ = (α-recoverDivisorClass ω α F)+indexClass κ := by module⟩,by
    intro κ ζ h
    apply Subtype.ext
    exact congrArg (fun A : PositiveAugmentedRoot (α+indexClass ζ) => A.val.bdiv) (F.property κ ζ h)⟩

def recoverAugmentedRoot (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) : AugmentedRoot α := by
  let β := recoverDivisorClass ω α F
  let D := (nefRootBigLimitEquiv ω (α-β)).symm (augmentedLimitToBigLimit ω α F)
  let A : AugmentedNefAny n X := ⟨D.val,D.property.1,recoverCoefficient ω α F,
    (F.val (sourceKahlerFormOfBackground ω)).val.coeff_nonneg,
    (F.val (sourceKahlerFormOfBackground ω)).val.summable⟩
  have hβ : A.divisorClass=β := AugmentedNefAny.divisorClass_eq A
    (F.val (sourceKahlerFormOfBackground ω)).val.hasSum_divisorClass
  refine ⟨A,?_⟩
  change (show RealBottChern n X from D.val.val ModelSystem.Model.root)+A.divisorClass=α
  rw [D.property.2,hβ]
  module

omit [MeasurableSpace X] [BorelSpace X] in
/-- Exact family recovery at EVERY original Kähler-form index. -/
theorem recoverAugmentedRoot_bdiv_at_every_index (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) (κ : SourceKahlerForm n X) :
    (recoverAugmentedRoot ω α F).val.bdiv=(F.val κ).val.bdiv-indexCartier κ :=
  recoverFamily_eq_at_every_index ω (α-recoverDivisorClass ω α F) (augmentedLimitToBigLimit ω α F) κ

omit [MeasurableSpace X] [BorelSpace X] in
theorem recoverAugmentedRoot_coeff_at_every_index (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) (κ : SourceKahlerForm n X) :
    (recoverAugmentedRoot ω α F).val.coeff=(F.val κ).val.coeff :=
  recoverCoefficient_eq_at_every_index ω α F κ

/-- Whole augmented inverse limit on the literal all-Kähler-form diagram. -/
def augmentedRootPositiveLimitEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    AugmentedRoot α ≃ AugmentedPositiveLimit ω α where
  toFun := augmentedRootToPositiveLimit ω α
  invFun := recoverAugmentedRoot ω α
  left_inv A := by
    apply Subtype.ext
    apply AugmentedNefAny.ext
    · rw [recoverAugmentedRoot_bdiv_at_every_index ω α _ (sourceKahlerFormOfBackground ω)]
      change A.val.bdiv+indexCartier (sourceKahlerFormOfBackground ω)-
        indexCartier (sourceKahlerFormOfBackground ω)=A.val.bdiv
      abel
    · rfl
  right_inv F := by
    apply Subtype.ext
    funext κ
    apply Subtype.ext
    apply AugmentedNefAny.ext
    · change (recoverAugmentedRoot ω α F).val.bdiv+indexCartier κ=(F.val κ).val.bdiv
      rw [recoverAugmentedRoot_bdiv_at_every_index ω α F κ]
      abel
    · exact recoverAugmentedRoot_coeff_at_every_index ω α F κ

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
