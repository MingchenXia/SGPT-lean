import SGPT.Hodge.SourceAugmentedBDivisorObjects
import SGPT.Hodge.SourceAugmentedCurrentOrder
import SGPT.Hodge.SourceAugmentedCurrentRealization

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
  [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The ACTUAL complete augmented datum reflects original multiplier equivalence
on the WHOLE current carrier in the same class. -/
theorem currentIEquivalent_of_augmentedData_eq (ω : KahlerBackground n X)
    {T S : ClosedPositive (n := n) (X := X)} (hclass : currentClassAny T=currentClassAny S)
    (hfamily : currentBDivisorAnyOn (ModelSystem.blowup n X) T=
      currentBDivisorAnyOn (ModelSystem.blowup n X) S)
    (hcoeff : currentCoefficientAny T=currentCoefficientAny S) :
    currentIOrderAny T S ∧ currentIOrderAny S T := by
  have hdiv := divisorCurrentAny_eq_of_coeff_eq hcoeff
  have hregclass : currentClassAny (regularCurrentAny T)=currentClassAny (regularCurrentAny S) := by
    have h := (currentClassAny_decomposition T).symm.trans
      (hclass.trans (currentClassAny_decomposition S))
    rw [hdiv] at h
    exact add_right_cancel h
  have hregfamily : currentBDivisorAnyOn (ModelSystem.blowup n X) (regularCurrentAny T)=
      currentBDivisorAnyOn (ModelSystem.blowup n X) (regularCurrentAny S) := by
    rw [SourceReg.currentBDivisorAnyOn_regular_eq,SourceReg.currentBDivisorAnyOn_regular_eq]
    exact hfamily
  have hI := currentIEquivalent_of_currentBDivisorAnyOn_eq
    (regularCurrentAny_idempotent T) (regularCurrentAny_idempotent S) hregclass hregfamily
  have hT : addCurrentAny (regularCurrentAny T) (divisorCurrentAny T)=T :=
    (current_decomposition_any T).symm
  have hS : addCurrentAny (regularCurrentAny S) (divisorCurrentAny T)=S :=
    (congrArg (addCurrentAny (regularCurrentAny S)) hdiv).trans (current_decomposition_any S).symm
  have hTS := currentIOrderAny_add ω hI.1 (currentIOrderAny_refl (divisorCurrentAny T))
  have hST := currentIOrderAny_add ω hI.2 (currentIOrderAny_refl (divisorCurrentAny T))
  rw [hT,hS] at hTS
  rw [hT,hS] at hST
  exact ⟨hTS,hST⟩

/-- Descent is proved from the original multiplier orders on actual original currents. -/
theorem positiveCurrentToAugmentedRoot_eq_of_IEquivalent (ω : KahlerBackground n X)
    (α : RealBottChern n X) (T S : PositiveClassCurrent ω α)
    (h : currentIOrderAny T.val S.val ∧ currentIOrderAny S.val T.val) :
    positiveCurrentToAugmentedRoot ω α T=positiveCurrentToAugmentedRoot ω α S := by
  apply Subtype.ext
  apply AugmentedNefAny.ext
  · exact currentBDivisorAnyOn_eq_of_currentIEquivalent
      (T.property.1.trans S.property.1.symm) h.1 h.2
  · exact currentCoefficientAny_eq_of_IEquivalent h.1 h.2

/-- Canonical full original quotient map: q(T) ↦ (D(T),sum_D nu(T,D) D). -/
def positiveQuotientToAugmentedRoot (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Quotient (positiveCurrentISetoid ω α) → PositiveAugmentedRoot α :=
  Quotient.lift (positiveCurrentToAugmentedRoot ω α)
    (fun T S h => positiveCurrentToAugmentedRoot_eq_of_IEquivalent ω α T S h)

theorem positiveQuotientToAugmentedRoot_injective (ω : KahlerBackground n X)
    (α : RealBottChern n X) : Function.Injective (positiveQuotientToAugmentedRoot ω α) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro T S h
  apply Quotient.sound
  exact currentIEquivalent_of_augmentedData_eq ω
    (T.property.1.trans S.property.1.symm)
    (congrArg (fun A : PositiveAugmentedRoot α => A.val.bdiv) h)
    (congrArg (fun A : PositiveAugmentedRoot α => A.val.coeff) h)

/-- Every ENTIRE original augmented object is realized internally by a genuine
positive-volume current. Actual series, coefficients, regularity, family and volume
are conclusions. No I-good or selected-trace restriction is introduced. -/
theorem exists_positiveCurrent_realizing_augmented (ω : KahlerBackground n X)
    (α : RealBottChern n X) (A : PositiveAugmentedRoot α) :
    ∃ T : PositiveClassCurrent ω α, positiveCurrentToAugmentedRoot ω α T=A := by
  let γ : RealBottChern n X := A.val.bdiv.val ModelSystem.Model.root
  let D : BigNefRoot γ := ⟨A.val.bdiv,A.property.1,A.val.isNef,rfl⟩
  obtain ⟨R,hR⟩ := exists_gCurrent_realizing ω γ D
  have hRf : currentBDivisorAnyOn (ModelSystem.blowup n X) R.val=A.val.bdiv :=
    congrArg Subtype.val hR
  obtain ⟨V,hVclass,hVcoeff,hVdiv⟩ := exists_divisorial_currentAny_of_class_sum
    ω A.val.coeff A.val.coeff_nonneg A.val.divisorClass A.val.hasSum_divisorClass
  let T := addCurrentAny R.val V
  have hTreg : regularCurrentAny T=R.val := regularCurrentAny_add_of_divisorial
    R.val V R.property.2.1 hVdiv
  have hTf : currentBDivisorAnyOn (ModelSystem.blowup n X) T=A.val.bdiv := by
    rw [←SourceReg.currentBDivisorAnyOn_regular_eq T,hTreg]
    exact hRf
  have hTc : currentClassAny T=α := by
    change currentClassAny (addCurrentAny R.val V)=α
    rw [addCurrentAny_class,R.property.1,hVclass]
    exact A.property.2
  have hTvol : 0<currentIVolumeAny T := by
    rw [currentIVolumeAny_eq_bdivisorVolume ω,hTf]
    exact A.property.1
  have hTcoeff : currentCoefficientAny T=A.val.coeff :=
    (addCurrentAny_coeff_of_regular R.val V R.property.2.1).trans hVcoeff
  refine ⟨⟨T,hTc,hTvol⟩,?_⟩
  apply Subtype.ext
  exact AugmentedNefAny.ext hTf hTcoeff

theorem positiveQuotientToAugmentedRoot_surjective (ω : KahlerBackground n X)
    (α : RealBottChern n X) : Function.Surjective (positiveQuotientToAugmentedRoot ω α) := by
  intro A
  obtain ⟨T,hT⟩ := exists_positiveCurrent_realizing_augmented ω α A
  exact ⟨Quotient.mk _ T,hT⟩

/-- WHOLE original cor:Iequiv_curr_b_div, every natural dimension and arbitrary
root class, with the original current I-equivalence and ENTIRE augmented target. -/
theorem source_Iequiv_curr_b_div (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Bijective (positiveQuotientToAugmentedRoot ω α) :=
  ⟨positiveQuotientToAugmentedRoot_injective ω α,positiveQuotientToAugmentedRoot_surjective ω α⟩

def sourceAugmentedCurrentEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Quotient (positiveCurrentISetoid ω α) ≃ PositiveAugmentedRoot α :=
  Equiv.ofBijective (positiveQuotientToAugmentedRoot ω α) (source_Iequiv_curr_b_div ω α)

/-- Exact original forward family and coefficient readback. -/
theorem sourceAugmentedCurrentEquiv_apply_mk (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : PositiveClassCurrent ω α) :
    (sourceAugmentedCurrentEquiv ω α (Quotient.mk _ T)).val.bdiv=
      currentBDivisorAnyOn (ModelSystem.blowup n X) T.val ∧
    (sourceAugmentedCurrentEquiv ω α (Quotient.mk _ T)).val.coeff=currentCoefficientAny T.val := ⟨rfl,rfl⟩

theorem sourceAugmentedCurrentEquiv_left_inverse (ω : KahlerBackground n X) (α : RealBottChern n X)
    (q : Quotient (positiveCurrentISetoid ω α)) :
    (sourceAugmentedCurrentEquiv ω α).symm (sourceAugmentedCurrentEquiv ω α q)=q :=
  (sourceAugmentedCurrentEquiv ω α).symm_apply_apply q

theorem sourceAugmentedCurrentEquiv_right_inverse (ω : KahlerBackground n X) (α : RealBottChern n X)
    (A : PositiveAugmentedRoot α) : sourceAugmentedCurrentEquiv ω α
      ((sourceAugmentedCurrentEquiv ω α).symm A)=A :=
  (sourceAugmentedCurrentEquiv ω α).apply_symm_apply A

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
