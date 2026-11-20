import SGPT.Hodge.SourceAugmentedProjectiveFamilies

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

omit [MeasurableSpace X] [BorelSpace X] in
/-- Identity law in the actual full augmented diagram. -/
theorem positiveAugmentedTransition_refl (ω : KahlerBackground n X) (α : RealBottChern n X)
    (κ : SourceKahlerForm n X) (A : PositiveAugmentedRoot (α+indexClass κ)) :
    positiveAugmentedTransition ω α (sourceKahlerFormLE_refl κ) A=A := by
  apply Subtype.ext
  apply AugmentedNefAny.ext
  · change A.val.bdiv+rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ κ))=A.val.bdiv
    rw [indexDifference_cartier,sub_self,add_zero]
  · rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- Composition law for every ordered triple of actual original Kähler forms. -/
theorem positiveAugmentedTransition_comp (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ ξ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ) (hζξ : sourceKahlerFormLE ζ ξ)
    (A : PositiveAugmentedRoot (α+indexClass κ)) :
    positiveAugmentedTransition ω α hζξ (positiveAugmentedTransition ω α hκζ A)=
      positiveAugmentedTransition ω α (sourceKahlerFormLE_trans hκζ hζξ) A := by
  apply Subtype.ext
  apply AugmentedNefAny.ext
  · change A.val.bdiv+rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ))+
      rootCartierAny (RealBottChern.ofRepresentative (indexDifference ζ ξ))=
        A.val.bdiv+rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ξ))
    simp only [indexDifference_cartier]
    abel
  · rfl

theorem positiveQuotientTransition_refl (ω : KahlerBackground n X) (α : RealBottChern n X)
    (κ : SourceKahlerForm n X) (q : Quotient (positiveCurrentISetoid ω (α+indexClass κ))) :
    positiveQuotientTransition ω α (sourceKahlerFormLE_refl κ) q=q := by
  apply (sourceAugmentedCurrentEquiv ω (α+indexClass κ)).injective
  simp only [positiveQuotientTransition,Equiv.apply_symm_apply]
  exact positiveAugmentedTransition_refl ω α κ _

theorem positiveQuotientTransition_comp (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ ξ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ) (hζξ : sourceKahlerFormLE ζ ξ)
    (q : Quotient (positiveCurrentISetoid ω (α+indexClass κ))) :
    positiveQuotientTransition ω α hζξ (positiveQuotientTransition ω α hκζ q)=
      positiveQuotientTransition ω α (sourceKahlerFormLE_trans hκζ hζξ) q := by
  apply (sourceAugmentedCurrentEquiv ω (α+indexClass ξ)).injective
  simp only [positiveQuotientTransition,Equiv.apply_symm_apply]
  exact positiveAugmentedTransition_comp ω α hκζ hζξ _

/-- The WHOLE original current inverse limit. Every literal geometric Kähler form
is an index, every component is the entire original positive-volume current I-quotient,
and transitions are exactly induced by actual smooth-current addition. -/
def PositiveCurrentProjectiveLimit (ω : KahlerBackground n X) (α : RealBottChern n X) :=
  {q : ∀ κ : SourceKahlerForm n X, Quotient (positiveCurrentISetoid ω (α+indexClass κ)) //
    ∀ (κ ζ : SourceKahlerForm n X) (h : sourceKahlerFormLE κ ζ),
      positiveQuotientTransition ω α h (q κ)=q ζ}

def augmentedLimitToCurrentLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : AugmentedPositiveLimit ω α) : PositiveCurrentProjectiveLimit ω α :=
  ⟨fun κ => (sourceAugmentedCurrentEquiv ω (α+indexClass κ)).symm (F.val κ),by
    intro κ ζ h
    apply (sourceAugmentedCurrentEquiv ω (α+indexClass ζ)).injective
    simp only [positiveQuotientTransition,Equiv.apply_symm_apply]
    exact F.property κ ζ h⟩

def currentLimitToAugmentedLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (q : PositiveCurrentProjectiveLimit ω α) : AugmentedPositiveLimit ω α :=
  ⟨fun κ => sourceAugmentedCurrentEquiv ω (α+indexClass κ) (q.val κ),by
    intro κ ζ h
    have he := congrArg (sourceAugmentedCurrentEquiv ω (α+indexClass ζ)) (q.property κ ζ h)
    simpa only [positiveQuotientTransition,Equiv.apply_symm_apply] using he⟩

/-- Whole diagram correspondence, retaining every original form and both inverse laws. -/
def augmentedCurrentLimitEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    AugmentedPositiveLimit ω α ≃ PositiveCurrentProjectiveLimit ω α where
  toFun := augmentedLimitToCurrentLimit ω α
  invFun := currentLimitToAugmentedLimit ω α
  left_inv F := by
    apply Subtype.ext
    funext κ
    exact (sourceAugmentedCurrentEquiv ω (α+indexClass κ)).apply_symm_apply (F.val κ)
  right_inv q := by
    apply Subtype.ext
    funext κ
    exact (sourceAugmentedCurrentEquiv ω (α+indexClass κ)).symm_apply_apply (q.val κ)

/-- WHOLE original cor:nef_b_degenerate_2, all natural dimensions and arbitrary
root classes. No positive-volume restriction on the original augmented target,
countable replacement of the Kähler index, supplied initial form or cofinality
certificate appears. -/
def sourceAugmentedCurrentProjectiveEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    AugmentedRoot α ≃ PositiveCurrentProjectiveLimit ω α :=
  (augmentedRootPositiveLimitEquiv ω α).trans (augmentedCurrentLimitEquiv ω α)

theorem source_nef_b_degenerate_2 (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Bijective (sourceAugmentedCurrentProjectiveEquiv ω α) :=
  (sourceAugmentedCurrentProjectiveEquiv ω α).bijective

/-- Exact family and coefficient readback at EVERY original Kähler-form index. -/
theorem sourceAugmentedCurrentProjectiveEquiv_component (ω : KahlerBackground n X)
    (α : RealBottChern n X) (A : AugmentedRoot α) (κ : SourceKahlerForm n X) :
    (sourceAugmentedCurrentEquiv ω (α+indexClass κ)
      ((sourceAugmentedCurrentProjectiveEquiv ω α A).val κ)).val.bdiv=A.val.bdiv+indexCartier κ ∧
    (sourceAugmentedCurrentEquiv ω (α+indexClass κ)
      ((sourceAugmentedCurrentProjectiveEquiv ω α A).val κ)).val.coeff=A.val.coeff := by
  have h := (sourceAugmentedCurrentEquiv ω (α+indexClass κ)).apply_symm_apply
    (augmentedRootComponent ω α A κ)
  exact ⟨congrArg (fun B : PositiveAugmentedRoot (α+indexClass κ) => B.val.bdiv) h,
    congrArg (fun B : PositiveAugmentedRoot (α+indexClass κ) => B.val.coeff) h⟩

/-- Exact inverse datum, independently of which ORIGINAL Kähler-form component is read. -/
theorem sourceAugmentedCurrentProjectiveEquiv_inverse_component (ω : KahlerBackground n X)
    (α : RealBottChern n X) (q : PositiveCurrentProjectiveLimit ω α) (κ : SourceKahlerForm n X) :
    ((sourceAugmentedCurrentProjectiveEquiv ω α).symm q).val.bdiv=
      (sourceAugmentedCurrentEquiv ω (α+indexClass κ) (q.val κ)).val.bdiv-indexCartier κ ∧
    ((sourceAugmentedCurrentProjectiveEquiv ω α).symm q).val.coeff=
      (sourceAugmentedCurrentEquiv ω (α+indexClass κ) (q.val κ)).val.coeff :=
  ⟨recoverAugmentedRoot_bdiv_at_every_index ω α (currentLimitToAugmentedLimit ω α q) κ,
    recoverAugmentedRoot_coeff_at_every_index ω α (currentLimitToAugmentedLimit ω α q) κ⟩

theorem sourceAugmentedCurrentProjectiveEquiv_left_inverse (ω : KahlerBackground n X)
    (α : RealBottChern n X) (A : AugmentedRoot α) :
    (sourceAugmentedCurrentProjectiveEquiv ω α).symm (sourceAugmentedCurrentProjectiveEquiv ω α A)=A :=
  (sourceAugmentedCurrentProjectiveEquiv ω α).symm_apply_apply A

theorem sourceAugmentedCurrentProjectiveEquiv_right_inverse (ω : KahlerBackground n X)
    (α : RealBottChern n X) (q : PositiveCurrentProjectiveLimit ω α) :
    sourceAugmentedCurrentProjectiveEquiv ω α ((sourceAugmentedCurrentProjectiveEquiv ω α).symm q)=q :=
  (sourceAugmentedCurrentProjectiveEquiv ω α).apply_symm_apply q

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
