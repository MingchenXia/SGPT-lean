import SGPT.Hodge.SourceNefProjectiveEquiv
import SGPT.Hodge.SourceGCurrentSmoothShift
import SGPT.PSH.SourceNonArchimedeanVolume

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The actual physical reverse-domination index is directed, with genuine
Kähler common lower forms, not a cofinality assumption. -/
theorem sourceKahlerIndex_reverse_directed (κ ζ : SourceKahlerForm n X) :
    ∃ ξ : SourceKahlerForm n X, sourceKahlerFormLE ξ κ ∧ sourceKahlerFormLE ξ ζ :=
  sourceKahlerForm_commonLower κ ζ

/-- Identity law of the original quotient transition. -/
theorem quotientTransition_refl (ω : KahlerBackground n X) (α : RealBottChern n X)
    (κ : SourceKahlerForm n X) (q : Quotient (gCurrentISetoid ω (α + indexClass κ))) :
    quotientTransition ω α (sourceKahlerFormLE_refl κ) q = q := by
  apply (sourceCurrentBDivisorEquiv ω (α + indexClass κ)).injective
  simp only [quotientTransition, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (sourceCurrentBDivisorEquiv ω (α + indexClass κ) q).val +
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ κ)) = _
  rw [indexDifference_cartier, sub_self, add_zero]

/-- Composition law of the original quotient transition, for every ordered triple. -/
theorem quotientTransition_comp (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ ξ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (hζξ : sourceKahlerFormLE ζ ξ)
    (q : Quotient (gCurrentISetoid ω (α + indexClass κ))) :
    quotientTransition ω α hζξ (quotientTransition ω α hκζ q) =
      quotientTransition ω α (sourceKahlerFormLE_trans hκζ hζξ) q := by
  apply (sourceCurrentBDivisorEquiv ω (α + indexClass ξ)).injective
  simp only [quotientTransition, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (sourceCurrentBDivisorEquiv ω (α + indexClass κ) q).val +
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)) +
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference ζ ξ)) =
    (sourceCurrentBDivisorEquiv ω (α + indexClass κ) q).val +
      rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ξ))
  simp only [indexDifference_cartier]
  abel

/-- The WHOLE original inverse limit: every geometric Kähler form is an index,
every component is the entire original G(alpha+omega)/~I, and compatibility uses
exactly the transition induced by T↦T+omega'-omega. -/
def CurrentProjectiveLimit (ω : KahlerBackground n X) (α : RealBottChern n X) :=
  {q : ∀ κ : SourceKahlerForm n X, Quotient (gCurrentISetoid ω (α + indexClass κ)) //
    ∀ (κ ζ : SourceKahlerForm n X) (h : sourceKahlerFormLE κ ζ),
      quotientTransition ω α h (q κ) = q ζ}

def bigLimitToCurrentLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) : CurrentProjectiveLimit ω α :=
  ⟨fun κ => (sourceCurrentBDivisorEquiv ω (α + indexClass κ)).symm (F.val κ), by
    intro κ ζ h
    apply (sourceCurrentBDivisorEquiv ω (α + indexClass ζ)).injective
    simp only [quotientTransition, Equiv.apply_symm_apply]
    exact F.property κ ζ h⟩

def currentLimitToBigLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (q : CurrentProjectiveLimit ω α) : BigNefProjectiveLimit ω α :=
  ⟨fun κ => sourceCurrentBDivisorEquiv ω (α + indexClass κ) (q.val κ), by
    intro κ ζ h
    have he := congrArg (sourceCurrentBDivisorEquiv ω (α + indexClass ζ)) (q.property κ ζ h)
    simpa only [quotientTransition, Equiv.apply_symm_apply] using he⟩

/-- Pointwise actual-current correspondence respects the full original diagram. -/
def bigCurrentLimitEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    BigNefProjectiveLimit ω α ≃ CurrentProjectiveLimit ω α where
  toFun := bigLimitToCurrentLimit ω α
  invFun := currentLimitToBigLimit ω α
  left_inv F := by
    apply Subtype.ext
    funext κ
    exact (sourceCurrentBDivisorEquiv ω (α + indexClass κ)).apply_symm_apply (F.val κ)
  right_inv q := by
    apply Subtype.ext
    funext κ
    exact (sourceCurrentBDivisorEquiv ω (α + indexClass κ)).symm_apply_apply (q.val κ)

/-- WHOLE cor:nef_b_degenerate_1, all dimensions and all original root classes.
No alpha-big assumption, positive-mass restriction on the original nef family,
countable replacement of the index or output certificate is introduced. -/
def sourceNefCurrentProjectiveEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    NefRoot α ≃ CurrentProjectiveLimit ω α :=
  (nefRootBigLimitEquiv ω α).trans (bigCurrentLimitEquiv ω α)

theorem source_nef_b_degenerate_1 (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Bijective (sourceNefCurrentProjectiveEquiv ω α) :=
  (sourceNefCurrentProjectiveEquiv ω α).bijective

/-- Exact natural forward readback at EVERY original Kähler-form index. -/
theorem sourceNefCurrentProjectiveEquiv_component (ω : KahlerBackground n X)
    (α : RealBottChern n X) (D : NefRoot α) (κ : SourceKahlerForm n X) :
    (sourceCurrentBDivisorEquiv ω (α + indexClass κ)
      ((sourceNefCurrentProjectiveEquiv ω α D).val κ)).val = D.val + indexCartier κ := by
  exact congrArg Subtype.val
    ((sourceCurrentBDivisorEquiv ω (α + indexClass κ)).apply_symm_apply
      (nefRootComponent ω α D κ))

/-- Exact inverse family, independently of which actual Kähler index is read. -/
theorem sourceNefCurrentProjectiveEquiv_inverse_component (ω : KahlerBackground n X)
    (α : RealBottChern n X) (q : CurrentProjectiveLimit ω α) (κ : SourceKahlerForm n X) :
    ((sourceNefCurrentProjectiveEquiv ω α).symm q).val =
      (sourceCurrentBDivisorEquiv ω (α + indexClass κ) (q.val κ)).val - indexCartier κ :=
  recoverFamily_eq_at_every_index ω α (currentLimitToBigLimit ω α q) κ

theorem sourceNefCurrentProjectiveEquiv_left_inverse (ω : KahlerBackground n X)
    (α : RealBottChern n X) (D : NefRoot α) :
    (sourceNefCurrentProjectiveEquiv ω α).symm (sourceNefCurrentProjectiveEquiv ω α D) = D :=
  (sourceNefCurrentProjectiveEquiv ω α).symm_apply_apply D

theorem sourceNefCurrentProjectiveEquiv_right_inverse (ω : KahlerBackground n X)
    (α : RealBottChern n X) (q : CurrentProjectiveLimit ω α) :
    sourceNefCurrentProjectiveEquiv ω α ((sourceNefCurrentProjectiveEquiv ω α).symm q) = q :=
  (sourceNefCurrentProjectiveEquiv ω α).apply_symm_apply q

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
