import SGPT.Hodge.SourceNefProjectiveFamilies

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
  [CompactSpace X] [ConnectedSpace X]

omit [CompactSpace X] [ConnectedSpace X] in
theorem indexClass_ofBackground (κ : KahlerBackground n X) :
    indexClass (sourceKahlerFormOfBackground κ) = RealBottChern.ofRepresentative κ.form :=
  RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (sourceKahlerFormRepresentative_geometricallyEq κ)

/-- All actual Kähler shifts of the original family, with their actual transitions. -/
def nefToBigLimit (ω : KahlerBackground n X) (α : RealBottChern n X)
    (D : NefRoot α) : BigNefProjectiveLimit ω α :=
  ⟨fun κ => nefRootComponent ω α D κ, by
    intro κ ζ hκζ
    apply Subtype.ext
    change D.val + indexCartier κ +
      rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)) =
      D.val + indexCartier ζ
    rw [indexDifference_cartier]
    abel⟩

/-- A family is recovered by subtracting one genuine root Cartier family.
The next theorem proves this is independent of the initially selected index. -/
def recoverFamily (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) : WeilFamilyAny (ModelSystem.blowup n X) :=
  (F.val (sourceKahlerFormOfBackground ω)).val - indexCartier (sourceKahlerFormOfBackground ω)

theorem recoverFamily_eq_at_every_index (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) (κ : SourceKahlerForm n X) :
    recoverFamily ω α F = (F.val κ).val - indexCartier κ := by
  let κ₀ := sourceKahlerFormOfBackground ω
  let ζ := sourceKahlerFormCommonUpper κ₀ κ
  have h₀ := congrArg Subtype.val
    (F.property κ₀ ζ (sourceKahlerFormLE_commonUpper_left κ₀ κ))
  have hκ := congrArg Subtype.val
    (F.property κ ζ (sourceKahlerFormLE_commonUpper_right κ₀ κ))
  change (F.val κ₀).val +
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ₀ ζ)) = (F.val ζ).val at h₀
  change (F.val κ).val +
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)) = (F.val ζ).val at hκ
  rw [indexDifference_cartier] at h₀ hκ
  change (F.val κ₀).val - indexCartier κ₀ = (F.val κ).val - indexCartier κ
  calc
    (F.val κ₀).val - indexCartier κ₀ = (F.val ζ).val - indexCartier ζ := by rw [← h₀]; abel
    _ = (F.val κ).val - indexCartier κ := by rw [← hκ]; abel

theorem recoverFamily_add_indexCartier (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) (κ : SourceKahlerForm n X) :
    recoverFamily ω α F + indexCartier κ = (F.val κ).val := by
  rw [recoverFamily_eq_at_every_index ω α F κ]
  exact sub_add_cancel _ _

theorem recoverFamily_isNef (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) : IsNefAny (recoverFamily ω α F) := by
  apply isNefAny_of_forall_add_rootKahler ω
  intro κ
  have he := recoverFamily_add_indexCartier ω α F (sourceKahlerFormOfBackground κ)
  change recoverFamily ω α F + rootCartierAny
    (indexClass (sourceKahlerFormOfBackground κ)) = _ at he
  have he' : recoverFamily ω α F +
      rootCartierAny (RealBottChern.ofRepresentative κ.form) =
      (F.val (sourceKahlerFormOfBackground κ)).val :=
    (congrArg (fun c => recoverFamily ω α F + rootCartierAny c)
      (indexClass_ofBackground κ)).symm.trans he
  exact he'.symm ▸ (F.val (sourceKahlerFormOfBackground κ)).property.2.1

theorem recoverFamily_root (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) :
    (recoverFamily ω α F).val ModelSystem.Model.root = α := by
  change (F.val (sourceKahlerFormOfBackground ω)).val.val ModelSystem.Model.root -
    (indexCartier (sourceKahlerFormOfBackground ω)).val ModelSystem.Model.root = α
  rw [(F.val (sourceKahlerFormOfBackground ω)).property.2.2, indexCartier_root]
  exact add_sub_cancel_right α _

def bigLimitToNef (ω : KahlerBackground n X) (α : RealBottChern n X)
    (F : BigNefProjectiveLimit ω α) : NefRoot α :=
  ⟨recoverFamily ω α F, recoverFamily_isNef ω α F, recoverFamily_root ω α F⟩

/-- Both inverse laws on the whole original all-index family sets. -/
def nefRootBigLimitEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    NefRoot α ≃ BigNefProjectiveLimit ω α where
  toFun := nefToBigLimit ω α
  invFun := bigLimitToNef ω α
  left_inv D := by
    apply Subtype.ext
    change D.val + indexCartier (sourceKahlerFormOfBackground ω) -
      indexCartier (sourceKahlerFormOfBackground ω) = D.val
    exact add_sub_cancel_right _ _
  right_inv F := by
    apply Subtype.ext
    funext κ
    apply Subtype.ext
    exact recoverFamily_add_indexCartier ω α F κ

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
