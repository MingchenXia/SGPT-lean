import SGPT.Hodge.SourceCurrentCorrespondence
import SGPT.Hodge.SourceDSContinuity
import SGPT.PSH.SourceNonArchimedeanPotentials

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.PSH.VariableComplexAtlas
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The actual root Cartier family, whose trace is the pullback of the given real class. -/
def rootCartierAny (α : RealBottChern n X) : WeilFamilyAny (ModelSystem.blowup n X) := by
  cases n with
  | zero => exact 0
  | succ m =>
    exact fromExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m)
      (WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root α)

/-- Every actual model trace is literally the class pullback; zero uses actual vanishing classes. -/
theorem rootCartierAny_onModel (α : RealBottChern n X) (π : (ModelSystem.blowup n X).Model) :
    (rootCartierAny α).val π =
      Modification.classPullbackOfLE (show (ModelSystem.Model.root : (ModelSystem.blowup n X).Model).1 ≤ π.1
        from ModelSystem.Model.root_le π) α := by
  cases n with
  | zero => exact (realBottChern_eq_zero_of_dim_zero _).symm
  | succ m =>
    change (WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root α).onModel π = _
    exact WeilBDivisorOn.isRealization_cartierOf ModelSystem.Model.root α π
      (ModelSystem.Model.root_le π)

/-- The original root is retained. -/
theorem rootCartierAny_root (α : RealBottChern n X) :
    (rootCartierAny α).val ModelSystem.Model.root = α := by
  rw [rootCartierAny_onModel]
  exact Modification.classPullbackOfLE_refl Modification.root α

/-- Actual linearity on the complete compatible model family. -/
theorem rootCartierAny_add (α β : RealBottChern n X) :
    rootCartierAny (α + β) = rootCartierAny α + rootCartierAny β := by
  apply Subtype.ext
  funext π
  change (rootCartierAny (α + β)).val π = (rootCartierAny α).val π + (rootCartierAny β).val π
  simp only [rootCartierAny_onModel]
  exact map_add _ _ _

theorem rootCartierAny_sub (α β : RealBottChern n X) :
    rootCartierAny (α - β) = rootCartierAny α - rootCartierAny β := by
  apply Subtype.ext
  funext π
  change (rootCartierAny (α - β)).val π = (rootCartierAny α).val π - (rootCartierAny β).val π
  simp only [rootCartierAny_onModel]
  exact map_sub _ _ _

theorem rootCartierAny_smul (c : ℝ) (α : RealBottChern n X) :
    rootCartierAny (c • α) = c • rootCartierAny α := by
  apply Subtype.ext
  funext π
  change (rootCartierAny (c • α)).val π = c • (rootCartierAny α).val π
  simp only [rootCartierAny_onModel]
  exact map_smul _ _ _

/-- Exact comparison with the existing book root Cartier family in positive dimension. -/
theorem rootCartierAny_toExisting {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y]
    (α : RealBottChern (m + 1) Y) :
    toExisting (ModelSystem.blowup (m + 1) Y) (Nat.succ_pos m) (rootCartierAny α) =
      WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root α := by
  apply WeilBDivisorOn.ext
  intro π
  change (rootCartierAny α).val π = _
  rw [rootCartierAny_onModel]
  exact (WeilBDivisorOn.isRealization_cartierOf ModelSystem.Model.root α π
    (ModelSystem.Model.root_le π)).symm

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
