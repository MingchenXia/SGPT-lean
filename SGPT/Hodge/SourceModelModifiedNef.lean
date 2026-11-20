import SGPT.Hodge.SourceNefProjective

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The literal original modified-nef epsilon-potential/prime condition, in
every dimension and on a genuine smooth representative of the actual class. -/
def ClassModifiedNefAny (κ : KahlerBackground n X) (α : RealBottChern n X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ u : X → EReal,
    IsThetaPshPotential (Quotient.out α + ε • κ.form).val u ∧
      ∀ D : SGPT.PSH.GeometricPrimeCarrier n X,
        (⨅ x ∈ D.val, squaredLogLelongNumber (n := n) u x) = 0

/-- Exact positive-dimensional comparison with the EXISTING original class
definition, including every actual prime and the original Lelong normalization. -/
theorem classModifiedNefAny_iff_existing {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (κ : KahlerBackground (m + 1) Y) (α : RealBottChern (m + 1) Y) :
    ClassModifiedNefAny κ α ↔ SGPT.Siu.ClassModifiedNefWithRespectTo κ α := by
  change SGPT.Siu.ModifiedNefWithRespectTo κ (Quotient.out α) ↔ _
  have he : SGPT.Siu.ClassModifiedNefWithRespectTo κ
      (RealBottChern.ofRepresentative (Quotient.out α)) =
      SGPT.Siu.ClassModifiedNefWithRespectTo κ α :=
    congrArg (SGPT.Siu.ClassModifiedNefWithRespectTo κ) (Quotient.out_eq α)
  exact (SGPT.Siu.classModifiedNefWithRespectTo_ofRepresentative κ _).symm.trans (Iff.of_eq he)

/-- Actual dimension-zero epsilon-PSH witnesses and the actual empty geometric
prime index prove modified nefness, rather than a proxy True branch. -/
theorem classModifiedNefAny_zero {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    (κ : KahlerBackground 0 Y) (α : RealBottChern 0 Y) : ClassModifiedNefAny κ α := by
  intro ε _hε
  refine ⟨fun _ => (0 : EReal), ?_, fun D => isEmptyElim D⟩
  exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (Quotient.out α + ε • κ.form))
    (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)

variable [CompactSpace X]

/-- The complete original condition is independent of the actual reference
Kähler form, in every dimension. -/
theorem classModifiedNefAny_kahler_independent (κ ζ : KahlerBackground n X)
    (α : RealBottChern n X) : ClassModifiedNefAny κ α ↔ ClassModifiedNefAny ζ α := by
  cases n with
  | zero => exact ⟨fun _ => classModifiedNefAny_zero ζ α,
      fun _ => classModifiedNefAny_zero κ α⟩
  | succ m =>
    rw [classModifiedNefAny_iff_existing, classModifiedNefAny_iff_existing]
    exact SGPT.Siu.classModifiedNefWithRespectTo_iff κ ζ α

variable [ConnectedSpace X]

/-- WHOLE cor:mn_level_nefb on the original literal book model family, all
dimensions, every model and every Kähler reference. The existing actual
directed-net nef predicate is unchanged and no bigness premise is added. -/
theorem source_mn_level_nefb (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) :
    IsNefAny D ↔ ∀ (π : (ModelSystem.blowup n X).Model)
      (κ : KahlerBackground n π.1.carrier), ClassModifiedNefAny κ (D.val π) := by
  cases n with
  | zero => exact ⟨fun _ _ κ => classModifiedNefAny_zero κ _, fun _ => isNefAny_zero D⟩
  | succ m =>
    constructor
    · intro hD π κ
      exact (classModifiedNefAny_iff_existing κ _).mpr
        ((WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ω⟩
          ((isNefAny_iff_existing (Nat.succ_pos m) D).mp hD) π).2 κ)
    · intro hD
      apply (isNefAny_iff_existing (Nat.succ_pos m) D).mpr
      exact isNef_of_allModelModifiedNef ω (toExisting _ (Nat.succ_pos m) D)
        (fun π κ => (classModifiedNefAny_iff_existing κ _).mp (hD π κ))

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
