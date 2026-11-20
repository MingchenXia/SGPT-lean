import SGPT.Hodge.BDivChainZero
import SGPT.BDivisor.BlowupModelWeil
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents

/-!
# Dimension-uniform native class families

This file defines a family of actual
Bott--Chern classes over the actual model system.  The zero branch of the
pushforward lands in the actual class group (which is trivial by the checked
`realBottChern_eq_zero_of_dim_zero`), not in a proxy object.  The positive
branch is the existing class pushforward.  The local coefficient lemma concerns
actual degree-two distribution-valued forms; it is not yet a global current
construction, positivity, or the book's current b-divisor.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.BDivisor

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Class pushforward on the real model classes in every dimension. The zero
branch is forced by the actual zero target; the positive branch is unchanged. -/
def classPushforwardAny {π π' : Modification n X} (h : π ≤ π') :
    RealBottChern n π'.carrier →ₗ[ℝ] RealBottChern n π.carrier := by
  classical
  exact if hn : 0 < n then Modification.classPushforwardOfLE hn h else 0

@[simp] theorem classPushforwardAny_pos (hn : 0 < n) {π π' : Modification n X}
    (h : π ≤ π') : classPushforwardAny h = Modification.classPushforwardOfLE hn h := by
  classical
  simp [classPushforwardAny, hn]

/-- The dimension-uniform pushforward has the genuine identity law. -/
theorem classPushforwardAny_refl (π : Modification n X)
    (α : RealBottChern n π.carrier) : classPushforwardAny (le_refl π) α = α := by
  by_cases hn : 0 < n
  · simpa only [classPushforwardAny_pos hn] using
      Modification.classPushforwardOfLE_refl hn π α
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (realBottChern_eq_zero_of_dim_zero _).trans
      (realBottChern_eq_zero_of_dim_zero α).symm

/-- The genuine model-class pushforward is functorial in every dimension. -/
theorem classPushforwardAny_trans {π π' π'' : Modification n X}
    (h₁ : π ≤ π') (h₂ : π' ≤ π'') (α : RealBottChern n π''.carrier) :
    classPushforwardAny (h₁.trans h₂) α =
      classPushforwardAny h₁ (classPushforwardAny h₂ α) := by
  by_cases hn : 0 < n
  · simpa only [classPushforwardAny_pos hn] using
      Modification.classPushforwardOfLE_trans hn h₁ h₂ α
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (realBottChern_eq_zero_of_dim_zero _).trans
      (realBottChern_eq_zero_of_dim_zero _).symm

/-- The original model-class push-pull identity also retains its zero branch. -/
theorem classPushforwardAny_pullback {π π' : Modification n X} (h : π ≤ π')
    (α : RealBottChern n π.carrier) :
    classPushforwardAny h (Modification.classPullbackOfLE h α) = α := by
  by_cases hn : 0 < n
  · simpa only [classPushforwardAny_pos hn] using
      Modification.classPushforwardOfLE_classPullbackOfLE hn h α
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (realBottChern_eq_zero_of_dim_zero _).trans
      (realBottChern_eq_zero_of_dim_zero α).symm

/-- The same native compatible model-class family used by the existing
Weil b-divisor construction, with dimension-uniform pushforward. -/
def weilFamiliesAny (S : ModelSystem n X) :
    Submodule ℝ ((π : S.Model) → RealBottChern n π.1.carrier) where
  carrier := {D | ∀ (π π' : S.Model) (h : π ≤ π'),
    classPushforwardAny (show π.1 ≤ π'.1 from h) (D π') = D π}
  zero_mem' := by
    intro π π' h
    exact map_zero _
  add_mem' := by
    intro D D' hD hD' π π' h
    change classPushforwardAny (show π.1 ≤ π'.1 from h) (D π' + D' π') = D π + D' π
    rw [map_add, hD π π' h, hD' π π' h]
  smul_mem' := by
    intro c D hD π π' h
    change classPushforwardAny (show π.1 ≤ π'.1 from h) (c • D π') = c • D π
    rw [map_smul, hD π π' h]

abbrev WeilFamilyAny (S : ModelSystem n X) := ↥(weilFamiliesAny S)

/-- On every positive-dimensional system the underlying native submodule is
literally the old one. This is the required compatibility, not a new axiom. -/
theorem weilFamiliesAny_eq_pos (S : ModelSystem n X) (hn : 0 < n) :
    weilFamiliesAny S = weilBDivisorsOn S hn := by
  ext D
  simp only [weilFamiliesAny, weilBDivisorsOn, Submodule.mem_mk,
    classPushforwardAny_pos hn]

/-- Restriction of the uniform class family to the already-defined positive
Weil b-divisor type, preserving the same actual classes at every model. -/
def toExisting (S : ModelSystem n X) (hn : 0 < n) (D : WeilFamilyAny S) :
    WeilBDivisorOn S hn := by
  refine ⟨D.val, ?_⟩
  intro π π' h
  simpa only [classPushforwardAny_pos hn] using D.property π π' h

@[simp] theorem toExisting_onModel (S : ModelSystem n X) (hn : 0 < n)
    (D : WeilFamilyAny S) (π : S.Model) :
    (toExisting S hn D).onModel π = D.val π := rfl

/-- Reconstruct the uniform family from the existing positive-dimensional
family without replacing any model or any Bott--Chern class. -/
def fromExisting (S : ModelSystem n X) (hn : 0 < n) (D : WeilBDivisorOn S hn) :
    WeilFamilyAny S := by
  refine ⟨D.val, ?_⟩
  intro π π' h
  simpa only [classPushforwardAny_pos hn] using D.property π π' h

@[simp] theorem fromExisting_onModel (S : ModelSystem n X) (hn : 0 < n)
    (D : WeilBDivisorOn S hn) (π : S.Model) :
    (fromExisting S hn D).val π = D.onModel π := rfl

@[simp] theorem toExisting_fromExisting (S : ModelSystem n X) (hn : 0 < n)
    (D : WeilBDivisorOn S hn) : toExisting S hn (fromExisting S hn D) = D := by
  apply Subtype.ext
  rfl

@[simp] theorem fromExisting_toExisting (S : ModelSystem n X) (hn : 0 < n)
    (D : WeilFamilyAny S) : fromExisting S hn (toExisting S hn D) = D := by
  apply Subtype.ext
  rfl

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open TopologicalSpace SGPT.Foundations.Analysis
  SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.LocalCurrents SGPT.BDivisor

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

/-- Zero-dimensional families consist of the actual zero model classes. -/
theorem modelClass_eq_zero (S : ModelSystem 0 X) (D : WeilFamilyAny S)
    (π : S.Model) : D.val π = 0 :=
  realBottChern_eq_zero_of_dim_zero (D.val π)

/-- Actual local distribution coefficients of degree two vanish in complex
 dimension zero. Gluing and positive-dimensional pairing are separate work. -/
theorem localDistributionTwo_eq_zero
    (Ω : Opens (ComplexModel 0)) (A : DistributionForm Ω 2) : A = 0 := by
  ext v φ
  change A v φ = 0
  rw [A.map_coord_zero (0 : Fin 2) (Subsingleton.elim (v 0) 0)]
  rfl

end SGPT.Hodge.BDivChain.NativeDraft
