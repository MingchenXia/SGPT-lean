import Mathlib.Algebra.Module.GradedModule

/-! # The literal integral grading of a nonnegative external direct sum -/

open scoped DirectSum
open DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

universe u v

variable (K : Type u) [Semiring K] (E : ℕ → Type v)
  [∀ d, AddCommMonoid (E d)] [∀ d, Module K (E d)]

/-- A degree of the actual external direct sum consists of the literal sequences supported there. -/
def nonnegativeDirectSumPiece (k : ℤ) : Submodule K (⨁ d, E d) where
  carrier := {x | ∀ d : ℕ, (d : ℤ) ≠ k → x d = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy d hd; simp [hx d hd, hy d hd]
  smul_mem' := by
    intro c x hx d hd
    change c • x d = 0
    rw [hx d hd, smul_zero]

/-- The actual degree inclusion has its true singleton support. -/
def nonnegativeDirectSumPieceInclusion (d : ℕ) : E d →ₗ[K] nonnegativeDirectSumPiece K E d :=
  (DirectSum.lof K ℕ E d).codRestrict _ (by
    intro x e he
    exact DirectSum.of_eq_of_ne d e x (by exact_mod_cast he))

/-- Each actual homogeneous sequence is its unique actual singleton component. -/
theorem nonnegativeDirectSumPiece_eq_single (d : ℕ)
    (x : nonnegativeDirectSumPiece K E d) :
    (x : ⨁ e, E e) = DirectSum.lof K ℕ E d (x.val d) := by
  ext e
  by_cases h : e = d
  · subst e; simp
  · rw [x.property e (by exact_mod_cast h)]
    exact (DirectSum.of_eq_of_ne d e (x.val d) h).symm

/-- An integral degree outside the nonnegative integers is literally zero. -/
theorem nonnegativeDirectSumPiece_eq_bot (k : ℤ) (hk : k < 0) :
    nonnegativeDirectSumPiece K E k = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    ext d
    exact hx d (by omega)
  · exact bot_le

/-- The real singleton components produce the actual native integral decomposition map. -/
def nonnegativeDirectSumDecompose : (⨁ d, E d) →ₗ[K]
    ⨁ k : ℤ, nonnegativeDirectSumPiece K E k :=
  DirectSum.toModule K ℕ _ (fun d =>
    (DirectSum.lof K ℤ (fun k => nonnegativeDirectSumPiece K E k) (d : ℤ)).comp
      (nonnegativeDirectSumPieceInclusion K E d))

/-- Summing the actual components recovers the original external sequence. -/
theorem nonnegativeDirectSumDecompose_left_inv :
    DirectSum.coeLinearMap (nonnegativeDirectSumPiece K E) ∘ₗ
      nonnegativeDirectSumDecompose K E = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  simp [nonnegativeDirectSumDecompose, nonnegativeDirectSumPieceInclusion]
  rfl

/-- Every integral homogeneous component is recovered by the actual singleton decomposition. -/
theorem nonnegativeDirectSumDecompose_right_inv :
    nonnegativeDirectSumDecompose K E ∘ₗ
      DirectSum.coeLinearMap (nonnegativeDirectSumPiece K E) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro k
  apply LinearMap.ext
  intro x
  by_cases hk : 0 ≤ k
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    change nonnegativeDirectSumDecompose K E
      (DirectSum.coeLinearMap (nonnegativeDirectSumPiece K E)
        (DirectSum.lof K ℤ _ (d : ℤ) x)) = DirectSum.lof K ℤ _ (d : ℤ) x
    rw [DirectSum.coeLinearMap_lof,
      nonnegativeDirectSumPiece_eq_single K E d x]
    simp only [nonnegativeDirectSumDecompose, DirectSum.toModule_lof,
      LinearMap.comp_apply]
    congr 1
    apply Subtype.ext
    exact (nonnegativeDirectSumPiece_eq_single K E d x).symm
  · have hx : x = 0 := by
      apply Subtype.ext
      ext d
      exact x.property d (by omega)
    subst x
    simp

/-- The real nonnegative external direct sum has a native integral internal decomposition. -/
instance nonnegativeDirectSumDecomposition :
    DirectSum.Decomposition (nonnegativeDirectSumPiece K E) :=
  DirectSum.Decomposition.ofLinearMap (nonnegativeDirectSumPiece K E)
    (nonnegativeDirectSumDecompose K E)
    (nonnegativeDirectSumDecompose_left_inv K E)
    (nonnegativeDirectSumDecompose_right_inv K E)

end

end SGPT.Foundations.Schemes
