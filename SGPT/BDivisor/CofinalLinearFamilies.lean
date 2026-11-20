import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic

set_option autoImplicit false

namespace SGPT.BDivisor

universe u v w z

variable {R : Type u} [Semiring R] {I : Type v} [Preorder I]
  {E : I → Type w} [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]

/-- Compatible families for linear transition maps ordered by domination. -/
def compatibleLinearFamilies
    (push : ∀ ⦃i j : I⦄, i ≤ j → E j →ₗ[R] E i) :
    Submodule R (∀ i, E i) where
  carrier := {a | ∀ i j (h : i ≤ j), push h (a j) = a i}
  zero_mem' := by
    intro i j h
    exact map_zero _
  add_mem' := by
    intro a b ha hb i j h
    change push h (a j + b j) = a i + b i
    rw [map_add, ha i j h, hb i j h]
  smul_mem' := by
    intro c a ha i j h
    change push h (c • a j) = c • a i
    rw [map_smul, ha i j h]

/-- Restriction along a monotone cofinal map from a directed index preorder is a
linear equivalence on compatible families. -/
noncomputable def compatibleLinearFamiliesCofinalEquiv
    (push : ∀ ⦃i j : I⦄, i ≤ j → E j →ₗ[R] E i)
    (pushRefl : ∀ (i : I) (x : E i), push (le_refl i) x = x)
    (pushTrans : ∀ ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : E k),
      push (hij.trans hjk) x = push hij (push hjk x))
    {J : Type z} [Preorder J] (F : J → I) (hF : Monotone F)
    (directedJ : ∀ a b : J, ∃ c, a ≤ c ∧ b ≤ c)
    (cofinal : ∀ i : I, ∃ j : J, i ≤ F j) :
    compatibleLinearFamilies push ≃ₗ[R]
      compatibleLinearFamilies (E := fun j => E (F j)) (fun {i j} h => push (hF h)) := by
  classical
  let subPush : ∀ ⦃a b : J⦄, a ≤ b → E (F b) →ₗ[R] E (F a) :=
    fun {a b} h => push (hF h)
  let jFor (i : I) : J := (cofinal i).choose
  have dominates (i : I) : i ≤ F (jFor i) := (cofinal i).choose_spec
  let extend (b : compatibleLinearFamilies subPush) (i : I) : E i :=
    push (dominates i) (b.val (jFor i))
  have extend_at (b : compatibleLinearFamilies subPush) (i : I) (j : J) (h : i ≤ F j) :
      extend b i = push h (b.val j) := by
    obtain ⟨k, hkChosen, hk⟩ := directedJ (jFor i) j
    have hChosen : push (hF hkChosen) (b.val k) = b.val (jFor i) :=
      b.property (jFor i) k hkChosen
    have hOther : push (hF hk) (b.val k) = b.val j := b.property j k hk
    calc
      extend b i = push (dominates i) (push (hF hkChosen) (b.val k)) := by
        change push (dominates i) (b.val (jFor i)) = _
        rw [hChosen]
      _ = push ((dominates i).trans (hF hkChosen)) (b.val k) :=
        (pushTrans (dominates i) (hF hkChosen) _).symm
      _ = push h (push (hF hk) (b.val k)) := pushTrans h (hF hk) _
      _ = push h (b.val j) := by rw [hOther]
  refine
    { toFun := fun a => ⟨fun j => a.val (F j), fun j k h => a.property (F j) (F k) (hF h)⟩
      invFun := fun b => ⟨extend b, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  · intro i i' h
    change push h (extend b i') = extend b i
    rw [extend_at b i' (jFor i') (dominates i'),
      extend_at b i (jFor i') (h.trans (dominates i'))]
    exact (pushTrans h (dominates i') _).symm
  · intro a
    apply Subtype.ext
    funext i
    exact a.property i (F (jFor i)) (dominates i)
  · intro b
    apply Subtype.ext
    funext j
    change extend b (F j) = b.val j
    exact (extend_at b (F j) j (le_refl _)).trans (pushRefl _ _)

end SGPT.BDivisor
