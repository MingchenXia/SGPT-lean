import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Order.Fin.Tuple
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.Okounkov

private def integerTailEquiv {m : ℕ}
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ)) :
    (Fin m → ℤ) ≃ (Fin m → ℤ) :=
  (toLex : (Fin m → ℤ) ≃ Lex (Fin m → ℤ)).trans
    (g.toEquiv.trans (ofLex : Lex (Fin m → ℤ) ≃ (Fin m → ℤ)))

/-- The actual source block map is a genuine bijection, constructed from the
existing finite head/tail and product-shear equivalences. -/
def integerCorrectionStepEquiv {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ)) :
    Lex (Fin (m + 1) → ℤ) ≃ Lex (Fin (m + 1) → ℤ) :=
  (ofLex : Lex (Fin (m + 1) → ℤ) ≃ (Fin (m + 1) → ℤ)).trans
    ((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).symm.trans
      ((Equiv.prodShear (Equiv.refl ℤ)
        (fun a => (integerTailEquiv g).trans (Equiv.addRight (fun i => a * c i)))).trans
        ((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).trans
          (toLex : (Fin (m + 1) → ℤ) ≃ Lex (Fin (m + 1) → ℤ)))))

@[simp] theorem integerCorrectionStepEquiv_apply_zero {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ))
    (v : Lex (Fin (m + 1) → ℤ)) :
    integerCorrectionStepEquiv c g v 0 = v 0 := rfl

@[simp] theorem integerCorrectionStepEquiv_apply_succ {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ))
    (v : Lex (Fin (m + 1) → ℤ)) (i : Fin m) :
    integerCorrectionStepEquiv c g v i.succ =
      ofLex (g (toLex (fun j => v j.succ))) i + v 0 * c i := rfl

/-- Integer distributivity and actual tail additivity give the literal
additive law; no matrix or additivity certificate is assumed. -/
theorem integerCorrectionStepEquiv_map_add {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ))
    (u v : Lex (Fin (m + 1) → ℤ)) :
    integerCorrectionStepEquiv c g (u + v) =
      integerCorrectionStepEquiv c g u + integerCorrectionStepEquiv c g v := by
  apply ofLex.injective
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  change ofLex (g (toLex (fun k => u k.succ) + toLex (fun k => v k.succ))) j +
      (u 0 + v 0) * c j =
    (ofLex (g (toLex (fun k => u k.succ))) j + u 0 * c j) +
      (ofLex (g (toLex (fun k => v k.succ))) j + v 0 * c j)
  rw [map_add]
  change (ofLex (g (toLex (fun k => u k.succ))) j +
      ofLex (g (toLex (fun k => v k.succ))) j) + (u 0 + v 0) * c j = _
  ring

private theorem integerLex_head_tail_lt_iff {m : ℕ}
    (u v : Lex (Fin (m + 1) → ℤ)) :
    u < v ↔ u 0 < v 0 ∨ u 0 = v 0 ∧
      toLex (fun i : Fin m => u i.succ) < toLex (fun i : Fin m => v i.succ) := by
  have hu : Fin.cons (u 0) (fun i => u i.succ) = ofLex u := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hv : Fin.cons (v 0) (fun i => v i.succ) = ofLex v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change Pi.Lex (· < ·) (· < ·) (ofLex u) (ofLex v) ↔ _
  rw [← hu, ← hv]
  exact Fin.pi_lex_lt_cons_cons (s := (· < ·))

/-- Strict lexicographic order is preserved and reflected for every integer
row, including arbitrary negative entries and the empty tail. -/
theorem integerCorrectionStepEquiv_lt_iff {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ))
    (u v : Lex (Fin (m + 1) → ℤ)) :
    integerCorrectionStepEquiv c g u < integerCorrectionStepEquiv c g v ↔ u < v := by
  rw [integerLex_head_tail_lt_iff, integerLex_head_tail_lt_iff]
  simp only [integerCorrectionStepEquiv_apply_zero, integerCorrectionStepEquiv_apply_succ]
  change (u 0 < v 0 ∨ u 0 = v 0 ∧
      g (toLex (fun i => u i.succ)) + toLex (fun i => u 0 * c i) <
        g (toLex (fun i => v i.succ)) + toLex (fun i => v 0 * c i)) ↔
    (u 0 < v 0 ∨ u 0 = v 0 ∧
      toLex (fun i : Fin m => u i.succ) < toLex (fun i : Fin m => v i.succ))
  by_cases hhead : u 0 = v 0
  · have htail : g (toLex (fun i => u i.succ)) < g (toLex (fun i => v i.succ)) ↔
        toLex (fun i : Fin m => u i.succ) < toLex (fun i : Fin m => v i.succ) :=
      lt_iff_lt_of_le_iff_le' (map_le_map_iff g) (map_le_map_iff g)
    simp only [hhead, add_lt_add_iff_right, htail]
  · simp only [hhead, false_and, or_false]

/-- The source block is an actual ordered additive automorphism of the
original integer lexicographic group. -/
def integerCorrectionStep {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ)) :
    Lex (Fin (m + 1) → ℤ) ≃+o Lex (Fin (m + 1) → ℤ) where
  toEquiv := integerCorrectionStepEquiv c g
  map_add' := integerCorrectionStepEquiv_map_add c g
  map_le_map_iff' := by
    intro u v
    change integerCorrectionStepEquiv c g u ≤ integerCorrectionStepEquiv c g v ↔ u ≤ v
    exact le_iff_lt_or_eq.trans
      ((or_congr (integerCorrectionStepEquiv_lt_iff c g u v)
        (integerCorrectionStepEquiv c g).injective.eq_iff).trans le_iff_lt_or_eq.symm)

/-- The original one-dimensional correction is literally the identity,
because its true tail has no coordinates. -/
theorem integerCorrectionStep_dim_one (c : Fin 0 → ℤ)
    (g : Lex (Fin 0 → ℤ) ≃+o Lex (Fin 0 → ℤ)) :
    integerCorrectionStep c g = OrderAddMonoidIso.refl (Lex (Fin 1 → ℤ)) := by
  apply DFunLike.ext
  intro v
  apply ofLex.injective
  funext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rfl

end SGPT.Okounkov
