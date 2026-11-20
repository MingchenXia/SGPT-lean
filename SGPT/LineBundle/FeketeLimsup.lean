import SGPT.LineBundle.Fekete
import Mathlib.Order.LiminfLimsup

/-!
# The revised pointwise limsup version of Fekete's lemma

Source: SGPT revision de08f12f, chapter_testcurve.tex:1175-1179,
equation eq:limkGammaFk. This abstract producer does not assert the
superadditivity of the actual USC-regularized section potentials.
The value at degree zero is unrestricted; negative infinity may occur in
arbitrarily many positive degrees.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.LineBundle

open Filter Set
open scoped Topology

/-- The limsup of normalized positive-index superadditive terms is their
supremum when no positive-index value is positive infinity. The supremum
itself may be positive infinity. Eventual finiteness and linear upper or
lower bounds are unnecessary. -/
theorem EReal.limsup_div_eq_iSup_of_superadditive
    (a : ℕ → EReal)
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k))
    (htop : ∀ k : ℕ, 0 < k → a k ≠ ⊤) :
    limsup (fun k : ℕ => a k / ((k : ℝ) : EReal)) atTop =
      ⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  apply le_antisymm
  · refine (iInf_le (fun n : ℕ => ⨆ i ≥ n, a i / ((i : ℝ) : EReal)) 1).trans ?_
    refine iSup₂_le fun i hi => ?_
    exact le_iSup₂ (f := fun k (_ : 0 < k) => a k / ((k : ℝ) : EReal)) i (by omega)
  · refine iSup₂_le fun m hm => ?_
    refine le_iInf fun N => ?_
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmE : (0 : EReal) < ((m : ℝ) : EReal) := EReal.coe_pos.mpr hmR
    by_cases hbot : a m = ⊥
    · rw [hbot, EReal.bot_div_of_pos_ne_top hmE (EReal.coe_ne_top _)]
      exact bot_le
    · let α : ℝ := (a m).toReal
      have hα : a m = (α : EReal) := (EReal.coe_toReal (htop m hm) hbot).symm
      have hit := EReal.superadditive_iterate hsuper hm hα hm N
      have hcoef : ((N + 1 : ℕ) : ℝ) * α = (N : ℝ) * α + α := by
        push_cast
        ring
      have hindex : (N + 1) * m = N * m + m := by ring
      have hmul : ((((N + 1 : ℕ) : ℝ) * α : ℝ) : EReal) ≤ a ((N + 1) * m) := by
        rw [hα, ← EReal.coe_add] at hit
        rw [hcoef, hindex]
        exact hit
      have hden : (0 : ℝ) < ((N + 1) * m : ℕ) := by positivity
      have hdiv := EReal.div_le_div_right_of_nonneg
        (EReal.coe_nonneg.mpr hden.le) hmul
      have hcancel : ((((N + 1 : ℕ) : ℝ) * α : ℝ) : EReal) /
          ((((N + 1) * m : ℕ) : ℝ) : EReal) =
          a m / ((m : ℝ) : EReal) := by
        rw [hα, ← EReal.coe_div, ← EReal.coe_div]
        congr 1
        push_cast
        field_simp
      have hnorm : a m / ((m : ℝ) : EReal) ≤
          a ((N + 1) * m) / ((((N + 1) * m : ℕ) : ℝ) : EReal) := by
        simpa only [hcancel] using hdiv
      have hm1 : 1 ≤ m := hm
      have hN : N ≤ (N + 1) * m :=
        le_trans (Nat.le_succ N) (by simpa using Nat.mul_le_mul_left (N + 1) hm1)
      exact hnorm.trans (le_iSup₂
        (f := fun i (_ : N ≤ i) => a i / ((i : ℝ) : EReal)) ((N + 1) * m) hN)

/-- The finite-linear-upper-bound specialization of the revised limsup
version of Fekete's lemma. No eventual finiteness is assumed. -/
theorem EReal.limsup_div_eq_iSup_of_superadditive_of_linear_upper_bound
    (a : ℕ → EReal) (C : ℝ)
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k))
    (hup : ∀ k : ℕ, 0 < k → a k ≤ ((C * k : ℝ) : EReal)) :
    limsup (fun k : ℕ => a k / ((k : ℝ) : EReal)) atTop =
      ⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal) :=
  EReal.limsup_div_eq_iSup_of_superadditive a hsuper
    (fun k hk => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hup k hk))

end SGPT.LineBundle
