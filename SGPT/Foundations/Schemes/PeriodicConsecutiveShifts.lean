import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

namespace SGPT.Foundations.Schemes

/-- A one-sided shift inequality on an actual periodic sequence is equality. -/
theorem periodic_nat_shift_eq_of_le (f : ℕ → ℝ) (q a : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (ha : ∀ k, f k ≤ f (k + a)) :
    ∀ k, f (k + a) = f k := by
  have hit : ∀ m k : ℕ, f k ≤ f (k + m * a) := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      exact (ih k).trans (by simpa [Nat.succ_mul, Nat.add_assoc] using ha (k + m * a))
  intro k
  apply le_antisymm _ (ha k)
  have h := hit (q - 1) (k + a)
  have he : k + a + (q - 1) * a = k + a * q := by nlinarith [Nat.sub_add_cancel hq]
  have hperiod : f (k + a * q) = f k := by simpa using hp.nat_mul a k
  rw [he, hperiod] at h
  exact h

/-- Consecutive actual shift inequalities force an actual periodic sequence
constant; no coprime-degree or degree-one-section premise is used. -/
theorem periodic_nat_eq_const_of_consecutive_shift_le (f : ℕ → ℝ) (q a : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (ha : ∀ k, f k ≤ f (k + a))
    (hb : ∀ k, f k ≤ f (k + (a + 1))) : ∀ k, f k = f 0 := by
  have hA := periodic_nat_shift_eq_of_le f q a hq hp ha
  have hB := periodic_nat_shift_eq_of_le f q (a + 1) hq hp hb
  have hstep : ∀ k, f (k + 1) = f k := by
    intro k
    calc
      f (k + 1) = f (k + 1 + a) := (hA (k + 1)).symm
      _ = f (k + (a + 1)) := by congr 1; omega
      _ = f k := hB k
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (hstep k).trans ih

end SGPT.Foundations.Schemes
