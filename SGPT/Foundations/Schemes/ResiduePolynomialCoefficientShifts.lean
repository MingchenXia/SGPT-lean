import SGPT.Foundations.Schemes.PolynomialBoundedDegreeCoefficientLimits
import SGPT.Foundations.Schemes.PeriodicConsecutiveShifts

/-! # Genuine sequence shifts constrain actual bounded residue coefficients -/

open Filter Polynomial
open scoped Topology

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual sequence shift inequality gives the corresponding original
residue top-coefficient inequality, with the actual quotient/remainder shift. -/
theorem residuePolynomial_coeff_shift_le (h : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (n b a : ℕ) (Q : Fin q → Polynomial ℝ) (hdeg : ∀ r, (Q r).natDegree ≤ n)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (ha : ∀ k, h k ≤ h (k + a)) (r : Fin q) :
    (Q r).coeff n ≤ (Q ⟨(r.val + a) % q, Nat.mod_lt _ hq⟩).coeff n := by
  let c : ℕ := (r.val + a) / q
  let s : Fin q := ⟨(r.val + a) % q, Nat.mod_lt _ hq⟩
  let T := (Q s).comp (X + C (c : ℝ))
  have hT : T.natDegree ≤ n := by
    simpa only [T, natDegree_comp, natDegree_X_add_C, mul_one] using hdeg s
  have hcomp : ∀ᶠ m : ℕ in atTop, (Q r).eval (m : ℝ) ≤ T.eval (m : ℝ) := by
    filter_upwards [eventually_ge_atTop b] with m hm
    have hc : q * m + r.val + a = q * (m + c) + s.val := by
      have he := Nat.div_add_mod (r.val + a) q
      dsimp [c, s]
      nlinarith
    have heval : T.eval (m : ℝ) = (Q s).eval ((m + c : ℕ) : ℝ) := by
      simp [T, Nat.cast_add]
    rw [heval, ← hQ r m hm, ← hQ s (m + c) (hm.trans (Nat.le_add_right m c))]
    exact (ha (q * m + r.val)).trans_eq (congrArg h hc)
  have htop := polynomial_coeff_le_of_eventually_eval_le (Q r) T n (hdeg r) hT hcomp
  rw [polynomial_comp_X_add_C_coeff_of_natDegree_le (Q s) n (c : ℝ) (hdeg s)] at htop
  exact htop

/-- Actual consecutive sequence shift inequalities force equality of all
actual residue coefficients at a genuine common polynomial degree bound. -/
theorem residuePolynomial_coeff_eq_of_consecutive_shifts (h : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (n b a : ℕ) (Q : Fin q → Polynomial ℝ) (hdeg : ∀ r, (Q r).natDegree ≤ n)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (ha : ∀ k, h k ≤ h (k + a)) (hb : ∀ k, h k ≤ h (k + (a + 1))) :
    ∀ r s, (Q r).coeff n = (Q s).coeff n := by
  let f : ℕ → ℝ := fun k ↦ (Q ⟨k % q, Nat.mod_lt _ hq⟩).coeff n
  have hp : Function.Periodic f q := by
    intro k
    dsimp [f]
    congr 2
    apply Fin.ext
    simp
  have hshift (d : ℕ) (hd : ∀ k, h k ≤ h (k + d)) : ∀ k, f k ≤ f (k + d) := by
    intro k
    have H := residuePolynomial_coeff_shift_le h q hq n b d Q hdeg hQ hd
      ⟨k % q, Nat.mod_lt _ hq⟩
    have hi : (⟨((k % q) + d) % q, Nat.mod_lt _ hq⟩ : Fin q) =
        ⟨(k + d) % q, Nat.mod_lt _ hq⟩ := by
      apply Fin.ext
      simp [Nat.add_mod]
    change (Q ⟨k % q, Nat.mod_lt _ hq⟩).coeff n ≤
      (Q ⟨((k % q) + d) % q, Nat.mod_lt _ hq⟩).coeff n at H
    rw [hi] at H
    exact H
  have hc := periodic_nat_eq_const_of_consecutive_shift_le f q a hq hp
    (hshift a ha) (hshift (a + 1) hb)
  intro r s
  have hr : f r.val = (Q r).coeff n := by
    dsimp [f]
    congr 2
    apply Fin.ext
    exact Nat.mod_eq_of_lt r.isLt
  have hs : f s.val = (Q s).coeff n := by
    dsimp [f]
    congr 2
    apply Fin.ext
    exact Nat.mod_eq_of_lt s.isLt
  exact hr.symm.trans ((hc r.val).trans ((hc s.val).symm.trans hs))

end
end SGPT.Foundations.Schemes
