import SGPT.Foundations.Schemes.PolynomialBoundedDegreeCoefficientLimits
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Actual finite residue polynomials give the full original sequence asymptotic -/

open Filter Polynomial Asymptotics
open scoped Topology

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

/-- Actual residue polynomial identities with one genuine intrinsic top
coefficient produce a full-sequence error of one lower degree. All residues
and their original uniform bound are retained; no asymptotic is input. -/
theorem residuePolynomial_full_isBigO_of_common_coeff
    (h : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 1 ≤ n) (b : ℕ)
    (Q : Fin q → Polynomial ℝ) (β : ℝ) (hdeg : ∀ r, (Q r).natDegree ≤ n)
    (hcoeff : ∀ r, (Q r).coeff n = β)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ)) :
    (fun k : ℕ ↦ h k - (β / (q : ℝ) ^ n) * (k : ℝ) ^ n) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ (n - 1)) := by
  classical
  let α : ℝ := β / (q : ℝ) ^ n
  let D : Fin q → Polynomial ℝ := fun r ↦ (C (q : ℝ) * X + C (r.val : ℝ)) ^ n
  let E : Fin q → Polynomial ℝ := fun r ↦ Q r - C α * D r
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hDdeg : ∀ r, (D r).natDegree = n := by
    intro r
    simp only [D, natDegree_pow, natDegree_linear hq0, mul_one]
  have hDlc : ∀ r, (D r).leadingCoeff = (q : ℝ) ^ n := by
    intro r
    simp only [D, leadingCoeff_pow, leadingCoeff_linear hq0]
  have hEdeg : ∀ r, (E r).natDegree ≤ n - 1 := by
    intro r
    have hle : (E r).natDegree ≤ n := by
      exact (natDegree_sub_le _ _).trans (max_le (hdeg r)
        ((natDegree_C_mul_le _ _).trans (le_of_eq (hDdeg r))))
    have hc : (E r).coeff n = 0 := by
      rw [show E r = Q r - C α * D r from rfl, coeff_sub, coeff_C_mul, hcoeff]
      have hdc : (D r).coeff n = (q : ℝ) ^ n := by
        rw [← hDlc r, ← hDdeg r, coeff_natDegree]
      rw [hdc]
      dsimp [α]
      field_simp; ring
    by_cases hz : E r = 0
    · simp [hz]
    have hne : (E r).natDegree ≠ n := by
      intro he
      have hnonzero := leadingCoeff_ne_zero.mpr hz
      rw [← coeff_natDegree, he, hc] at hnonzero
      exact hnonzero rfl
    omega
  have hbound : ∀ r, ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ‖(E r).eval (m : ℝ)‖ ≤ C * ‖(m : ℝ) ^ (n - 1)‖ := by
    intro r
    have hp := (Polynomial.isBigO_atTop_of_degree_le (E r) (X ^ (n - 1))
      (by rw [degree_X_pow]; exact degree_le_of_natDegree_le (hEdeg r))).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hp' : (fun m : ℕ ↦ (E r).eval (m : ℝ)) =O[atTop]
        (fun m : ℕ ↦ (m : ℝ) ^ (n - 1)) := by simpa [Function.comp_def] using hp
    obtain ⟨C, hC, ht⟩ := isBigO_iff'.mp hp'
    obtain ⟨M, hM⟩ := eventually_atTop.mp ht
    exact ⟨C, hC, M, hM⟩
  choose C hC M hM using hbound
  let B := max b (Finset.univ.sup M)
  let A : ℝ := ∑ r, C r
  have hA : ∀ r, C r ≤ A := by
    intro r
    exact Finset.single_le_sum (fun s _ ↦ (hC s).le) (Finset.mem_univ r)
  apply isBigO_iff.mpr
  refine ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop (q * B)] with k hk
  let m : ℕ := k / q
  let r : Fin q := ⟨k % q, Nat.mod_lt _ hq⟩
  have hBm : B ≤ m := (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hk)
  have hmb : b ≤ m := (le_max_left _ _).trans hBm
  have hmM : M r ≤ m :=
    (Finset.le_sup (f := M) (Finset.mem_univ r)).trans ((le_max_right _ _).trans hBm)
  have hkm : q * m + r.val = k := Nat.div_add_mod k q
  have heval : (E r).eval (m : ℝ) = h k - α * (k : ℝ) ^ n := by
    simp only [E, D, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]
    rw [← hQ r m hmb, hkm]
    congr 2
    exact_mod_cast congrArg (fun j : ℕ ↦ j ^ n) hkm
  change ‖h k - α * (k : ℝ) ^ n‖ ≤ A * ‖(k : ℝ) ^ (n - 1)‖
  rw [← heval]
  apply (hM r m hmM).trans
  have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k q
  have hpow : (m : ℝ) ^ (n - 1) ≤ (k : ℝ) ^ (n - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hmk _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_mul (hA r) hpow (pow_nonneg (Nat.cast_nonneg _) _) (le_trans (hC r).le (hA r))


/-- In dimension zero, actual degree-zero residue polynomials with the
same actual coefficient make the ORIGINAL full sequence eventually constant. -/
theorem residuePolynomial_eventually_eq_of_common_constant
    (h : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (b : ℕ)
    (Q : Fin q → Polynomial ℝ) (β : ℝ) (hdeg : ∀ r, (Q r).natDegree ≤ 0)
    (hcoeff : ∀ r, (Q r).coeff 0 = β)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ)) :
    ∀ᶠ k : ℕ in atTop, h k = β := by
  filter_upwards [eventually_ge_atTop (q * b)] with k hk
  let m := k / q
  let r : Fin q := ⟨k % q, Nat.mod_lt _ hq⟩
  have hmb : b ≤ m := (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hk)
  have hkm : q * m + r.val = k := Nat.div_add_mod k q
  have he := hQ r m hmb
  rw [hkm, eq_C_of_natDegree_le_zero (hdeg r), eval_C, hcoeff] at he
  exact he

end
end SGPT.Foundations.Schemes
