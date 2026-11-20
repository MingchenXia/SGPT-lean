import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Trace absorption in Hermitian small-gap comparison

This module formalizes the finite real inequalities in the proof of FPT,
`prop:hermitian-small-gap-comparison`, Steps 1 and 2. The arguments apply to
the actual mixed trace masses once their one-factor integration-by-parts
inequality has been proved. No assertion about currents, Hermitian products,
or Global Josefson is made by these scalar lemmas.
-/

set_option autoImplicit false

namespace SGPT.PSH.HermitianComparisonTraceAlgebra

open Finset

/-- Iterating adjacent trace inequalities gives the precise geometric factor. -/
theorem le_pow_mul_of_adjacent_le {a : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {m n : ℕ} (hmn : m ≤ n)
    (hstep : ∀ k, m ≤ k → k < n → a k ≤ c * a (k + 1)) :
    a m ≤ c ^ (n - m) * a n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      have hprevious : ∀ k, m ≤ k → k < n → a k ≤ c * a (k + 1) :=
        fun k hmk hkn => hstep k hmk (Nat.lt_trans hkn (Nat.lt_succ_self n))
      calc
        a m ≤ c ^ (n - m) * a n := ih hprevious
        _ ≤ c ^ (n - m) * (c * a (n + 1)) :=
          mul_le_mul_of_nonneg_left (hstep n hmn (Nat.lt_succ_self n))
            (pow_nonneg hc _)
        _ = c ^ (n + 1 - m) * a (n + 1) := by
          rw [Nat.succ_sub hmn, pow_succ]
          ring

/-- The lower traces are controlled by the current trace once all earlier
adjacent inequalities have been obtained. -/
theorem sum_le_of_adjacent_le {a : ℕ → ℝ} {k : ℕ} (ha : 0 ≤ a k)
    (hstep : ∀ j, j < k → a j ≤ 4 * a (j + 1)) :
    (∑ j ∈ range (k + 1), a j) ≤ (k + 1 : ℕ) * (4 : ℝ) ^ k * a k := by
  have hterm : ∀ j ∈ range (k + 1), a j ≤ (4 : ℝ) ^ k * a k := by
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    calc
      a j ≤ (4 : ℝ) ^ (k - j) * a k :=
        le_pow_mul_of_adjacent_le (by norm_num) hjk (fun i _ hi => hstep i hi)
      _ ≤ (4 : ℝ) ^ k * a k :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) ha
  calc
    (∑ j ∈ range (k + 1), a j) ≤ ∑ _j ∈ range (k + 1), (4 : ℝ) ^ k * a k :=
      sum_le_sum hterm
    _ = (k + 1 : ℕ) * (4 : ℝ) ^ k * a k := by simp [mul_assoc]

/-- FPT's pure-trace absorption, with its explicit dimension-dependent gap.
The recurrence is the scalar inequality obtained from one-factor comparison. -/
theorem pure_trace_adjacent_le {n : ℕ} {a : ℕ → ℝ} {δ : ℝ}
    (ha : ∀ k, k ≤ n → 0 ≤ a k) (hδ : 0 ≤ δ)
    (hsmall : δ * ((n + 1 : ℕ) * (4 : ℝ) ^ n) ≤ 1 / 4)
    (hrec : ∀ k, k < n →
      (1 / 2 : ℝ) * a k ≤ a (k + 1) + δ * ∑ j ∈ range (k + 1), a j) :
    ∀ k, k < n → a k ≤ 4 * a (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hkn : k ≤ n := Nat.le_of_lt hk
      have hstep : ∀ j, j < k → a j ≤ 4 * a (j + 1) :=
        fun j hj => ih j hj (Nat.lt_trans hj hk)
      have hsum := sum_le_of_adjacent_le (ha k hkn) hstep
      have hcoeff : (k + 1 : ℕ) * (4 : ℝ) ^ k ≤
          (n + 1 : ℕ) * (4 : ℝ) ^ n :=
        mul_le_mul (by exact_mod_cast Nat.add_le_add_right hkn 1)
          (pow_le_pow_right₀ (by norm_num) hkn) (by positivity) (by positivity)
      have hδcoeff : δ * ((k + 1 : ℕ) * (4 : ℝ) ^ k) ≤ (1 / 4 : ℝ) :=
        (mul_le_mul_of_nonneg_left hcoeff hδ).trans hsmall
      have herr : δ * (∑ j ∈ range (k + 1), a j) ≤ (1 / 4 : ℝ) * a k := by
        calc
          δ * (∑ j ∈ range (k + 1), a j) ≤
              δ * ((k + 1 : ℕ) * (4 : ℝ) ^ k * a k) :=
            mul_le_mul_of_nonneg_left hsum hδ
          _ = (δ * ((k + 1 : ℕ) * (4 : ℝ) ^ k)) * a k := by ring
          _ ≤ (1 / 4 : ℝ) * a k :=
            mul_le_mul_of_nonneg_right hδcoeff (ha k hkn)
      linarith [hrec k hk]

/-- Every pure trace is bounded by the top mass, including the degree-zero
trace. This is the concluding estimate of FPT's pure-trace step. -/
theorem pure_trace_le_top {n : ℕ} {a : ℕ → ℝ} {δ : ℝ}
    (ha : ∀ k, k ≤ n → 0 ≤ a k) (hδ : 0 ≤ δ)
    (hsmall : δ * ((n + 1 : ℕ) * (4 : ℝ) ^ n) ≤ 1 / 4)
    (hrec : ∀ k, k < n →
      (1 / 2 : ℝ) * a k ≤ a (k + 1) + δ * ∑ j ∈ range (k + 1), a j)
    {k : ℕ} (hk : k ≤ n) : a k ≤ (4 : ℝ) ^ (n - k) * a n :=
  le_pow_mul_of_adjacent_le (by norm_num) hk
    (fun j _ hj => pure_trace_adjacent_le ha hδ hsmall hrec j hj)

/-- A positive degree-zero trace forces positive top mass after absorption.
For Hermitian comparison the degree-zero trace is the metric volume of the
nonempty open sublevel set. -/
theorem top_pos_of_pure_trace_recurrence {n : ℕ} {a : ℕ → ℝ} {δ : ℝ}
    (ha : ∀ k, k ≤ n → 0 ≤ a k) (ha0 : 0 < a 0) (hδ : 0 ≤ δ)
    (hsmall : δ * ((n + 1 : ℕ) * (4 : ℝ) ^ n) ≤ 1 / 4)
    (hrec : ∀ k, k < n →
      (1 / 2 : ℝ) * a k ≤ a (k + 1) + δ * ∑ j ∈ range (k + 1), a j) :
    0 < a n := by
  have htop := pure_trace_le_top ha hδ hsmall hrec (Nat.zero_le n)
  by_contra hn
  have hn' : a n ≤ 0 := le_of_not_gt hn
  have hnonpos : (4 : ℝ) ^ (n - 0) * a n ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hn'
  exact (not_lt_of_ge (htop.trans hnonpos)) ha0

/-- Replacing all mixed factors with first-kind factors accumulates one error
per replaced factor. Here `L` is one fixed lower-degree trace sum; no positivity
or measure representation is needed for this exact finite telescoping step. -/
theorem mixed_trace_replace {a : ℕ → ℕ → ℝ} {δ L : ℝ} {n : ℕ}
    (hrec : ∀ j k, j + k = n → 0 < k →
      a j k ≤ a (j + 1) (k - 1) + δ * L)
    {j k : ℕ} (hjk : j + k = n) :
    a j k ≤ a (j + k) 0 + k * δ * L := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
      have hnext : j + 1 + k = n := by omega
      have hi := ih hnext
      have hfirst := hrec j (k + 1) hjk (Nat.succ_pos k)
      simp only [Nat.add_sub_cancel] at hfirst
      have hind : a (j + 1) k ≤ a (j + (k + 1)) 0 + k * δ * L := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hi
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

/-- The sum of all mixed traces strictly below one total degree. The
finite rectangle is only an enumeration; the indicator keeps exactly the
lower-triangular indices of FPT's sum over `p + q < m`. -/
def lowerTraceSum (n : ℕ) (a : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ range (n + 1), ∑ q ∈ range (n + 1), if p + q < m then a p q else 0

/-- FPT's mixed-trace step, with an explicit (nonoptimal) dimension constant.
It uses only the one-factor recurrence and pure-trace bound, and proves the
uniform bound rather than storing it as additional data. -/
theorem mixed_trace_le_top {n : ℕ} {a : ℕ → ℕ → ℝ} {δ T : ℝ}
    (hT : 0 ≤ T)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hpure : ∀ m, m ≤ n → a m 0 ≤ (4 : ℝ) ^ n * T)
    (hrec : ∀ j k, j + k ≤ n → 0 < k →
      a j k ≤ a (j + 1) (k - 1) + δ * lowerTraceSum n a (j + k))
    {j k : ℕ} (hjk : j + k ≤ n) :
    a j k ≤ (4 : ℝ) ^ n * (1 + (n : ℝ) * (n + 1) ^ 2) ^ (j + k) * T := by
  let B : ℝ := (4 : ℝ) ^ n
  let D : ℝ := 1 + (n : ℝ) * (n + 1) ^ 2
  have hB : 0 ≤ B := by positivity
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg ((n : ℝ) + 1))]
  have hdegree : ∀ m, m ≤ n → ∀ j k, j + k = m →
      a j k ≤ B * D ^ m * T := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm j k hjkm
        by_cases hm0 : m = 0
        · have hj : j = 0 := by omega
          have hk : k = 0 := by omega
          subst m
          subst j
          subst k
          simpa only [Nat.zero_add, pow_zero, mul_one] using hpure 0 (Nat.zero_le n)
        have hlow : lowerTraceSum n a m ≤
            (n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T := by
          have hterm (p q : ℕ) : (if p + q < m then a p q else 0) ≤
              B * D ^ (m - 1) * T := by
            split_ifs with hpq
            · have hpqn : p + q ≤ n := (Nat.le_of_lt hpq).trans hm
              have hprev := ih (p + q) hpq hpqn p q rfl
              have hpqpred : p + q ≤ m - 1 := Nat.le_pred_of_lt hpq
              exact hprev.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpqpred) hB) hT)
            · positivity
          have hs := sum_le_sum (s := range (n + 1))
            (fun p _ => sum_le_sum (s := range (n + 1)) (fun q _ => hterm p q))
          calc
            lowerTraceSum n a m ≤
                ∑ _p ∈ range (n + 1), ∑ _q ∈ range (n + 1),
                  B * D ^ (m - 1) * T := hs
            _ = (n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T := by
              simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
              ring
        have hreplace : a j k ≤ a m 0 + k * δ * lowerTraceSum n a m := by
          have h := mixed_trace_replace (n := m) (a := a) (δ := δ)
            (L := lowerTraceSum n a m) (fun p q hpq hq => by
              have hpqn : p + q ≤ n := by omega
              simpa only [hpq] using hrec p q hpqn hq) hjkm
          simpa only [hjkm] using h
        have hkδ : (k : ℝ) * δ ≤ n := by
          calc
            (k : ℝ) * δ ≤ k * 1 := mul_le_mul_of_nonneg_left hδ₁ (by positivity)
            _ ≤ n := by simp only [mul_one]; exact_mod_cast (show k ≤ n by omega)
        have herr : (k : ℝ) * δ * lowerTraceSum n a m ≤
            (n : ℝ) * ((n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T) := by
          calc
            (k : ℝ) * δ * lowerTraceSum n a m ≤
                (k : ℝ) * δ * ((n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T) :=
              mul_le_mul_of_nonneg_left hlow (mul_nonneg (by positivity) hδ)
            _ ≤ (n : ℝ) * ((n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T) :=
              mul_le_mul_of_nonneg_right hkδ (by positivity)
        have hpure' : a m 0 ≤ B * D ^ (m - 1) * T := by
          have hpowone : 1 ≤ D ^ (m - 1) := by
            simpa only [pow_zero] using pow_le_pow_right₀ hD (Nat.zero_le (m - 1))
          have hBpow : B ≤ B * D ^ (m - 1) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowone hB
          calc
            a m 0 ≤ B * T := hpure m hm
            _ ≤ B * D ^ (m - 1) * T :=
              mul_le_mul_of_nonneg_right hBpow hT
        have hpow : D ^ m = D ^ (m - 1) * D := by
          calc
            D ^ m = D ^ (m - 1 + 1) := congrArg (fun t => D ^ t) (by omega)
            _ = D ^ (m - 1) * D := pow_succ _ _
        calc
          a j k ≤ a m 0 + k * δ * lowerTraceSum n a m := hreplace
          _ ≤ B * D ^ (m - 1) * T +
              (n : ℝ) * ((n + 1 : ℝ) ^ 2 * B * D ^ (m - 1) * T) :=
            add_le_add hpure' herr
          _ = B * D ^ m * T := by rw [hpow]; dsimp [D]; ring
  simpa only [B, D] using hdegree (j + k) hjk j k rfl

/-- One explicit dimension constant for the scalar small-gap comparison. -/
def comparisonConstant (n : ℕ) : ℝ :=
  n * (n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n * (1 + (n : ℝ) * (n + 1) ^ 2) ^ n

theorem comparisonConstant_nonneg (n : ℕ) : 0 ≤ comparisonConstant n := by
  unfold comparisonConstant
  positivity

/-- The complete finite trace-absorption argument in FPT's small-gap proof.
Both recurrences must still be supplied by the actual one-factor current
comparison. No current comparison is assumed as the conclusion itself. -/
theorem small_gap_trace_comparison {n : ℕ} {a : ℕ → ℕ → ℝ} {δ : ℝ}
    (ha : ∀ j k, j + k ≤ n → 0 ≤ a j k) (hδ : 0 ≤ δ)
    (hsmall : δ * ((n + 1 : ℕ) * (4 : ℝ) ^ n) ≤ 1 / 4)
    (hpure : ∀ m, m < n → (1 / 2 : ℝ) * a m 0 ≤
      a (m + 1) 0 + δ * ∑ h ∈ range (m + 1), a h 0)
    (hrec : ∀ j k, j + k ≤ n → 0 < k →
      a j k ≤ a (j + 1) (k - 1) + δ * lowerTraceSum n a (j + k)) :
    a 0 n ≤ (1 + comparisonConstant n * δ) * a n 0 := by
  let D : ℝ := 1 + (n : ℝ) * (n + 1) ^ 2
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg ((n : ℝ) + 1))]
  have hT : 0 ≤ a n 0 := ha n 0 (by omega)
  have hδ₁ : δ ≤ 1 := by
    have hcoeff : (1 : ℝ) ≤ (n + 1 : ℕ) * (4 : ℝ) ^ n := by
      calc
        (1 : ℝ) = 1 * (4 : ℝ) ^ 0 := by norm_num
        _ ≤ (n + 1 : ℕ) * (4 : ℝ) ^ n :=
          mul_le_mul (by exact_mod_cast Nat.succ_pos n)
            (pow_le_pow_right₀ (by norm_num) (Nat.zero_le n)) (by norm_num) (by positivity)
    have h := mul_le_mul_of_nonneg_left hcoeff hδ
    linarith
  have hpurebound : ∀ m, m ≤ n → a m 0 ≤ (4 : ℝ) ^ n * a n 0 := by
    intro m hm
    have h := pure_trace_le_top (a := fun i => a i 0)
      (fun i hi => ha i 0 (by simpa only [Nat.add_zero] using hi)) hδ hsmall hpure hm
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) hT)
  have hlow : lowerTraceSum n a n ≤
      (n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n * D ^ n * a n 0 := by
    have hterm (p q : ℕ) : (if p + q < n then a p q else 0) ≤
        (4 : ℝ) ^ n * D ^ n * a n 0 := by
      split_ifs with hpq
      · have hpqn := Nat.le_of_lt hpq
        have h := mixed_trace_le_top hT hδ hδ₁ hpurebound hrec hpqn
        exact h.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpqn) (by positivity)) hT)
      · positivity
    have hs := sum_le_sum (s := range (n + 1))
      (fun p _ => sum_le_sum (s := range (n + 1)) (fun q _ => hterm p q))
    calc
      lowerTraceSum n a n ≤ ∑ _p ∈ range (n + 1), ∑ _q ∈ range (n + 1),
          (4 : ℝ) ^ n * D ^ n * a n 0 := hs
      _ = (n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n * D ^ n * a n 0 := by
        simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
  have hreplace : a 0 n ≤ a n 0 + n * δ * lowerTraceSum n a n := by
    have h := mixed_trace_replace (n := n) (a := a) (δ := δ)
      (L := lowerTraceSum n a n) (fun p q hpq hq => by
        have hpqn : p + q ≤ n := by omega
        simpa only [hpq] using hrec p q hpqn hq) (j := 0) (k := n) (by simp)
    simpa only [Nat.zero_add] using h
  calc
    a 0 n ≤ a n 0 + n * δ * lowerTraceSum n a n := hreplace
    _ ≤ a n 0 + n * δ * ((n + 1 : ℝ) ^ 2 * (4 : ℝ) ^ n * D ^ n * a n 0) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hlow (mul_nonneg (by positivity) hδ)) _
    _ = (1 + comparisonConstant n * δ) * a n 0 := by
      dsimp [comparisonConstant, D]
      ring

end SGPT.PSH.HermitianComparisonTraceAlgebra
