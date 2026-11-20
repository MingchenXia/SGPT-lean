import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Concrete fast Cantor coefficients for the first BBJ existence construction.
The complete mathematical route is in source-bbj-polar-cantor.tex.
This module does not assert the whole BBJ example or any current representation. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter
open scoped Topology

/-- The explicit coefficients `2^(-16^(k+1))`, written using natural powers. -/
def cantorCoefficient (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (16 ^ (k + 1))

lemma cantorCoefficient_pos (k : ℕ) : 0 < cantorCoefficient k := by
  exact pow_pos (by norm_num) _

lemma cantorCoefficient_le (k : ℕ) : cantorCoefficient k ≤ (1 / 2 : ℝ) ^ 16 := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  exact Nat.le_pow (Nat.succ_pos k)

lemma cantorCoefficient_succ (k : ℕ) :
    cantorCoefficient (k + 1) = cantorCoefficient k ^ 16 := by
  simp only [cantorCoefficient, ← pow_mul]
  congr 1

lemma cantorCoefficient_succ_lt (k : ℕ) :
    cantorCoefficient (k + 1) < cantorCoefficient k / 4 := by
  rw [cantorCoefficient_succ]
  have hpos := cantorCoefficient_pos k
  have hsmall : cantorCoefficient k ≤ 1 / 2 := by
    have := cantorCoefficient_le k
    norm_num at this ⊢
    linarith
  have hpow : cantorCoefficient k ^ 15 ≤ (1 / 2 : ℝ) ^ 15 :=
    pow_le_pow_left₀ hpos.le hsmall 15
  rw [show (16 : ℕ) = 15 + 1 from rfl, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hpow hpos.le]

lemma summable_cantorCoefficient : Summable cantorCoefficient := by
  apply summable_of_ratio_norm_eventually_le (r := 1 / 4) (by norm_num)
  exact Filter.Eventually.of_forall fun k => by
    simp only [Real.norm_eq_abs, abs_of_pos (cantorCoefficient_pos _)]
    have := (cantorCoefficient_succ_lt k).le
    linarith

lemma cantorCoefficient_shift_le (n k : ℕ) :
    cantorCoefficient (n + k) ≤ (1 / 4 : ℝ) ^ k * cantorCoefficient n := by
  have h := le_geom (u := fun k => cantorCoefficient (n + k))
    (c := 1 / 4) (by norm_num) k (fun j _ => by
      have hstep := (cantorCoefficient_succ_lt (n + j)).le
      simpa only [Nat.add_assoc, div_eq_mul_inv, mul_comm, one_mul] using hstep)
  simpa only [Nat.add_zero] using h

lemma cantorCoefficient_tail_le (n : ℕ) :
    (∑' k : ℕ, cantorCoefficient (n + k)) ≤ (4 / 3 : ℝ) * cantorCoefficient n := by
  have hg : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * cantorCoefficient n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hs : Summable fun k : ℕ => cantorCoefficient (n + k) :=
    hg.of_norm_bounded fun k => by
      simpa only [Real.norm_eq_abs, abs_of_pos (cantorCoefficient_pos _)]
        using cantorCoefficient_shift_le n k
  have h := hs.tsum_le_tsum (cantorCoefficient_shift_le n) hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  norm_num at h ⊢
  exact h

lemma cantorCoefficient_tail_lt (n : ℕ) :
    (∑' k : ℕ, cantorCoefficient (n + k)) < 2 * cantorCoefficient n := by
  have h := cantorCoefficient_tail_le n
  have hp := cantorCoefficient_pos n
  linarith

/-- Coding of the actual Boolean product by the explicit rapidly decreasing series. -/
def cantorCode (b : ℕ → Bool) : ℝ :=
  ∑' k : ℕ, if b k then cantorCoefficient k else 0

lemma summable_cantorCode_terms (b : ℕ → Bool) :
    Summable (fun k => if b k then cantorCoefficient k else 0) := by
  apply summable_cantorCoefficient.of_norm_bounded
  intro k
  split <;> simp [Real.norm_eq_abs, abs_of_pos (cantorCoefficient_pos k),
    (cantorCoefficient_pos k).le]

lemma continuous_cantorCode : Continuous cantorCode := by
  apply continuous_tsum (u := cantorCoefficient)
  · intro k
    exact (continuous_of_discreteTopology (f := fun t : Bool =>
      if t then cantorCoefficient k else (0 : ℝ))).comp (continuous_apply k)
  · exact summable_cantorCoefficient
  · intro k b
    split <;> simp [Real.norm_eq_abs, abs_of_pos (cantorCoefficient_pos k),
      (cantorCoefficient_pos k).le]

lemma cantorCode_nonneg (b : ℕ → Bool) : 0 ≤ cantorCode b := by
  apply tsum_nonneg
  intro k
  split
  · exact (cantorCoefficient_pos k).le
  · exact le_rfl

lemma cantorCode_lt_half (b : ℕ → Bool) : cantorCode b < 1 / 2 := by
  have h : cantorCode b ≤ ∑' k : ℕ, cantorCoefficient k := by
    apply (summable_cantorCode_terms b).tsum_le_tsum _ summable_cantorCoefficient
    intro k
    split <;> simp [(cantorCoefficient_pos k).le]
  have ht := cantorCoefficient_tail_lt 0
  simp only [Nat.zero_add] at ht
  have h0 : cantorCoefficient 0 = (1 / 65536 : ℝ) := by norm_num [cantorCoefficient]
  rw [h0] at ht
  linarith

/-- The concrete coding error after a finite prefix is nonnegative and has the
same uniform tail bound for every bit sequence. -/
lemma cantorCode_prefix_error (b : ℕ → Bool) (n : ℕ) :
    0 ≤ cantorCode b - ∑ k ∈ Finset.range n, (if b k then cantorCoefficient k else 0) ∧
    cantorCode b - ∑ k ∈ Finset.range n, (if b k then cantorCoefficient k else 0) ≤
      (4 / 3 : ℝ) * cantorCoefficient n := by
  rw [cantorCode, ← Summable.sum_add_tsum_nat_add n (summable_cantorCode_terms b),
    add_sub_cancel_left]
  constructor
  · apply tsum_nonneg
    intro k
    split
    · exact (cantorCoefficient_pos _).le
    · exact le_rfl
  · have h : (∑' k : ℕ, if b (k + n) then cantorCoefficient (k + n) else 0) ≤
        ∑' k : ℕ, cantorCoefficient (k + n) := by
      apply ((summable_nat_add_iff n).2 (summable_cantorCode_terms b)).tsum_le_tsum _
        ((summable_nat_add_iff n).2 summable_cantorCoefficient)
      intro k
      split <;> simp [(cantorCoefficient_pos _).le]
    exact h.trans (by simpa only [Nat.add_comm] using cantorCoefficient_tail_le n)

lemma cantorCode_lt_of_first_difference (b d : ℕ → Bool) (k : ℕ)
    (hprefix : ∀ i < k, b i = d i) (hb : b k = false) (hd : d k = true) :
    cantorCode b < cantorCode d := by
  have hp : (∑ i ∈ Finset.range k, (if b i then cantorCoefficient i else 0)) =
      ∑ i ∈ Finset.range k, (if d i then cantorCoefficient i else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hprefix i (Finset.mem_range.mp hi)]
  have hbe := (cantorCode_prefix_error b (k + 1)).2
  have hde := (cantorCode_prefix_error d (k + 1)).1
  simp only [Finset.sum_range_succ, hb, Bool.false_eq_true, if_false, add_zero, hp] at hbe
  simp only [Finset.sum_range_succ, hd, if_true] at hde
  have htail := cantorCoefficient_succ_lt k
  have hpos := cantorCoefficient_pos k
  linarith

lemma cantorCode_injective : Function.Injective cantorCode := by
  intro b d heq
  by_contra hne
  have hex : ∃ k, b k ≠ d k := Function.ne_iff.mp hne
  let k := Nat.find hex
  have hk : b k ≠ d k := Nat.find_spec hex
  have hp : ∀ i < k, b i = d i := by
    intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  cases hb : b k <;> cases hd : d k
  · exact hk (hb.trans hd.symm)
  · exact (ne_of_lt (cantorCode_lt_of_first_difference b d k hp hb hd)) heq
  · exact (ne_of_lt (cantorCode_lt_of_first_difference d b k
      (fun i hi => (hp i hi).symm) hd hb)) heq.symm
  · exact hk (hb.trans hd.symm)

end SGPT.BBJ
