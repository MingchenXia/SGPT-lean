import SGPT.BBJ.ProjectiveCantor

/-! Actual finite prefix centers and exact convex coefficients for the BBJ pole
construction. The complete proofs precede implementation in source-bbj-prefixes.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter
open scoped Topology
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual finite word extended by zero bits. -/
def cantorPrefixBits {n : ℕ} (s : Fin n → Bool) (k : ℕ) : Bool :=
  if h : k < n then s ⟨k,h⟩ else false

/-- The concrete real prefix center, using the already genuine infinite coding. -/
def cantorPrefixReal {n : ℕ} (s : Fin n → Bool) : ℝ :=
  cantorCode (cantorPrefixBits s)

/-- Its literal finite sum formula follows from zero support outside the prefix. -/
lemma cantorPrefixReal_eq_sum {n : ℕ} (s : Fin n → Bool) :
    cantorPrefixReal s = ∑ k ∈ Finset.range n,
      (if cantorPrefixBits s k then cantorCoefficient k else 0) := by
  apply tsum_eq_sum
  intro k hk
  have hkn : ¬ k < n := by simpa only [Finset.mem_range] using hk
  simp [cantorPrefixBits, hkn]

lemma cantorPrefixReal_nonneg {n : ℕ} (s : Fin n → Bool) : 0 ≤ cantorPrefixReal s :=
  cantorCode_nonneg _

lemma cantorPrefixReal_lt_half {n : ℕ} (s : Fin n → Bool) : cantorPrefixReal s < 1 / 2 :=
  cantorCode_lt_half _

lemma cantorPrefixReal_zero (s : Fin 0 → Bool) : cantorPrefixReal s = 0 := by
  simp [cantorPrefixReal, cantorCode, cantorPrefixBits]

/-- The projective center is in the SAME actual Cantor set, by actual zero extension. -/
def projectiveCantorPrefix {n : ℕ} (s : Fin n → Bool) : P1 :=
  projectiveCantorCode (cantorPrefixBits s)

lemma projectiveCantorPrefix_mem {n : ℕ} (s : Fin n → Bool) :
    projectiveCantorPrefix s ∈ projectiveCantorSet := ⟨_,rfl⟩

lemma cantorPrefixReal_restrict_error (b : ℕ → Bool) (n : ℕ) :
    0 ≤ cantorCode b - cantorPrefixReal (fun i : Fin n => b i) ∧
    cantorCode b - cantorPrefixReal (fun i : Fin n => b i) ≤
      (4 / 3 : ℝ) * cantorCoefficient n := by
  have he : cantorPrefixReal (fun i : Fin n => b i) =
      ∑ k ∈ Finset.range n, (if b k then cantorCoefficient k else 0) := by
    rw [cantorPrefixReal_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [cantorPrefixBits, Finset.mem_range.mp hk]
  simpa only [he] using cantorCode_prefix_error b n

lemma cantorPrefixReal_restrict_abs_lt (b : ℕ → Bool) (n : ℕ) :
    |cantorCode b - cantorPrefixReal (fun i : Fin n => b i)| < 2 * cantorCoefficient n := by
  rw [abs_of_nonneg (cantorPrefixReal_restrict_error b n).1]
  have he := (cantorPrefixReal_restrict_error b n).2
  have hp := cantorCoefficient_pos n
  linarith

/-- The actual number of words includes the single empty word at level zero. -/
lemma card_cantorWords (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- The exact coefficient of a center in a level average. -/
def cantorAverageWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- The exact coefficient of a level average in the pole series. -/
def cantorLevelWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

lemma cantorAverageWeight_pos (n : ℕ) : 0 < cantorAverageWeight n :=
  pow_pos (by norm_num) _

lemma cantorLevelWeight_pos (n : ℕ) : 0 < cantorLevelWeight n :=
  pow_pos (by norm_num) _

lemma sum_cantorAverageWeight (n : ℕ) :
    (∑ _s : Fin n → Bool, cantorAverageWeight n) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, card_cantorWords, nsmul_eq_mul,
    cantorAverageWeight, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
  norm_num

lemma sum_cantorLevelWeight (N : ℕ) :
    (∑ n ∈ Finset.range N, cantorLevelWeight n) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, cantorLevelWeight, pow_succ]
    ring

lemma cantorLevelWeight_partial_bounds (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.range N, cantorLevelWeight n) ∧
      (∑ n ∈ Finset.range N, cantorLevelWeight n) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun n _ => (cantorLevelWeight_pos n).le
  · rw [sum_cantorLevelWeight]
    have h : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
    linarith

lemma cantor_matching_coefficient (n : ℕ) :
    cantorLevelWeight n * cantorAverageWeight n * (16 : ℝ) ^ (n + 1) =
      8 * (4 : ℝ) ^ n := by
  simp only [cantorLevelWeight, cantorAverageWeight]
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [pow_succ] at ih ⊢
    nlinarith only [ih]

end SGPT.BBJ
