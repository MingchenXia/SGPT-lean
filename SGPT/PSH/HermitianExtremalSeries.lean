import SGPT.PSH.HermitianExtremalL1Bound
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Noncollapse and poles of the normalized Josefson series

The finite negative-integral bounds keep the decreasing geometric series
finite almost everywhere. Positive coefficients retain every input pole.
These scalar statements retain extended-real values at poles and do not
assume that the limiting series belongs to a geometric function class.

Source: FPT, Hermitian Josefson, `lem:hermitian-extremal-pole-alternative`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalSeries

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis
open scoped Topology ENNReal

variable {α : Type*}

/-- The actual finite weighted sum, before taking its decreasing infimum. -/
def partialSum (a : ℕ → ℝ) (ψ : ℕ → α → EReal) (N : ℕ) (x : α) : EReal :=
  ∑ j ∈ Finset.range N, (a j : EReal) * ψ j x

/-- Nonnegative weights preserve the nonpositivity of every finite sum. -/
theorem partialSum_nonpos {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    (ha : ∀ j, 0 ≤ a j) (hψ : ∀ j x, ψ j x ≤ 0) (N : ℕ) (x : α) :
    partialSum a ψ N x ≤ 0 := by
  exact Finset.sum_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (ha j)) (hψ j x)

/-- Appending a nonpositive summand makes the original finite sums decrease. -/
theorem partialSum_antitone {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    (ha : ∀ j, 0 ≤ a j) (hψ : ∀ j x, ψ j x ≤ 0) (x : α) :
    Antitone fun N => partialSum a ψ N x := by
  apply antitone_nat_of_succ_le
  intro N
  rw [partialSum, Finset.sum_range_succ]
  simpa only [partialSum, zero_add, add_comm] using add_le_add_left
    (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (ha N)) (hψ N x))
    (partialSum a ψ N x)

/-- Negative deficits add for nonpositive summands, including bottom poles. -/
theorem neg_finset_sum_toENNReal {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ j ∈ s, f j ≤ 0) :
    (-∑ j ∈ s, f j).toENNReal = ∑ j ∈ s, (-f j).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : ∑ k ∈ s, f k ≤ 0 :=
      Finset.sum_nonpos fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hadd := finiteDeficit_add 0 0 (hf j (Finset.mem_insert_self j s)) hs
    simpa only [zero_add, EReal.coe_zero, zero_sub,
      ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))] using hadd

/-- Finite nonnegative real coefficients multiply the original pole deficit. -/
theorem neg_mul_toENNReal (a : ℝ) (ha : 0 ≤ a) (z : EReal) :
    (-((a : EReal) * z)).toENNReal = ENNReal.ofReal a * (-z).toENNReal := by
  rw [← mul_neg, EReal.toENNReal_mul (EReal.coe_nonneg.mpr ha),
    EReal.real_coe_toENNReal]

/-- Exact negative-deficit formula for the same weighted finite sum. -/
theorem neg_partialSum_toENNReal {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    (ha : ∀ j, 0 ≤ a j) (hψ : ∀ j x, ψ j x ≤ 0) (N : ℕ) (x : α) :
    (-partialSum a ψ N x).toENNReal =
      ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) * (-ψ j x).toENNReal := by
  rw [partialSum, neg_finset_sum_toENNReal]
  · exact Finset.sum_congr rfl fun j _ => neg_mul_toENNReal (a j) (ha j) (ψ j x)
  · intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (ha j)) (hψ j x)

/-- A strictly positive coefficient retains an original pole in every
finite sum containing its index. -/
theorem partialSum_eq_bot_of_input_pole {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    {j N : ℕ} (ha : 0 < a j) (hj : j < N) {x : α} (hx : ψ j x = ⊥) :
    partialSum a ψ N x = ⊥ := by
  rw [partialSum, ← Finset.add_sum_erase (Finset.range N)
    (fun k => (a k : EReal) * ψ k x) (Finset.mem_range.mpr hj), hx,
    EReal.coe_mul_bot_of_pos ha, EReal.bot_add]

/-- The decreasing-series infimum retains every pole with a strictly
positive coefficient. -/
theorem series_eq_bot_of_input_pole {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    {j : ℕ} (ha : 0 < a j) {x : α} (hx : ψ j x = ⊥) :
    (⨅ N, partialSum a ψ N x) = ⊥ :=
  le_bot_iff.mp ((iInf_le (fun N => partialSum a ψ N x) (j + 1)).trans_eq
    (partialSum_eq_bot_of_input_pole ha (Nat.lt_succ_self j) hx))

/-- If each original weighted term is at most minus one, its first `N`
terms are at most minus `N`, including extended-real input poles. -/
theorem partialSum_le_neg_nat {a : ℕ → ℝ} {ψ : ℕ → α → EReal} {x : α}
    (hterm : ∀ j, (a j : EReal) * ψ j x ≤ (-1 : EReal)) (N : ℕ) :
    partialSum a ψ N x ≤ ((-(N : ℝ) : ℝ) : EReal) := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    rw [partialSum, Finset.sum_range_succ]
    calc
      (∑ j ∈ Finset.range N, (a j : EReal) * ψ j x) + (a N : EReal) * ψ N x
          ≤ ((-(N : ℝ) : ℝ) : EReal) + (-1 : EReal) := add_le_add ih (hterm N)
      _ = ((-((N + 1 : ℕ) : ℝ) : ℝ) : EReal) := by
        rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by norm_num, ← EReal.coe_add]
        congr 1
        push_cast
        ring

/-- Unit negative contribution at every index forces the actual series
to be negative infinity, by comparison with all finite real levels. -/
theorem series_eq_bot_of_weighted_terms_le_neg_one
    {a : ℕ → ℝ} {ψ : ℕ → α → EReal} {x : α}
    (hterm : ∀ j, (a j : EReal) * ψ j x ≤ (-1 : EReal)) :
    (⨅ N, partialSum a ψ N x) = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (-b)
  exact ((iInf_le (fun N => partialSum a ψ N x) N).trans
    (partialSum_le_neg_nat hterm N)).trans_lt
      (EReal.coe_lt_coe_iff.mpr (by linarith))

variable [MeasurableSpace α] {μ : Measure α}

/-- A summable unit coefficient budget transfers one uniform input
negative-integral bound to every actual finite weighted sum. -/
theorem lintegral_neg_partialSum_le {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    (ha : ∀ j, 0 ≤ a j) (hψ : ∀ j x, ψ j x ≤ 0)
    (hmeas : ∀ j, AEMeasurable (fun x => (-ψ j x).toENNReal) μ)
    {B : ℝ≥0∞} (hB : ∀ j, ∫⁻ x, (-ψ j x).toENNReal ∂μ ≤ B)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) ≤ 1) (N : ℕ) :
    ∫⁻ x, (-partialSum a ψ N x).toENNReal ∂μ ≤ B := by
  simp_rw [neg_partialSum_toENNReal ha hψ]
  rw [lintegral_finsetSum' (Finset.range N)
    (f := fun j x => ENNReal.ofReal (a j) * (-ψ j x).toENNReal)
    (fun j _ => aemeasurable_const.mul (hmeas j))]
  simp_rw [lintegral_const_mul'' _ (hmeas _)]
  calc
    ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) * ∫⁻ x, (-ψ j x).toENNReal ∂μ
        ≤ ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) * B :=
      Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hB j)
    _ = (∑ j ∈ Finset.range N, ENNReal.ofReal (a j)) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * B := mul_le_mul' (hbudget N) le_rfl
    _ = B := one_mul _

/-- If an extended-real infimum is bottom, its negative deficits are
unbounded. This is a scalar order statement with no finiteness premise. -/
theorem iSup_negative_deficit_eq_top {f : ℕ → EReal} (hbot : (⨅ j, f j) = ⊥) :
    (⨆ j, (-f j).toENNReal) = ⊤ := by
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  refine iSup_le fun N => ?_
  obtain ⟨j, hj⟩ := iInf_lt_iff.mp
    (show (⨅ j, f j) < ((-(N : ℝ) : ℝ) : EReal) by rw [hbot]; exact EReal.bot_lt_coe _)
  have hneg : ((N : ℝ) : EReal) ≤ -f j := by
    simpa only [EReal.coe_neg, neg_neg] using EReal.neg_le_neg_iff.mpr hj.le
  have h := EReal.toENNReal_le_toENNReal hneg
  rw [EReal.real_coe_toENNReal, ENNReal.ofReal_natCast] at h
  exact h.trans (le_iSup (fun j => (-f j).toENNReal) j)

/-- Monotone convergence turns a uniform finite negative-integral bound
into almost-everywhere noncollapse of the decreasing extended-real limit. -/
theorem ae_ne_bot_iInf_of_lintegral_bound {w : ℕ → α → EReal}
    (hanti : ∀ x, Antitone fun j => w j x)
    (hmeas : ∀ j, AEMeasurable (fun x => (-w j x).toENNReal) μ)
    {B : ℝ≥0∞} (hBtop : B < ⊤)
    (hB : ∀ j, ∫⁻ x, (-w j x).toENNReal ∂μ ≤ B) :
    ∀ᵐ x ∂μ, (⨅ j, w j x) ≠ ⊥ := by
  have hmono (x : α) : Monotone fun j => (-w j x).toENNReal :=
    fun i j hij => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hanti x hij))
  have hint : ∫⁻ x, ⨆ j, (-w j x).toENNReal ∂μ ≤ B := by
    rw [lintegral_iSup' hmeas (Eventually.of_forall hmono)]
    exact iSup_le hB
  have hfinite := ae_lt_top' (AEMeasurable.iSup hmeas) (hint.trans_lt hBtop).ne
  filter_upwards [hfinite] with x hx hbot
  exact hx.ne (iSup_negative_deficit_eq_top hbot)

/-- The normalized weighted series is finite almost everywhere under the
actual summand integral estimates and the coefficient budget. -/
theorem ae_ne_bot_series_of_uniform_lintegral {a : ℕ → ℝ} {ψ : ℕ → α → EReal}
    (ha : ∀ j, 0 ≤ a j) (hψ : ∀ j x, ψ j x ≤ 0)
    (hmeas : ∀ j, AEMeasurable (fun x => (-ψ j x).toENNReal) μ)
    {B : ℝ≥0∞} (hBtop : B < ⊤) (hB : ∀ j, ∫⁻ x, (-ψ j x).toENNReal ∂μ ≤ B)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) ≤ 1) :
    ∀ᵐ x ∂μ, (⨅ N, partialSum a ψ N x) ≠ ⊥ := by
  apply ae_ne_bot_iInf_of_lintegral_bound (partialSum_antitone ha hψ)
    (fun N => ?_) hBtop (lintegral_neg_partialSum_le ha hψ hmeas hB hbudget)
  have heq : (fun x => (-partialSum a ψ N x).toENNReal) =
      fun x => ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) * (-ψ j x).toENNReal :=
    funext (neg_partialSum_toENNReal ha hψ N)
  rw [heq]
  convert
    (Finset.aemeasurable_sum (Finset.range N)
      (f := fun j x => ENNReal.ofReal (a j) * (-ψ j x).toENNReal)
      (fun j _ => aemeasurable_const.mul (hmeas j))) using 1
  funext x
  simp only [Finset.sum_apply]

end SGPT.PSH.HermitianExtremalSeries
