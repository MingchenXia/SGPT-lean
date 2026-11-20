import SGPT.NAPotential.BerkovichSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Additive-to-multiplicative Berkovich valuation dictionary

The book uses `WithTop ℝ` additive valuations. The downstream BJ formalization
uses `ℝ≥0` multiplicative valuations on the same residue fields. The exponential
with value zero at infinity gives the forward map. No relative point or psh
statement is asserted here.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.BJ

open SGPT.NAPotential.Berkovich
open scoped NNReal

/-- `exp (-a)` with the book's value `exp (-∞) = 0`. -/
def expNegNN (a : WithTop ℝ) : ℝ≥0 :=
  ⟨BerkovichPoint.expNeg a, BerkovichPoint.expNeg_nonneg a⟩

@[simp] theorem expNegNN_top : expNegNN ⊤ = 0 := by
  apply Subtype.ext
  rfl

@[simp] theorem expNegNN_coe (a : ℝ) : (expNegNN (a : WithTop ℝ) : ℝ) = Real.exp (-a) := rfl

@[simp] theorem expNegNN_zero : expNegNN 0 = 1 := by
  apply Subtype.ext
  change Real.exp (-(0 : ℝ)) = 1
  simp

/-- Exponential turns the additive infinity convention into an absorbing zero. -/
theorem expNegNN_add (a b : WithTop ℝ) : expNegNN (a + b) = expNegNN a * expNegNN b := by
  cases a with
  | top => simp
  | coe a =>
    cases b with
    | top => simp
    | coe b =>
      apply Subtype.ext
      change Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b)
      rw [neg_add, Real.exp_add]

/-- Negative exponential reverses the order, including infinity. -/
theorem expNegNN_antitone : Antitone expNegNN := by
  intro a b hab
  cases a with
  | top =>
    have hb : b = ⊤ := top_le_iff.mp hab
    subst b
    exact le_rfl
  | coe a =>
    cases b with
    | top => simp
    | coe b =>
      change Real.exp (-b) ≤ Real.exp (-a)
      exact Real.exp_le_exp.mpr (neg_le_neg (WithTop.coe_le_coe.mp hab))

/-- The multiplicative residue valuation attached to an original additive one. -/
def SourceRealValuation.toNNRealValuation {K : Type*} [Field K] [Algebra ℂ K]
    (v : SourceRealValuation K) : Valuation K ℝ≥0 where
  toFun x := expNegNN (v x)
  map_zero' := by rw [v.map_zero, expNegNN_top]
  map_one' := by rw [v.map_one, expNegNN_zero]
  map_mul' x y := by rw [v.map_mul', expNegNN_add]
  map_add_le_max' x y := by
    have h := expNegNN_antitone (v.min_le_map_add' x y)
    rw [expNegNN_antitone.map_min] at h
    exact h

@[simp] theorem SourceRealValuation.toNNRealValuation_apply {K : Type*}
    [Field K] [Algebra ℂ K] (v : SourceRealValuation K) (x : K) :
    SourceRealValuation.toNNRealValuation v x = expNegNN (v x) := rfl

/-- The multiplicative residue valuation is trivial on the same complex scalars. -/
theorem SourceRealValuation.toNNRealValuation_complex {K : Type*}
    [Field K] [Algebra ℂ K] (v : SourceRealValuation K) (c : ℂ) (hc : c ≠ 0) :
    SourceRealValuation.toNNRealValuation v (algebraMap ℂ K c) = 1 := by
  rw [SourceRealValuation.toNNRealValuation_apply, v.map_complex' c hc, expNegNN_zero]

/-- Negative logarithm, taking zero to the additive infinity. -/
def negLogNN (a : ℝ≥0) : WithTop ℝ :=
  if a = 0 then ⊤ else (-Real.log (a : ℝ) : ℝ)

@[simp] theorem negLogNN_zero : negLogNN 0 = ⊤ := by simp [negLogNN]

@[simp] theorem negLogNN_one : negLogNN 1 = 0 := by simp [negLogNN]

@[simp] theorem negLogNN_eq_top_iff (a : ℝ≥0) : negLogNN a = ⊤ ↔ a = 0 := by
  by_cases ha : a = 0 <;> simp [negLogNN, ha]

/-- The logarithmic dictionary reverses the nonnegative-real order. -/
theorem negLogNN_antitone : Antitone negLogNN := by
  intro a b hab
  by_cases ha : a = 0
  · simp [ha]
  · have hapos : 0 < a := pos_iff_ne_zero.mpr ha
    have hb : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hapos hab)
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    simp only [negLogNN, if_neg ha, if_neg hb, WithTop.coe_le_coe]
    exact neg_le_neg (Real.log_le_log (NNReal.coe_pos.mpr hapos) hab')

/-- Negative logarithm sends products to extended-real sums. -/
theorem negLogNN_mul (a b : ℝ≥0) : negLogNN (a * b) = negLogNN a + negLogNN b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  simp only [negLogNN, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb), NNReal.coe_mul,
    Real.log_mul ha' hb', neg_add, WithTop.coe_add]

@[simp] theorem negLogNN_expNegNN (a : WithTop ℝ) : negLogNN (expNegNN a) = a := by
  cases a with
  | top => simp
  | coe a =>
    have ha : expNegNN (a : WithTop ℝ) ≠ 0 := by
      intro h
      have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
      simp only [expNegNN_coe, NNReal.coe_zero] at h'
      exact (Real.exp_ne_zero (-a)) h'
    simp [negLogNN, ha, Real.log_exp]

@[simp] theorem expNegNN_negLogNN (a : ℝ≥0) : expNegNN (negLogNN a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · have ha' : 0 < (a : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
    rw [negLogNN, if_neg ha]
    apply Subtype.ext
    change Real.exp (-(-Real.log (a : ℝ))) = (a : ℝ)
    simpa only [neg_neg] using Real.exp_log ha'

/-- Logarithms recover the original additive valuation from an actual multiplicative one. -/
def SourceRealValuation.ofNNRealValuation {K : Type*} [Field K] [Algebra ℂ K]
    (w : Valuation K ℝ≥0)
    (hcomplex : ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ K c) = 1) : SourceRealValuation K where
  toFun x := negLogNN (w x)
  eq_top_iff' x := by rw [negLogNN_eq_top_iff, Valuation.zero_iff]
  map_mul' x y := by rw [map_mul, negLogNN_mul]
  min_le_map_add' x y := by
    have h := negLogNN_antitone (w.map_add x y)
    rw [negLogNN_antitone.map_max] at h
    exact h
  map_complex' c hc := by rw [hcomplex c hc, negLogNN_one]

/-- The two actual residue valuation conventions are equivalent, including poles. -/
def sourceValuationEquivNNReal {K : Type*} [Field K] [Algebra ℂ K] :
    SourceRealValuation K ≃
      {w : Valuation K ℝ≥0 // ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ K c) = 1} where
  toFun v := ⟨SourceRealValuation.toNNRealValuation v,
    SourceRealValuation.toNNRealValuation_complex v⟩
  invFun w := SourceRealValuation.ofNNRealValuation w.val w.property
  left_inv v := by
    apply SourceRealValuation.ext
    intro x
    exact negLogNN_expNegNN (v x)
  right_inv w := by
    apply Subtype.ext
    apply Valuation.ext
    intro x
    exact expNegNN_negLogNN (w.val x)

end SGPT.NAPotential.BJ
