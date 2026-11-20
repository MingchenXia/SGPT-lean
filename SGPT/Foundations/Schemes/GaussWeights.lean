import SGPT.Foundations.Schemes.ValuationFiltration
import SGPT.Foundations.Schemes.InvariantHomogeneity
import SGPT.Foundations.Schemes.ValuationIdeals
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Actual Gauss valuations and homogeneous weights

Local algebra for the source's cone weights. The polynomial valuation is
constructed from the coefficient valuation using the weighted Gauss norm,
rather than supplied as a function satisfying the desired valuation laws.
-/

namespace SGPT.Foundations.Schemes

open Polynomial

/-- Exponentiation of a finite additive weight, with `exp(-∞) = 0`. -/
noncomputable def expNegWeight (a : WithTop ℝ) : ℝ :=
  a.recTopCoe 0 (fun r => Real.exp (-r))

@[simp] theorem expNegWeight_top : expNegWeight ⊤ = 0 := rfl

@[simp] theorem expNegWeight_coe (a : ℝ) : expNegWeight (a : WithTop ℝ) = Real.exp (-a) := rfl

@[simp] theorem expNegWeight_zero : expNegWeight 0 = 1 := by
  change Real.exp (-(0 : ℝ)) = 1
  simp

theorem expNegWeight_nonneg (a : WithTop ℝ) : 0 ≤ expNegWeight a := by
  cases a using WithTop.recTopCoe
  · simp
  · change 0 ≤ Real.exp _
    positivity

@[simp] theorem expNegWeight_eq_zero_iff (a : WithTop ℝ) :
    expNegWeight a = 0 ↔ a = ⊤ := by
  cases a using WithTop.recTopCoe <;> simp

theorem expNegWeight_antitone : Antitone expNegWeight := by
  intro a b hab
  cases a using WithTop.recTopCoe <;> cases b using WithTop.recTopCoe
  · simp
  · simp at hab
  · change 0 ≤ Real.exp _
    positivity
  · simpa only [expNegWeight_coe, Real.exp_le_exp, neg_le_neg_iff,
      WithTop.coe_le_coe] using hab

theorem expNegWeight_min (a b : WithTop ℝ) :
    expNegWeight (min a b) = max (expNegWeight a) (expNegWeight b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (expNegWeight_antitone h)]
  · rw [min_eq_right h, max_eq_right (expNegWeight_antitone h)]

theorem expNegWeight_add (a b : WithTop ℝ) :
    expNegWeight (a + b) = expNegWeight a * expNegWeight b := by
  cases a using WithTop.recTopCoe <;> cases b using WithTop.recTopCoe
  · simp
  · simp
  · simp
  · rename_i a b
    change Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b)
    rw [neg_add, Real.exp_add]

/-- The nonarchimedean absolute value actually induced by a real additive valuation. -/
noncomputable def valuationAbsoluteValue {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) : AbsoluteValue K ℝ where
  toFun x := expNegWeight (v x)
  map_mul' x y := by rw [v.map_mul, expNegWeight_add]
  nonneg' x := expNegWeight_nonneg (v x)
  eq_zero' x := (expNegWeight_eq_zero_iff (v x)).trans v.top_iff
  add_le' x y := by
    apply (expNegWeight_antitone (v.map_add x y)).trans
    rw [expNegWeight_min]
    exact max_le_add_of_nonneg (expNegWeight_nonneg _) (expNegWeight_nonneg _)

@[simp] theorem valuationAbsoluteValue_apply {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (x : K) :
    valuationAbsoluteValue v x = expNegWeight (v x) := rfl

theorem valuationAbsoluteValue_isNonarchimedean {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) : IsNonarchimedean (valuationAbsoluteValue v) := by
  intro x y
  simpa only [valuationAbsoluteValue_apply, expNegWeight_min] using
    expNegWeight_antitone (v.map_add x y)

/-- The additive weight associated to a nonnegative absolute value, with `v(0)=∞`. -/
noncomputable def logWeight (r : ℝ) : WithTop ℝ :=
  if r = 0 then ⊤ else ((-Real.log r : ℝ) : WithTop ℝ)

@[simp] theorem logWeight_zero : logWeight 0 = ⊤ := by simp [logWeight]

@[simp] theorem logWeight_one : logWeight 1 = 0 := by simp [logWeight]

@[simp] theorem logWeight_expNegWeight (a : WithTop ℝ) :
    logWeight (expNegWeight a) = a := by
  cases a using WithTop.recTopCoe <;> simp [logWeight]

theorem logWeight_mul (r s : ℝ) : logWeight (r * s) = logWeight r + logWeight s := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  simp only [logWeight, hr, hs, mul_ne_zero hr hs, ↓reduceIte, Real.log_mul hr hs]
  change ((-(Real.log r + Real.log s) : ℝ) : WithTop ℝ) =
    ((-Real.log r + -Real.log s : ℝ) : WithTop ℝ)
  congr 1
  ring

/-- Negative logarithm reverses order on the nonnegative absolute values. -/
theorem logWeight_antitone_nonneg {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    logWeight s ≤ logWeight r := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hspos : 0 < s := hrpos.trans_le hrs
  simp only [logWeight, hr0, ne_of_gt hspos, ↓reduceIte, WithTop.coe_le_coe]
  exact neg_le_neg (Real.log_le_log hrpos hrs)

theorem logWeight_max {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    logWeight (max r s) = min (logWeight r) (logWeight s) := by
  rcases le_total r s with h | h
  · rw [max_eq_right h, min_eq_right (logWeight_antitone_nonneg hr h)]
  · rw [max_eq_left h, min_eq_left (logWeight_antitone_nonneg hs h)]

/-- An actual nonarchimedean absolute value induces an actual additive valuation. -/
noncomputable def logAbsoluteValuation {R : Type*} [Ring R] [Nontrivial R]
    (a : AbsoluteValue R ℝ) (hna : IsNonarchimedean a) : AddValuation R (WithTop ℝ) :=
  AddValuation.of (fun x => logWeight (a x))
    (by simp) (by simp)
    (fun x y => by
      rw [← logWeight_max (a.nonneg x) (a.nonneg y)]
      exact logWeight_antitone_nonneg (a.nonneg (x + y)) (hna x y))
    (fun x y => by rw [a.map_mul, logWeight_mul])

@[simp] theorem logAbsoluteValuation_apply {R : Type*} [Ring R] [Nontrivial R]
    (a : AbsoluteValue R ℝ) (hna : IsNonarchimedean a) (x : R) :
    logAbsoluteValuation a hna x = logWeight (a x) := rfl

/-- Weighted Gauss absolute value, constructed from the coefficient valuation
and radius `exp(-c)`. Its multiplicativity is Mathlib's genuine Gauss theorem. -/
noncomputable def gaussAbsoluteValue {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) : AbsoluteValue K[X] ℝ := by
  letI : IsAbsoluteValue (Polynomial.gaussNorm (valuationAbsoluteValue v) (Real.exp (-c))) :=
    Polynomial.gaussNorm_isAbsoluteValue (valuationAbsoluteValue_isNonarchimedean v)
      (Real.exp_pos (-c))
  exact IsAbsoluteValue.toAbsoluteValue
    (Polynomial.gaussNorm (valuationAbsoluteValue v) (Real.exp (-c)))

@[simp] theorem gaussAbsoluteValue_apply {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p : K[X]) :
    gaussAbsoluteValue v c p = p.gaussNorm (valuationAbsoluteValue v) (Real.exp (-c)) := rfl

theorem gaussAbsoluteValue_isNonarchimedean {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) : IsNonarchimedean (gaussAbsoluteValue v c) :=
  Polynomial.isNonarchimedean_gaussNorm (valuationAbsoluteValue v)
    (valuationAbsoluteValue_isNonarchimedean v) (Real.exp_pos (-c)).le

/-- The weighted Gauss additive valuation on the actual polynomial ring. -/
noncomputable def gaussAddValuation {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) : AddValuation K[X] (WithTop ℝ) :=
  logAbsoluteValuation (gaussAbsoluteValue v c) (gaussAbsoluteValue_isNonarchimedean v c)

@[simp] theorem gaussAddValuation_apply {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p : K[X]) :
    gaussAddValuation v c p =
      logWeight (p.gaussNorm (valuationAbsoluteValue v) (Real.exp (-c))) := rfl

/-- Exponentiated homogeneous weights are exactly the Gauss coefficient terms. -/
theorem gauss_coefficient_exp {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (a : K) (k : ℕ) :
    valuationAbsoluteValue v a * Real.exp (-c) ^ k =
      expNegWeight (v a + (((k : ℝ) * c : ℝ) : WithTop ℝ)) := by
  rw [expNegWeight_add, valuationAbsoluteValue_apply, expNegWeight_coe]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The constructed valuation has the literal source monomial weights. -/
@[simp] theorem gaussAddValuation_monomial {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (a : K) (k : ℕ) :
    gaussAddValuation v c (monomial k a) =
      v a + (((k : ℝ) * c : ℝ) : WithTop ℝ) := by
  rw [gaussAddValuation_apply, gaussNorm_monomial, gauss_coefficient_exp,
    logWeight_expNegWeight]

@[simp] theorem gaussAddValuation_C {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (a : K) :
    gaussAddValuation v c (C a) = v a := by
  rw [gaussAddValuation_apply, gaussNorm_C, valuationAbsoluteValue_apply,
    logWeight_expNegWeight]

@[simp] theorem gaussAddValuation_X {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) :
    gaussAddValuation v c X = (c : WithTop ℝ) := by
  simpa only [monomial_one_one_eq_X, v.map_one, Nat.cast_one, one_mul, zero_add]
    using gaussAddValuation_monomial v c (1 : K) 1

/-- Every coefficient weight bounds the actual polynomial valuation from above. -/
theorem gaussAddValuation_le_coefficient {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p : K[X]) (k : ℕ) :
    gaussAddValuation v c p ≤ v (p.coeff k) + (((k : ℝ) * c : ℝ) : WithTop ℝ) := by
  have h := logWeight_antitone_nonneg
    (mul_nonneg ((valuationAbsoluteValue v).nonneg (p.coeff k))
      (pow_nonneg (Real.exp_pos (-c)).le k))
    (p.le_gaussNorm (valuationAbsoluteValue v) (Real.exp_pos (-c)).le k)
  simpa only [gaussAddValuation_apply, gauss_coefficient_exp, logWeight_expNegWeight] using h

/-- The constructed polynomial valuation is the actual minimum of its finite
coefficient weights. Multiplicativity of this minimum was produced above. -/
theorem gaussAddValuation_eq_inf' {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p : K[X]) (hp : p.support.Nonempty) :
    gaussAddValuation v c p =
      p.support.inf' hp (fun k => v (p.coeff k) + (((k : ℝ) * c : ℝ) : WithTop ℝ)) := by
  apply le_antisymm
  · exact Finset.le_inf' hp _ (fun k _ => gaussAddValuation_le_coefficient v c p k)
  · obtain ⟨i, hi, hnorm⟩ := Finset.exists_mem_eq_sup' hp
      (fun k => valuationAbsoluteValue v (p.coeff k) * Real.exp (-c) ^ k)
    have hvalue : p.gaussNorm (valuationAbsoluteValue v) (Real.exp (-c)) =
        valuationAbsoluteValue v (p.coeff i) * Real.exp (-c) ^ i := by
      simpa only [gaussNorm, hp, ↓reduceDIte] using hnorm
    rw [gaussAddValuation_apply, hvalue, gauss_coefficient_exp, logWeight_expNegWeight]
    exact Finset.inf'_le _ hi

/-- Multiplicativity is a property of the constructed valuation. -/
theorem gaussAddValuation_mul {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p q : K[X]) :
    gaussAddValuation v c (p * q) = gaussAddValuation v c p + gaussAddValuation v c q :=
  (gaussAddValuation v c).map_mul p q

/-- The source's ultrametric inequality for the constructed valuation. -/
theorem gaussAddValuation_add {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p q : K[X]) :
    min (gaussAddValuation v c p) (gaussAddValuation v c q) ≤
      gaussAddValuation v c (p + q) := (gaussAddValuation v c).map_add p q

/-- Finite-support formula including the zero polynomial, whose empty infimum is `∞`. -/
theorem gaussAddValuation_eq_inf {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℝ)) (c : ℝ) (p : K[X]) :
    gaussAddValuation v c p =
      p.support.inf (fun k => v (p.coeff k) + (((k : ℝ) * c : ℝ) : WithTop ℝ)) := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [gaussAddValuation_eq_inf' v c p (support_nonempty.mpr hp), Finset.inf'_eq_inf]

/-- Natural multiples of a finite real valuation weight remain the literal real multiples. -/
theorem withTop_real_nsmul (c : ℝ) (k : ℕ) :
    k • (c : WithTop ℝ) = (((k : ℝ) * c : ℝ) : WithTop ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih]
    change ((((k : ℝ) * c + c : ℝ)) : WithTop ℝ) =
      ((((k + 1 : ℕ) : ℝ) * c : ℝ) : WithTop ℝ)
    congr 1
    push_cast
    ring

/-- An actual scalar-invariant extension valuation agrees with the constructed
Gauss valuation on each polynomial. The invariance hypothesis is the literal
degree-scaling equality, not a coefficient-minimum assumption. -/
theorem invariantValuation_eval₂_eq_gauss
    {S L F : Type*} [Field S] [Infinite S] [Field L] [Field F] [Algebra S F]
    (w : AddValuation F (WithTop ℝ))
    (htrivial : ∀ a : S, a ≠ 0 → w (algebraMap S F a) = 0)
    (f : L →+* F) (p : L[X]) (z : F) {c : ℝ} (hz : w z = (c : WithTop ℝ))
    (hinvariant : ∀ a : S, a ≠ 0 →
      w (p.eval₂ f (algebraMap S F a * z)) = w (p.eval₂ f z)) :
    w (p.eval₂ f z) = gaussAddValuation (w.comap f) c p := by
  rw [valuation_polynomial_eval₂_eq_inf_of_degree_invariance w htrivial f p z hinvariant,
    gaussAddValuation_eq_inf]
  apply Finset.inf_congr rfl
  intro k hk
  change w (f (p.coeff k)) + k • w z =
    w (f (p.coeff k)) + (((k : ℝ) * c : ℝ) : WithTop ℝ)
  rw [hz, withTop_real_nsmul]

section ExtensionWeights

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- The base valuation is the genuine restriction of the extension valuation. -/
noncomputable def baseRestrictedValuation (w : AddValuation F (WithTop ℝ)) :
    AddValuation L (WithTop ℝ) :=
  w.comap (algebraMap L F)

@[simp] theorem baseRestrictedValuation_apply (w : AddValuation F (WithTop ℝ)) (g : L) :
    baseRestrictedValuation (L := L) w g = w (algebraMap L F g) := rfl

/-- The field algebra map is injective, so restriction assigns finite weights
to nonzero base elements. -/
theorem baseRestrictedValuation_ne_top (w : AddValuation F (WithTop ℝ))
    {g : L} (hg : g ≠ 0) : baseRestrictedValuation (L := L) w g ≠ ⊤ := by
  apply w.ne_top_iff.mpr
  intro h
  apply hg
  exact (algebraMap L F).injective (by simpa using h)

/-- Literal homogeneous weights in the source's chosen fiber coordinate. -/
theorem homogeneousWeight_eq (w : AddValuation F (WithTop ℝ))
    (z : F) {c : ℝ} (hz : w z = (c : WithTop ℝ)) (g : L) (k : ℕ) :
    w (algebraMap L F g * z ^ k) =
      (((k : ℝ) * c : ℝ) : WithTop ℝ) + baseRestrictedValuation (L := L) w g := by
  rw [w.map_mul, w.map_pow, hz, withTop_real_nsmul]
  exact add_comm _ _

end ExtensionWeights

/-- Changing the local frame by a local unit leaves each homogeneous weight
unchanged. Nonnegativity on the local ring proves that the unit has value zero. -/
theorem homogeneousWeight_frame_independent
    {A F : Type*} [CommRing A] [Field F]
    (w : AddValuation F (WithTop ℝ)) (f : A →+* F)
    (hcenter : ∀ a : A, (0 : WithTop ℝ) ≤ w (f a))
    (u : Aˣ) (g z : F) (k : ℕ) :
    w (g * (f (u : A) * z) ^ k) = w (g * z ^ k) := by
  rw [w.map_mul, w.map_mul, w.map_pow, w.map_pow, w.map_mul,
    valuation_unit_eq_zero w f hcenter u, zero_add]

/-- Changing both the coefficient and the fiber coordinate represents exactly
the same homogeneous element, before applying any valuation. -/
theorem homogeneousRepresentative_frame_change
    {A F : Type*} [CommRing A] [Field F]
    (f : A →+* F) (u : Aˣ) (g z : F) (k : ℕ) :
    (f (↑u⁻¹ : A) ^ k * g) * (f (u : A) * z) ^ k = g * z ^ k := by
  have hu : f (↑u⁻¹ : A) * f (u : A) = 1 := by
    rw [← map_mul]
    simp
  calc
    _ = (f (↑u⁻¹ : A) * f (u : A)) ^ k * (g * z ^ k) := by
      simp only [mul_pow]
      ring
    _ = _ := by rw [hu]; simp

/-- Membership in the actual positive-valuation ideal forces a finite fiber
weight to be positive. -/
theorem fiberWeight_pos_of_mem_positiveValuationIdeal
    {A F : Type*} [CommRing A] [Field F]
    (w : AddValuation F (WithTop ℝ)) (f : A →+* F)
    (hcenter : ∀ a : A, (0 : WithTop ℝ) ≤ w (f a))
    {z : A} (hz : z ∈ positiveValuationIdeal w f hcenter)
    {c : ℝ} (hc : w (f z) = (c : WithTop ℝ)) : 0 < c := by
  have hpos : (0 : WithTop ℝ) < w (f z) := hz
  rw [hc] at hpos
  exact WithTop.coe_lt_coe.mp hpos

/-- Nonzero positive-ideal elements have an actual positive real fiber weight;
finiteness follows from the field valuation, rather than being supplied. -/
theorem exists_positive_fiberWeight
    {A F : Type*} [CommRing A] [Field F]
    (w : AddValuation F (WithTop ℝ)) (f : A →+* F)
    (hcenter : ∀ a : A, (0 : WithTop ℝ) ≤ w (f a))
    {z : A} (hz : z ∈ positiveValuationIdeal w f hcenter) (hz0 : f z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ w (f z) = (c : WithTop ℝ) := by
  cases hw : w (f z) using WithTop.recTopCoe with
  | top => exact ((w.ne_top_iff.mpr hz0) hw).elim
  | coe c => exact ⟨c, fiberWeight_pos_of_mem_positiveValuationIdeal w f hcenter hz hw, rfl⟩

end SGPT.Foundations.Schemes
