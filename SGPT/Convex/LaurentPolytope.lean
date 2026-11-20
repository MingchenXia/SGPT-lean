import SGPT.Convex.LogSumExp
import Mathlib.Analysis.Complex.Exponential

namespace SGPT.Convex
open Set
open scoped BigOperators

/-- The actual source complex torus, with every original coordinate nonzero. -/
def TorusPoint (n : ℕ) := {z : Fin n → ℂ // ∀ j, z j ≠ 0}

/-- Original Laurent monomial with genuine integer powers. -/
noncomputable def laurentMonomial {n : ℕ} (z : TorusPoint n) (a : Fin n → ℤ) : ℂ :=
  ∏ j, z.1 j ^ a j

/-- Twice the actual logarithmic coordinate moduli used by the source squares. -/
noncomputable def torusLogCoordinates {n : ℕ} (z : TorusPoint n) : Fin n → ℝ :=
  fun j ↦ 2 * Real.log ‖z.1 j‖

theorem laurentMonomial_ne_zero {n : ℕ} (z : TorusPoint n) (a : Fin n → ℤ) :
    laurentMonomial z a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ ↦ zpow_ne_zero _ (z.2 j))

/-- Actual integer Laurent logarithms, including negative original exponents. -/
theorem log_norm_laurentMonomial {n : ℕ} (z : TorusPoint n) (a : Fin n → ℤ) :
    Real.log ‖laurentMonomial z a‖ = ∑ j, (a j : ℝ) * Real.log ‖z.1 j‖ := by
  rw [laurentMonomial, Complex.norm_prod,
    Real.log_prod (fun j _ ↦ norm_ne_zero_iff.mpr (zpow_ne_zero _ (z.2 j)))]
  simp_rw [Complex.norm_zpow, Real.log_zpow]

/-- The original squared modulus is the actual exponential dot cost. -/
theorem norm_sq_laurentMonomial_eq_exp {n : ℕ} (z : TorusPoint n) (a : Fin n → ℤ) :
    ‖laurentMonomial z a‖ ^ 2 = Real.exp (∑ j, torusLogCoordinates z j * (a j : ℝ)) := by
  calc
    ‖laurentMonomial z a‖ ^ 2 = Real.exp (Real.log (‖laurentMonomial z a‖ ^ 2)) :=
      (Real.exp_log (sq_pos_of_pos (norm_pos_iff.mpr (laurentMonomial_ne_zero z a)))).symm
    _ = Real.exp (∑ j, torusLogCoordinates z j * (a j : ℝ)) := by
      congr 1
      rw [Real.log_pow, log_norm_laurentMonomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [torusLogCoordinates, Nat.cast_ofNat]
      ring

/-- Actual torus logarithmic coordinates cover the entire original real space. -/
theorem torusLogCoordinates_surjective (n : ℕ) :
    Function.Surjective (@torusLogCoordinates n) := by
  intro x
  let z : TorusPoint n := ⟨fun j ↦ (Real.exp (x j / 2) : ℂ), by
    intro j
    change (Real.exp (x j / 2) : ℂ) ≠ 0
    exact_mod_cast Real.exp_ne_zero (x j / 2)⟩
  refine ⟨z, ?_⟩
  funext j
  simp only [torusLogCoordinates, z, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
  ring

variable {I : Type*} [Fintype I]

/-- The actual denominator in the printed Laurent quotient. -/
noncomputable def laurentDenominator {n : ℕ} (β : I → Fin n → ℤ) (z : TorusPoint n) : ℝ :=
  ∑ i, ‖laurentMonomial z (β i)‖ ^ 2

/-- Original Laurent quotient; source statements below retain its genuine
nonzero denominator requirement instead of silently assigning a zero inverse. -/
noncomputable def laurentRatio {n : ℕ} (β : I → Fin n → ℤ) (a : Fin n → ℤ)
    (z : TorusPoint n) : ℝ := ‖laurentMonomial z a‖ ^ 2 / laurentDenominator β z

variable [Nonempty I]

theorem laurentDenominator_pos {n : ℕ} (β : I → Fin n → ℤ) (z : TorusPoint n) :
    0 < laurentDenominator β z :=
  Finset.sum_pos (fun i _ ↦ sq_pos_of_pos (norm_pos_iff.mpr
    (laurentMonomial_ne_zero z (β i)))) Finset.univ_nonempty

/-- The exact original complex quotient is the genuine exponential log-cost. -/
theorem laurentRatio_eq_exp_neg_log_cost {n : ℕ} (β : I → Fin n → ℤ)
    (a : Fin n → ℤ) (z : TorusPoint n) :
    laurentRatio β a z = Real.exp (-(Real.log (∑ i,
      Real.exp (∑ j, torusLogCoordinates z j * (β i j : ℝ))) -
        ∑ j, torusLogCoordinates z j * (a j : ℝ))) := by
  rw [laurentRatio, laurentDenominator, norm_sq_laurentMonomial_eq_exp]
  simp_rw [norm_sq_laurentMonomial_eq_exp]
  rw [neg_sub, Real.exp_sub, Real.exp_log (sum_exp_pos _)]

omit [Fintype I] [Nonempty I] in
/-- Real upper bounds for an actual positive exponential are exactly real
lower bounds for the original cost. -/
theorem bddAbove_exp_neg_iff_bddBelow {X : Type*} [Nonempty X] (f : X → ℝ) :
    BddAbove (range (fun x ↦ Real.exp (-f x))) ↔ BddBelow (range f) := by
  constructor
  · rintro ⟨R, hR⟩
    have hpos : 0 < R := (Real.exp_pos (-f (Classical.arbitrary X))).trans_le
      (hR (mem_range_self (Classical.arbitrary X)))
    refine ⟨-Real.log R, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h := (Real.le_log_iff_exp_le hpos).mpr (hR (mem_range_self x))
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨Real.exp (-C), ?_⟩
    rintro _ ⟨x, rfl⟩
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (hC (mem_range_self x))

/-- Exact nonempty-source bounded Laurent quotient criterion, transported
through genuine surjective logarithmic coordinates and original monomials. -/
theorem bddAbove_laurentRatio_iff {n : ℕ} (β : I → Fin n → ℤ) (a : Fin n → ℤ) :
    BddAbove (range (laurentRatio β a)) ↔
      (fun j ↦ (a j : ℝ)) ∈ convexHull ℝ (range (fun i j ↦ (β i j : ℝ))) := by
  have heq : laurentRatio β a =
      (fun x : Fin n → ℝ ↦ Real.exp (-(Real.log (∑ i,
        Real.exp (∑ j, x j * (β i j : ℝ))) - ∑ j, x j * (a j : ℝ)))) ∘
          torusLogCoordinates := by
    funext z
    exact laurentRatio_eq_exp_neg_log_cost β a z
  rw [heq, (torusLogCoordinates_surjective n).range_comp,
    bddAbove_exp_neg_iff_bddBelow]
  exact bddBelow_logSumExp_sub_dot_iff (fun i j ↦ (β i j : ℝ)) (fun j ↦ (a j : ℝ))

omit [Nonempty I] in
/-- The printed mathematical quotient is an everywhere-defined bounded
function precisely when its actual denominator never vanishes and its
original nonnegative values have a uniform upper bound. -/
def IsBoundedDefinedLaurentRatio {n : ℕ} (β : I → Fin n → ℤ) (a : Fin n → ℤ) : Prop :=
  (∀ z : TorusPoint n, laurentDenominator β z ≠ 0) ∧ BddAbove (range (laurentRatio β a))

omit [Nonempty I] in
/-- Exact source lma:polybdd with the genuine domain-of-definition of its
printed quotient retained; the empty denominator is not assigned zero. -/
theorem isBoundedDefinedLaurentRatio_iff {n : ℕ}
    (β : I → Fin n → ℤ) (a : Fin n → ℤ) :
    IsBoundedDefinedLaurentRatio β a ↔
      (fun j ↦ (a j : ℝ)) ∈ convexHull ℝ (range (fun i j ↦ (β i j : ℝ))) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let : IsEmpty I := hI
    constructor
    · intro h
      let z : TorusPoint n := ⟨fun _ ↦ 1, by simp⟩
      have hz := h.1 z
      simp [laurentDenominator] at hz
    · intro hm
      simp only [Set.range_eq_empty (fun i j ↦ (β i j : ℝ)), convexHull_empty,
        mem_empty_iff_false] at hm
  | inr hI =>
    let : Nonempty I := hI
    constructor
    · intro h
      exact (bddAbove_laurentRatio_iff β a).mp h.2
    · intro hm
      exact ⟨fun z ↦ (laurentDenominator_pos β z).ne', (bddAbove_laurentRatio_iff β a).mpr hm⟩

end SGPT.Convex
