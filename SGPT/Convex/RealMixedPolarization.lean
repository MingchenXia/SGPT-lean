import SGPT.Convex.RealMixedCoefficient
import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

noncomputable section
namespace SGPT.Convex

/-- Native genuine slot expansion identifies the original subset sum with
actual coefficient tuples whose actual image lies in that subset. -/
theorem realMixedCoefficientML_subset_sum {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    realMixedCoefficientML (fun _ : Fin n ↦ ∑ j ∈ S, H j) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        realMixedCoefficientML (fun i ↦ H (g i)) := by
  classical
  have hs : (fun _ : Fin n ↦ ∑ j, (if j ∈ S then (1 : ℝ) else 0) • H j) =
      (fun _ : Fin n ↦ ∑ j ∈ S, H j) := by
    funext i
    simp
  rw [← hs, realMixedCoefficientML_sum]
  simp only [Fintype.prod_boole, ite_mul, one_mul, zero_mul, Finset.sum_filter]

/-- Main's genuine finite polarization algebra isolates the actual mixed
coefficient with exactly the original factorial normalization. -/
theorem realMixedCoefficientML_polarization {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
      ((n.factorial : ℝ) * (∑ j ∈ S, H j).det)) =
      (n.factorial : ℝ) * realMixedCoefficientML H := by
  classical
  simp_rw [← realMixedCoefficientML_diagonal, realMixedCoefficientML_subset_sum]
  exact SGPT.Foundations.Analysis.Pending.PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul
    (fun g ↦ realMixedCoefficientML (fun i ↦ H (g i)))
    (fun σ ↦ realMixedCoefficientML_perm H σ)

/-- Literal normalization cancels the true nonzero factorial, including dimension zero. -/
theorem realMixedCoefficientML_normalized_polarization {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (n.factorial : ℝ)⁻¹ *
      (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ((n.factorial : ℝ) * (∑ j ∈ S, H j).det)) = realMixedCoefficientML H := by
  rw [realMixedCoefficientML_polarization, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]

/-- Existing true PSD coefficient positivity makes the original normalized
finite signed polarization nonnegative, not merely a signed expression. -/
theorem realMixedCoefficientML_normalized_polarization_nonneg {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i, (H i).PosSemidef) :
    0 ≤ (n.factorial : ℝ)⁻¹ *
      (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ((n.factorial : ℝ) * (∑ j ∈ S, H j).det)) := by
  rw [realMixedCoefficientML_normalized_polarization]
  exact realMixedCoefficientML_nonneg H hH

end SGPT.Convex
