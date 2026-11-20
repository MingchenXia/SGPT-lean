import SGPT.Convex.GrowthSum
import SGPT.Convex.MixedAlexandrovPolynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Static draft during the cache no-Lean freeze. Not compiled or adopted.

Independent geometric mixed volume uses Minkowski sums and Euclidean Haar
volume ONLY. It does not mention PSH functions, currents or I-volumes.
The empty Minkowski sum is the additive zero set {0}, including dimension 0.
-/

noncomputable section
namespace SGPT.Convex

open Set MeasureTheory
open scoped BigOperators Pointwise ENNReal

variable {n : ℕ}

/-- Actual finite Minkowski sum, with the standard empty sum {0}. -/
def sourceMinkowskiSubsetSum
    (P : Fin n → Set (EuclideanSpace ℝ (Fin n))) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) := S.sum P

/-- The canonical independent Minkowski polarization of lattice-normalized
Euclidean volume. For compact convex bodies this is their usual mixed volume.
No positivity, polynomiality or desired source-current identity is built in. -/
def sourceGeometricMixedVolume
    (P : Fin n → Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n),
    (-1 : ℝ) ^ (n - S.card) * (volume (sourceMinkowskiSubsetSum P S)).toReal

theorem sourceMinkowskiSubsetSum_empty
    (P : Fin n → Set (EuclideanSpace ℝ (Fin n))) :
    sourceMinkowskiSubsetSum P ∅ = (0 : Set (EuclideanSpace ℝ (Fin n))) := by
  simp [sourceMinkowskiSubsetSum]

/-- Literal normalization of the independently defined geometric quantity. -/
theorem factorial_mul_sourceGeometricMixedVolume
    (P : Fin n → Set (EuclideanSpace ℝ (Fin n))) :
    (n.factorial : ℝ) * sourceGeometricMixedVolume P =
      ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        (volume (sourceMinkowskiSubsetSum P S)).toReal := by
  unfold sourceGeometricMixedVolume
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]

/-- The canonical geometric EMPTY mixed volume is 1 in dimension zero,
proved from the actual Euclidean Haar/Dirac normalization. -/
theorem sourceGeometricMixedVolume_empty
    (P : Fin 0 → Set (EuclideanSpace ℝ (Fin 0))) :
    sourceGeometricMixedVolume P = 1 := by
  classical
  simp [sourceGeometricMixedVolume, sourceMinkowskiSubsetSum,
    Finset.eq_empty_of_isEmpty, volume_euclideanSpace_eq_dirac]

end SGPT.Convex
