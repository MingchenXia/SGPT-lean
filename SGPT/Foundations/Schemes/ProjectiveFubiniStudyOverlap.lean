import SGPT.Foundations.Schemes.ProjectiveFubiniStudyMetric
import SGPT.Foundations.Schemes.PolynomialProjectiveAnticanonical

/-! # Literal projective ratio covariance of the normalized metric

The finite Euclidean homogeneous form is invariant under a simultaneous
nonzero scalar and under addition of radial tangent vectors. Normalized
quotient coordinates therefore preserve the actual coordinate metric.
-/

open scoped BigOperators ComplexConjugate ContDiff

set_option backward.isDefEq.respectTransparency false

namespace SGPT.Foundations.Schemes

noncomputable section

/-- The literal homogeneous Euclidean Hermitian form with the manuscript factor. -/
def projectiveFubiniStudyHomogeneousHermitian (n : ℕ) (q v w : Fin (n + 1) → ℂ) : ℂ :=
  (n + 1 : ℂ) *
    (projectiveEuclideanHermitianSum q q * projectiveEuclideanHermitianSum v w -
      projectiveEuclideanHermitianSum v q * projectiveEuclideanHermitianSum q w) /
    projectiveEuclideanHermitianSum q q ^ 2

theorem projectiveFubiniStudyHomogeneousHermitian_radial (n : ℕ)
    (q v w : Fin (n + 1) → ℂ) (a b : ℂ) :
    projectiveFubiniStudyHomogeneousHermitian n q (v + a • q) (w + b • q) =
      projectiveFubiniStudyHomogeneousHermitian n q v w := by
  simp only [projectiveFubiniStudyHomogeneousHermitian,
    projectiveEuclideanHermitianSum_add_left, projectiveEuclideanHermitianSum_add_right,
    projectiveEuclideanHermitianSum_smul_left, projectiveEuclideanHermitianSum_smul_right]
  ring

theorem projectiveEuclideanHermitianSum_self_ne_zero {n : ℕ} (q : Fin n → ℂ) (hq : q ≠ 0) :
    projectiveEuclideanHermitianSum q q ≠ 0 := by
  rw [projectiveEuclideanHermitianSum_self]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (projectiveEuclideanSquaredNorm_pos q hq))

theorem projectiveFubiniStudyHomogeneousHermitian_smul (n : ℕ)
    (q v w : Fin (n + 1) → ℂ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    projectiveFubiniStudyHomogeneousHermitian n (c • q) (c • v) (c • w) =
      projectiveFubiniStudyHomogeneousHermitian n q v w := by
  have hb := projectiveEuclideanHermitianSum_self_ne_zero q hq
  have hcc : conj c ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hc
  simp only [projectiveFubiniStudyHomogeneousHermitian,
    projectiveEuclideanHermitianSum_smul_left, projectiveEuclideanHermitianSum_smul_right]
  field_simp

theorem projectiveFubiniStudyHomogeneousHermitian_normalized (n : ℕ)
    (i : Fin (n + 1)) (q v w : Fin (n + 1) → ℂ)
    (hi : q i = 1) (hvi : v i = 0) (hwi : w i = 0) :
    projectiveFubiniStudyHomogeneousHermitian n q v w =
      projectiveFubiniStudyHermitian (fun a => q (i.succAbove a))
        (fun a => v (i.succAbove a)) (fun a => w (i.succAbove a)) := by
  have hq : projectiveEuclideanHermitianSum q q =
      (projectiveFubiniStudyDenominator (fun a => q (i.succAbove a)) : ℂ) := by
    rw [projectiveEuclideanHermitianSum, Fin.sum_univ_succAbove _ i]
    simp only [hi, map_one, one_mul]
    change 1 + projectiveEuclideanHermitianSum (fun a => q (i.succAbove a))
      (fun a => q (i.succAbove a)) = _
    rw [projectiveEuclideanHermitianSum_self]
    simp only [projectiveFubiniStudyDenominator, Complex.ofReal_add, Complex.ofReal_one]
  have hvw : projectiveEuclideanHermitianSum v w =
      projectiveEuclideanHermitianSum (fun a => v (i.succAbove a))
        (fun a => w (i.succAbove a)) := by
    simp [projectiveEuclideanHermitianSum, Fin.sum_univ_succAbove _ i, hvi]
  have hvq : projectiveEuclideanHermitianSum v q =
      projectiveEuclideanHermitianSum (fun a => v (i.succAbove a))
        (fun a => q (i.succAbove a)) := by
    simp [projectiveEuclideanHermitianSum, Fin.sum_univ_succAbove _ i, hvi]
  have hqw : projectiveEuclideanHermitianSum q w =
      projectiveEuclideanHermitianSum (fun a => q (i.succAbove a))
        (fun a => w (i.succAbove a)) := by
    simp [projectiveEuclideanHermitianSum, Fin.sum_univ_succAbove _ i, hwi]
  simp only [projectiveFubiniStudyHomogeneousHermitian, projectiveFubiniStudyHermitian,
    hq, hvw, hvq, hqw]

/-- The genuine derivative vector of homogeneous normalization at coordinate `j`. -/
def projectiveFubiniStudyQuotientTangent (n : ℕ) (j : Fin (n + 1))
    (q v : Fin (n + 1) → ℂ) (u : ℂˣ) : Fin (n + 1) → ℂ :=
  (↑(u⁻¹) : ℂ) • v + (-(↑(u⁻¹) : ℂ) * v j) • ((↑(u⁻¹) : ℂ) • q)

theorem projectiveFubiniStudyQuotientTangent_apply (n : ℕ) (j k : Fin (n + 1))
    (q v : Fin (n + 1) → ℂ) (u : ℂˣ) :
    projectiveFubiniStudyQuotientTangent n j q v u k =
      (↑(u⁻¹) : ℂ) * v k - q k * (↑(u⁻¹) : ℂ) ^ 2 * v j := by
  simp only [projectiveFubiniStudyQuotientTangent, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem projectiveFubiniStudyQuotientTangent_pivot (n : ℕ) (j : Fin (n + 1))
    (q v : Fin (n + 1) → ℂ) (u : ℂˣ) (hu : (u : ℂ) = q j) :
    projectiveFubiniStudyQuotientTangent n j q v u j = 0 := by
  simp only [projectiveFubiniStudyQuotientTangent, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hu, Units.inv_mul]
  ring

theorem projectiveFubiniStudyHomogeneousHermitian_quotient (n : ℕ) (j : Fin (n + 1))
    (q v w : Fin (n + 1) → ℂ) (hq : q ≠ 0) (u : ℂˣ) :
    projectiveFubiniStudyHomogeneousHermitian n ((↑(u⁻¹) : ℂ) • q)
      (projectiveFubiniStudyQuotientTangent n j q v u)
      (projectiveFubiniStudyQuotientTangent n j q w u) =
      projectiveFubiniStudyHomogeneousHermitian n q v w := by
  rw [projectiveFubiniStudyQuotientTangent, projectiveFubiniStudyQuotientTangent,
    projectiveFubiniStudyHomogeneousHermitian_radial]
  exact projectiveFubiniStudyHomogeneousHermitian_smul n q v w hq _ (Units.ne_zero _)

/-- Literal quotient-coordinate covariance before rewriting the derivative as a matrix. -/
theorem projectiveFubiniStudyHermitian_quotient (n : ℕ) (i j : Fin (n + 1))
    (q v w : Fin (n + 1) → ℂ) (hi : q i = 1) (hvi : v i = 0) (hwi : w i = 0)
    (u : ℂˣ) (hu : (u : ℂ) = q j) :
    projectiveFubiniStudyHermitian (fun a => (↑(u⁻¹) : ℂ) * q (j.succAbove a))
      (fun a => projectiveFubiniStudyQuotientTangent n j q v u (j.succAbove a))
      (fun a => projectiveFubiniStudyQuotientTangent n j q w u (j.succAbove a)) =
      projectiveFubiniStudyHermitian (fun a => q (i.succAbove a))
        (fun a => v (i.succAbove a)) (fun a => w (i.succAbove a)) := by
  have hq : q ≠ 0 := by
    intro h
    have : q i = 0 := congrFun h i
    rw [hi] at this
    exact one_ne_zero this
  have hj : ((↑(u⁻¹) : ℂ) • q) j = 1 := by
    change (↑(u⁻¹) : ℂ) * q j = 1
    rw [← hu, Units.inv_mul]
  calc
    _ = projectiveFubiniStudyHomogeneousHermitian n ((↑(u⁻¹) : ℂ) • q)
        (projectiveFubiniStudyQuotientTangent n j q v u)
        (projectiveFubiniStudyQuotientTangent n j q w u) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (projectiveFubiniStudyHomogeneousHermitian_normalized n j _ _ _ hj
          (projectiveFubiniStudyQuotientTangent_pivot n j q v u hu)
          (projectiveFubiniStudyQuotientTangent_pivot n j q w u hu)).symm
    _ = projectiveFubiniStudyHomogeneousHermitian n q v w :=
      projectiveFubiniStudyHomogeneousHermitian_quotient n j q v w hq u
    _ = _ := projectiveFubiniStudyHomogeneousHermitian_normalized n i q v w hi hvi hwi

theorem projectiveFubiniStudyNormalizedVector_sum (n : ℕ) (i : Fin (n + 1))
    (v : Fin (n + 1) → ℂ) (hvi : v i = 0) (k : Fin (n + 1)) :
    v k = ∑ b : Fin n, (if k = i.succAbove b then 1 else 0 : ℂ) * v (i.succAbove b) := by
  classical
  refine Fin.succAboveCases i ?_ (fun a => ?_) k
  · simp [hvi]
  · simp

/-- The actual quotient tangent has cotangent's literal new-row/old-column Jacobian. -/
theorem projectiveFubiniStudyQuotientTangent_jacobian (n : ℕ) (i j : Fin (n + 1))
    (q v : Fin (n + 1) → ℂ) (hvi : v i = 0) (u : ℂˣ) (a : Fin n) :
    projectiveFubiniStudyQuotientTangent n j q v u (j.succAbove a) =
      ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * v (i.succAbove b) := by
  classical
  rw [projectiveFubiniStudyQuotientTangent_apply,
    projectiveFubiniStudyNormalizedVector_sum n i v hvi (j.succAbove a),
    projectiveFubiniStudyNormalizedVector_sum n i v hvi j]
  simp only [projectiveQuotientJacobian, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_assoc]

/-- The literal normalized coordinate Hermitian forms agree under the actual ratio Jacobian. -/
theorem projectiveFubiniStudyHermitian_jacobian (n : ℕ) (i j : Fin (n + 1))
    (q v w : Fin (n + 1) → ℂ) (hi : q i = 1) (hvi : v i = 0) (hwi : w i = 0)
    (u : ℂˣ) (hu : (u : ℂ) = q j) :
    projectiveFubiniStudyHermitian (fun a => (↑(u⁻¹) : ℂ) * q (j.succAbove a))
      (fun a => ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * v (i.succAbove b))
      (fun a => ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * w (i.succAbove b)) =
      projectiveFubiniStudyHermitian (fun a => q (i.succAbove a))
        (fun a => v (i.succAbove a)) (fun a => w (i.succAbove a)) := by
  simpa only [projectiveFubiniStudyQuotientTangent_jacobian n i j q v hvi,
    projectiveFubiniStudyQuotientTangent_jacobian n i j q w hwi] using
      projectiveFubiniStudyHermitian_quotient n i j q v w hi hvi hwi u hu

theorem projectiveFubiniStudyRealMetric_jacobian (n : ℕ) (i j : Fin (n + 1))
    (q v w : Fin (n + 1) → ℂ) (hi : q i = 1) (hvi : v i = 0) (hwi : w i = 0)
    (u : ℂˣ) (hu : (u : ℂ) = q j) :
    projectiveFubiniStudyRealMetric (fun a => (↑(u⁻¹) : ℂ) * q (j.succAbove a))
      (fun a => ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * v (i.succAbove b))
      (fun a => ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * w (i.succAbove b)) =
      projectiveFubiniStudyRealMetric (fun a => q (i.succAbove a))
        (fun a => v (i.succAbove a)) (fun a => w (i.succAbove a)) :=
  congrArg (fun x : ℂ => 2 * x.re) (projectiveFubiniStudyHermitian_jacobian n i j q v w hi hvi hwi u hu)

end

end SGPT.Foundations.Schemes
