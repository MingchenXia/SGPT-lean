import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # The literal normalized Fubini–Study coordinate metric

All sums below are finite Euclidean sums. The coordinate model retains its
usual product topology and sup norm; these sums do not identify that norm
with a Euclidean norm. The factor `n + 1` is the manuscript's normalization.
-/

open scoped BigOperators ComplexConjugate ContDiff Manifold
open Manifold Bundle

set_option backward.isDefEq.respectTransparency false

namespace SGPT.Foundations.Schemes

noncomputable section

/-- The literal finite Euclidean Hermitian sum, conjugate-linear on the left. -/
def projectiveEuclideanHermitianSum {n : ℕ} (v w : Fin n → ℂ) : ℂ :=
  ∑ i, conj (v i) * w i

/-- The literal finite sum of squared Euclidean coordinate norms. -/
def projectiveEuclideanSquaredNorm {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem projectiveEuclideanHermitianSum_eq_inner {n : ℕ} (v w : Fin n → ℂ) :
    projectiveEuclideanHermitianSum v w =
      inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) := by
  simp [projectiveEuclideanHermitianSum, PiLp.inner_apply, mul_comm]

theorem projectiveEuclideanSquaredNorm_eq_norm_sq {n : ℕ} (v : Fin n → ℂ) :
    projectiveEuclideanSquaredNorm v = ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp [projectiveEuclideanSquaredNorm, EuclideanSpace.norm_sq_eq,
    Complex.normSq_eq_norm_sq]

theorem projectiveEuclideanSquaredNorm_nonneg {n : ℕ} (v : Fin n → ℂ) :
    0 ≤ projectiveEuclideanSquaredNorm v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)

theorem projectiveEuclideanSquaredNorm_pos {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < projectiveEuclideanSquaredNorm v := by
  rw [projectiveEuclideanSquaredNorm_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  apply hv
  exact (WithLp.toLp_injective 2) h

theorem projectiveEuclideanHermitianSum_self {n : ℕ} (v : Fin n → ℂ) :
    projectiveEuclideanHermitianSum v v = (projectiveEuclideanSquaredNorm v : ℂ) := by
  simp [projectiveEuclideanHermitianSum, projectiveEuclideanSquaredNorm,
    Complex.normSq_eq_conj_mul_self]

theorem projectiveEuclideanHermitianSum_conj_symm {n : ℕ} (v w : Fin n → ℂ) :
    conj (projectiveEuclideanHermitianSum v w) =
      projectiveEuclideanHermitianSum w v := by
  simp [projectiveEuclideanHermitianSum, map_sum, mul_comm]

theorem projectiveEuclideanHermitianSum_add_left {n : ℕ} (u v w : Fin n → ℂ) :
    projectiveEuclideanHermitianSum (u + v) w =
      projectiveEuclideanHermitianSum u w + projectiveEuclideanHermitianSum v w := by
  simp [projectiveEuclideanHermitianSum, add_mul, Finset.sum_add_distrib]

theorem projectiveEuclideanHermitianSum_add_right {n : ℕ} (u v w : Fin n → ℂ) :
    projectiveEuclideanHermitianSum u (v + w) =
      projectiveEuclideanHermitianSum u v + projectiveEuclideanHermitianSum u w := by
  simp [projectiveEuclideanHermitianSum, mul_add, Finset.sum_add_distrib]

theorem projectiveEuclideanHermitianSum_smul_left {n : ℕ} (c : ℂ) (v w : Fin n → ℂ) :
    projectiveEuclideanHermitianSum (c • v) w = conj c * projectiveEuclideanHermitianSum v w := by
  simp [projectiveEuclideanHermitianSum, Finset.mul_sum, mul_assoc]

theorem projectiveEuclideanHermitianSum_smul_right {n : ℕ} (c : ℂ) (v w : Fin n → ℂ) :
    projectiveEuclideanHermitianSum v (c • w) = c * projectiveEuclideanHermitianSum v w := by
  simp [projectiveEuclideanHermitianSum, Finset.mul_sum, mul_left_comm]

theorem projectiveEuclideanHermitianSum_cauchySchwarz {n : ℕ} (v w : Fin n → ℂ) :
    Complex.normSq (projectiveEuclideanHermitianSum v w) ≤
      projectiveEuclideanSquaredNorm v * projectiveEuclideanSquaredNorm w := by
  rw [Complex.normSq_eq_norm_sq, projectiveEuclideanHermitianSum_eq_inner,
    projectiveEuclideanSquaredNorm_eq_norm_sq, projectiveEuclideanSquaredNorm_eq_norm_sq,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The actual positive projective denominator in an affine coordinate chart. -/
def projectiveFubiniStudyDenominator {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  1 + projectiveEuclideanSquaredNorm z

theorem projectiveFubiniStudyDenominator_pos {n : ℕ} (z : Fin n → ℂ) :
    0 < projectiveFubiniStudyDenominator z := by
  have := projectiveEuclideanSquaredNorm_nonneg z
  unfold projectiveFubiniStudyDenominator
  linarith

/-- The manuscript-normalized literal coordinate Hermitian form. -/
def projectiveFubiniStudyHermitian {n : ℕ} (z v w : Fin n → ℂ) : ℂ :=
  (n + 1 : ℂ) *
    ((projectiveFubiniStudyDenominator z : ℂ) * projectiveEuclideanHermitianSum v w -
      projectiveEuclideanHermitianSum v z * projectiveEuclideanHermitianSum z w) /
    (projectiveFubiniStudyDenominator z : ℂ) ^ 2

/-- The corresponding real Riemannian coordinate form, with the factor `2`. -/
def projectiveFubiniStudyRealMetric {n : ℕ} (z v w : Fin n → ℂ) : ℝ :=
  2 * (projectiveFubiniStudyHermitian z v w).re

theorem projectiveFubiniStudyHermitian_add_left {n : ℕ} (z u v w : Fin n → ℂ) :
    projectiveFubiniStudyHermitian z (u + v) w =
      projectiveFubiniStudyHermitian z u w + projectiveFubiniStudyHermitian z v w := by
  simp only [projectiveFubiniStudyHermitian, projectiveEuclideanHermitianSum_add_left]
  ring

theorem projectiveFubiniStudyHermitian_add_right {n : ℕ} (z u v w : Fin n → ℂ) :
    projectiveFubiniStudyHermitian z u (v + w) =
      projectiveFubiniStudyHermitian z u v + projectiveFubiniStudyHermitian z u w := by
  simp only [projectiveFubiniStudyHermitian, projectiveEuclideanHermitianSum_add_right]
  ring

theorem projectiveFubiniStudyHermitian_smul_left {n : ℕ}
    (z v w : Fin n → ℂ) (c : ℂ) :
    projectiveFubiniStudyHermitian z (c • v) w = conj c * projectiveFubiniStudyHermitian z v w := by
  simp only [projectiveFubiniStudyHermitian, projectiveEuclideanHermitianSum_smul_left]
  ring

theorem projectiveFubiniStudyHermitian_smul_right {n : ℕ}
    (z v w : Fin n → ℂ) (c : ℂ) :
    projectiveFubiniStudyHermitian z v (c • w) = c * projectiveFubiniStudyHermitian z v w := by
  simp only [projectiveFubiniStudyHermitian, projectiveEuclideanHermitianSum_smul_right]
  ring

theorem projectiveFubiniStudyHermitian_conj_symm {n : ℕ} (z v w : Fin n → ℂ) :
    conj (projectiveFubiniStudyHermitian z v w) = projectiveFubiniStudyHermitian z w v := by
  simp only [projectiveFubiniStudyHermitian, map_div₀, map_mul, map_sub, map_pow,
    projectiveEuclideanHermitianSum_conj_symm, Complex.conj_ofReal,
    map_add, map_natCast, map_one]
  ring

/-- The actual conjugate-linear/linear bundled Hermitian coordinate form. -/
def projectiveFubiniStudySesquilinear (n : ℕ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ _ _ (projectiveFubiniStudyHermitian z)
    (projectiveFubiniStudyHermitian_add_left z)
    (fun c v w => projectiveFubiniStudyHermitian_smul_left z v w c)
    (projectiveFubiniStudyHermitian_add_right z)
    (fun c v w => projectiveFubiniStudyHermitian_smul_right z v w c)

theorem projectiveFubiniStudyHermitian_self {n : ℕ} (z v : Fin n → ℂ) :
    projectiveFubiniStudyHermitian z v v =
      (((n + 1 : ℝ) * (projectiveFubiniStudyDenominator z * projectiveEuclideanSquaredNorm v -
        Complex.normSq (projectiveEuclideanHermitianSum v z)) /
        projectiveFubiniStudyDenominator z ^ 2 : ℝ) : ℂ) := by
  rw [projectiveFubiniStudyHermitian, projectiveEuclideanHermitianSum_self,
    ← projectiveEuclideanHermitianSum_conj_symm v z, mul_comm
      (projectiveEuclideanHermitianSum v z), ← Complex.normSq_eq_conj_mul_self]
  push_cast
  rfl

theorem projectiveFubiniStudyHermitian_self_lower_bound {n : ℕ} (z v : Fin n → ℂ) :
    (n + 1 : ℝ) * projectiveEuclideanSquaredNorm v /
        projectiveFubiniStudyDenominator z ^ 2 ≤
      (projectiveFubiniStudyHermitian z v v).re := by
  rw [projectiveFubiniStudyHermitian_self, Complex.ofReal_re]
  have hc := projectiveEuclideanHermitianSum_cauchySchwarz v z
  have hden := projectiveFubiniStudyDenominator_pos z
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold projectiveFubiniStudyDenominator
  nlinarith

theorem projectiveFubiniStudyHermitian_pos {n : ℕ} (z v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < (projectiveFubiniStudyHermitian z v v).re := by
  apply lt_of_lt_of_le _ (projectiveFubiniStudyHermitian_self_lower_bound z v)
  exact div_pos (mul_pos (by positivity) (projectiveEuclideanSquaredNorm_pos v hv))
    (sq_pos_of_pos (projectiveFubiniStudyDenominator_pos z))

theorem projectiveFubiniStudyRealMetric_symm {n : ℕ} (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z v w = projectiveFubiniStudyRealMetric z w v := by
  have h := congrArg Complex.re (projectiveFubiniStudyHermitian_conj_symm z v w)
  simpa only [projectiveFubiniStudyRealMetric, Complex.conj_re] using congrArg (2 * ·) h

theorem projectiveFubiniStudyRealMetric_pos {n : ℕ} (z v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < projectiveFubiniStudyRealMetric z v v :=
  mul_pos (by norm_num) (projectiveFubiniStudyHermitian_pos z v hv)

theorem projectiveFubiniStudyRealMetric_add_left {n : ℕ} (z u v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z (u + v) w =
      projectiveFubiniStudyRealMetric z u w + projectiveFubiniStudyRealMetric z v w := by
  rw [projectiveFubiniStudyRealMetric, projectiveFubiniStudyHermitian_add_left,
    Complex.add_re]
  unfold projectiveFubiniStudyRealMetric
  ring

theorem projectiveFubiniStudyRealMetric_add_right {n : ℕ} (z u v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z u (v + w) =
      projectiveFubiniStudyRealMetric z u v + projectiveFubiniStudyRealMetric z u w := by
  rw [projectiveFubiniStudyRealMetric, projectiveFubiniStudyHermitian_add_right,
    Complex.add_re]
  unfold projectiveFubiniStudyRealMetric
  ring

theorem projectiveFubiniStudyRealMetric_smul_left {n : ℕ}
    (z v w : Fin n → ℂ) (c : ℝ) :
    projectiveFubiniStudyRealMetric z (c • v) w = c * projectiveFubiniStudyRealMetric z v w := by
  change 2 * (projectiveFubiniStudyHermitian z ((c : ℂ) • v) w).re = _
  rw [projectiveFubiniStudyHermitian_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
  unfold projectiveFubiniStudyRealMetric
  ring

theorem projectiveFubiniStudyRealMetric_smul_right {n : ℕ}
    (z v w : Fin n → ℂ) (c : ℝ) :
    projectiveFubiniStudyRealMetric z v (c • w) = c * projectiveFubiniStudyRealMetric z v w := by
  change 2 * (projectiveFubiniStudyHermitian z v ((c : ℂ) • w)).re = _
  rw [projectiveFubiniStudyHermitian_smul_right, Complex.re_ofReal_mul]
  unfold projectiveFubiniStudyRealMetric
  ring

/-- The actual real bilinear form underlying the normalized coordinate metric. -/
def projectiveFubiniStudyBilinear (n : ℕ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (projectiveFubiniStudyRealMetric z)
    (projectiveFubiniStudyRealMetric_add_left z)
    (fun c v w => projectiveFubiniStudyRealMetric_smul_left z v w c)
    (projectiveFubiniStudyRealMetric_add_right z)
    (fun c v w => projectiveFubiniStudyRealMetric_smul_right z v w c)

/-- The genuine continuous bilinear map on the existing finite coordinate model. -/
def projectiveFubiniStudyContinuousBilinear (n : ℕ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (projectiveFubiniStudyBilinear n z))

theorem projectiveFubiniStudyContinuousBilinear_apply (n : ℕ) (z v w : Fin n → ℂ) :
    projectiveFubiniStudyContinuousBilinear n z v w = projectiveFubiniStudyRealMetric z v w :=
  rfl

theorem projectiveEuclideanSquaredNorm_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveEuclideanSquaredNorm (n := n)) := by
  unfold projectiveEuclideanSquaredNorm
  apply ContDiff.sum
  intro i _
  simp only [Complex.normSq_apply]
  simpa only [pow_two, Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] using
    (((Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i)).pow 2).add
      ((Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ i)).pow 2))

theorem projectiveFubiniStudyDenominator_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveFubiniStudyDenominator (n := n)) :=
  contDiff_const.add (projectiveEuclideanSquaredNorm_contDiff n)

theorem projectiveFubiniStudyHermitian_contDiff {n : ℕ} (v w : Fin n → ℂ) :
    ContDiff ℝ ∞ (fun z => projectiveFubiniStudyHermitian z v w) := by
  have hd : ContDiff ℝ ∞ (fun z : Fin n → ℂ => (projectiveFubiniStudyDenominator z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (projectiveFubiniStudyDenominator_contDiff n)
  have hv : ContDiff ℝ ∞ (fun z : Fin n → ℂ => projectiveEuclideanHermitianSum v z) := by
    unfold projectiveEuclideanHermitianSum
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℂ i)
  have hw : ContDiff ℝ ∞ (fun z : Fin n → ℂ => projectiveEuclideanHermitianSum z w) := by
    unfold projectiveEuclideanHermitianSum
    exact ContDiff.sum fun i _ =>
      (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)).mul contDiff_const
  unfold projectiveFubiniStudyHermitian
  simp only [div_eq_mul_inv]
  exact (contDiff_const.mul ((hd.mul contDiff_const).sub (hv.mul hw))).mul
    ((hd.pow 2).inv fun z => pow_ne_zero 2
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (projectiveFubiniStudyDenominator_pos z))))

theorem projectiveFubiniStudyRealMetric_contDiff {n : ℕ} (v w : Fin n → ℂ) :
    ContDiff ℝ ∞ (fun z => projectiveFubiniStudyRealMetric z v w) :=
  contDiff_const.mul (Complex.reCLM.contDiff.comp (projectiveFubiniStudyHermitian_contDiff v w))

theorem projectiveFubiniStudyContinuousBilinear_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveFubiniStudyContinuousBilinear n) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  exact projectiveFubiniStudyRealMetric_contDiff v w

theorem projectiveFubiniStudyRealMetric_unitBall_norm_le {n : ℕ} (z v : Fin n → ℂ)
    (hv : projectiveFubiniStudyRealMetric z v v < 1) :
    ‖v‖ ≤ projectiveFubiniStudyDenominator z := by
  have hd := projectiveFubiniStudyDenominator_pos z
  have hn := projectiveEuclideanSquaredNorm_nonneg v
  have hl := projectiveFubiniStudyHermitian_self_lower_bound z v
  have hn1 : (1 : ℝ) ≤ n + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hd2 : 0 < projectiveFubiniStudyDenominator z ^ 2 := sq_pos_of_pos hd
  have hlow : projectiveEuclideanSquaredNorm v /
      projectiveFubiniStudyDenominator z ^ 2 ≤ (projectiveFubiniStudyHermitian z v v).re := by
    apply le_trans _ hl
    exact div_le_div_of_nonneg_right (by nlinarith) hd2.le
  have hsum : projectiveEuclideanSquaredNorm v ≤ projectiveFubiniStudyDenominator z ^ 2 := by
    have hlt : projectiveEuclideanSquaredNorm v /
        projectiveFubiniStudyDenominator z ^ 2 < 1 := by
      unfold projectiveFubiniStudyRealMetric at hv
      linarith
    exact ((div_lt_one hd2).mp hlt).le
  apply (pi_norm_le_iff_of_nonneg hd.le).mpr
  intro i
  have hi : Complex.normSq (v i) ≤ projectiveEuclideanSquaredNorm v :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  nlinarith [norm_nonneg (v i)]

theorem projectiveFubiniStudyRealMetric_isVonNBounded (n : ℕ) (z : Fin n → ℂ) :
    Bornology.IsVonNBounded ℝ {v | projectiveFubiniStudyRealMetric z v v < 1} := by
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  exact ⟨projectiveFubiniStudyDenominator z,
    fun v hv => projectiveFubiniStudyRealMetric_unitBall_norm_le z v hv⟩

/-- The actual smooth normalized coordinate metric on the real tangent bundle of `ℂⁿ`. -/
def projectiveFubiniStudyCoordinateMetric (n : ℕ) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun z : Fin n → ℂ => TangentSpace 𝓘(ℝ, Fin n → ℂ) z) where
  inner z := projectiveFubiniStudyContinuousBilinear n z
  symm z v w := projectiveFubiniStudyRealMetric_symm z v w
  pos z v hv := projectiveFubiniStudyRealMetric_pos z v hv
  isVonNBounded z := projectiveFubiniStudyRealMetric_isVonNBounded n z
  contMDiff := by
    intro z
    rw [contMDiffAt_section]
    convert! (projectiveFubiniStudyContinuousBilinear_contDiff n).contDiffAt.contMDiffAt
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

end

end SGPT.Foundations.Schemes
