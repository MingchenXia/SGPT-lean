import SGPT.NPP.LogConcavityDinewPsh
import SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
import SGPT.Foundations.Analysis.Pending.DeterminantTraceInf

/-!
# Linearization of the determinant along complex frames

For an `n × n` complex matrix `Y`, `frameMap Y` is the complex-linear map of `ℂⁿ` sending `eₖ` to
the vector with coordinates `conj (Y j k)`. Along this frame the operator
`L_Y f = ∑ₖ leviForm f · (frameMap Y eₖ)` computes `Re tr (Yᴴ H Y)` for the complex Hessian `H`
(`sum_leviForm_frameMap`). The arithmetic–geometric mean inequality gives
`n (det H)^{1/n} ≤ Re tr (Yᴴ H Y)` for `|det Y| = 1` (`mul_rpow_det_le_trace_frame`), and
conversely, if `Re tr (Yᴴ H Y) ≥ n m` for every such `Y`, then `det H ≥ mⁿ`
(`pow_le_det_of_forall_frame`). This is FPT `lem:determinant-linearization-mixed` with
`B = Y Yᴴ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder MatrixOrder

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-- The complex-linear map sending `eₖ` to `coordCombination (Y · k)`. -/
def frameMap (Y : Matrix (Fin n) (Fin n) ℂ) : ComplexModel n →L[ℂ] ComplexModel n :=
  ∑ k, (EuclideanSpace.proj k : ComplexModel n →L[ℂ] ℂ).smulRight
    (coordCombination (fun j => Y j k))

theorem frameMap_apply_coord (Y : Matrix (Fin n) (Fin n) ℂ) (z : ComplexModel n) (j : Fin n) :
    frameMap Y z j = ∑ k, star (Y j k) * z k := by
  simp [frameMap, coordCombination_eq_toLp, mul_comm]

theorem frameMap_coordinateVector (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    frameMap Y (coordinateVector k) = coordCombination (fun j => Y j k) := by
  ext j
  rw [frameMap_apply_coord, coordCombination_eq_toLp]
  simp [coordinateVector, Finset.sum_ite_eq', EuclideanSpace.single_apply]

theorem frameMap_mul (Y Y' : Matrix (Fin n) (Fin n) ℂ) (z : ComplexModel n) :
    frameMap Y (frameMap Y' z) = frameMap (Y * Y') z := by
  ext j
  simp only [frameMap_apply_coord, Matrix.mul_apply, star_sum, star_mul', Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem frameMap_one (z : ComplexModel n) : frameMap 1 z = z := by
  ext j
  simp [frameMap_apply_coord, Matrix.one_apply, Finset.sum_ite_eq]

/-- The quadratic form of a Hermitian matrix at a column, as a matrix entry. -/
theorem star_dotProduct_mulVec_col (Y H : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    star (fun j => Y j k) ⬝ᵥ (H.mulVec (fun j => Y j k)) = (Yᴴ * H * Y) k k := by
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The frame operator on bilinear forms** computes `Re tr (Yᴴ H Y)`. -/
theorem sum_leviFormOfBilin_frameMap {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hA : ∀ x y, A x y = A y x) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ k, leviFormOfBilin A (frameMap Y (coordinateVector k)) =
      (Yᴴ * complexHessianOfBilin A * Y).trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, frameMap_coordinateVector, ← star_dotProduct_mulVec_col,
    dotProduct_mulVec_complexHessianOfBilin hA]
  simp

/-- **The frame operator on functions** computes `Re tr (Yᴴ H Y)`. -/
theorem sum_leviForm_frameMap {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ k, leviForm f z (frameMap Y (coordinateVector k)) =
      (Yᴴ * complexHessian f z * Y).trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, frameMap_coordinateVector, ← star_dotProduct_mulVec_col,
    dotProduct_mulVec_complexHessian_eq_leviForm hf]
  simp

theorem det_conjTranspose_mul_mul (Y H : Matrix (Fin n) (Fin n) ℂ) (hY : ‖Y.det‖ = 1) :
    (Yᴴ * H * Y).det = H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have : star Y.det * Y.det = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hY]
    simp
  calc star Y.det * H.det * Y.det = (star Y.det * Y.det) * H.det := by ring
    _ = H.det := by rw [this, one_mul]

/-- **AM–GM along a frame**: `n (det H)^{1/n} ≤ Re tr (Yᴴ H Y)` for `H ≥ 0`, `|det Y| = 1`. -/
theorem mul_rpow_det_le_trace_frame (hn : 0 < n) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosSemidef) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : ‖Y.det‖ = 1) :
    n * H.det.re ^ ((n : ℝ)⁻¹) ≤ (Yᴴ * H * Y).trace.re := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hX : (Yᴴ * H * Y).PosSemidef := hH.conjTranspose_mul_mul_same Y
  have h := DeterminantTraceInf.rpow_inv_card_re_det_le_re_trace_div hX
  rw [det_conjTranspose_mul_mul Y H hY, Fintype.card_fin] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn'] at h
  linarith

/-- **The determinant from the frame inequalities**: if `Re tr (Yᴴ H Y) ≥ n m` for every `Y`
with `|det Y| = 1`, then `det H ≥ mⁿ`. -/
theorem pow_le_det_of_forall_frame (hn : 0 < n) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ‖Y.det‖ = 1 → n * m ≤ (Yᴴ * H * Y).trace.re) :
    m ^ n ≤ H.det.re := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdet0 : 0 ≤ H.det.re := (Complex.nonneg_iff.mp hH.det_nonneg).1
  have hroot : m ≤ H.det.re ^ ((n : ℝ)⁻¹) := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨B, hB, hdet, htr⟩ :=
      DeterminantTraceInf.exists_posDef_det_eq_one_re_trace_div_le hH (half_pos hε)
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
    simp only [Matrix.star_eq_conjTranspose] at hy
    have hydet : ‖yᴴ.det‖ = 1 := by
      have h1 : B.det = star y.det * y.det := by rw [hy, Matrix.det_mul, Matrix.det_conjTranspose]
      rw [hdet] at h1
      have h2 := congrArg norm h1
      rw [norm_one, norm_mul, norm_star] at h2
      rw [Matrix.det_conjTranspose, norm_star]
      nlinarith [norm_nonneg y.det]
    have h1 := h yᴴ hydet
    have htr' : (yᴴᴴ * H * yᴴ).trace = (B * H).trace := by
      rw [Matrix.conjTranspose_conjTranspose, hy, Matrix.trace_mul_comm (y * H) yᴴ,
        Matrix.mul_assoc]
    rw [htr'] at h1
    rw [Fintype.card_fin, div_le_iff₀ hn'] at htr
    nlinarith
  calc m ^ n ≤ (H.det.re ^ ((n : ℝ)⁻¹)) ^ n := pow_le_pow_left₀ hm hroot n
    _ = H.det.re := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdet0, inv_mul_cancel₀ hn'.ne', Real.rpow_one]

/-- The frame vectors have total squared length at least `n` when `|det Y| = 1`. -/
theorem le_sum_norm_frameMap_sq (hn : 0 < n) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : ‖Y.det‖ = 1) :
    (n : ℝ) ≤ ∑ k, ‖frameMap Y (coordinateVector k)‖ ^ 2 := by
  have h := mul_rpow_det_le_trace_frame hn Matrix.PosSemidef.one hY
  simp only [Matrix.det_one, Complex.one_re, Real.one_rpow, mul_one, Matrix.mul_one] at h
  refine h.trans (le_of_eq ?_)
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, frameMap_coordinateVector, coordCombination_eq_toLp, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.conjTranspose_apply, norm_star]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

end SGPT.NPP.LogConcavityDinew
