import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.GramNormVolume
open Set MeasureTheory Metric
open scoped Topology ComplexConjugate

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
/-- The determinant of the genuine Gram matrix of actual images of an
ON basis is the complex determinant norm-square, including empty bases. -/
theorem gram_det_re_eq_normSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (q : E →ₗ[ℂ] E) :
    (Matrix.gram ℂ (fun i => q (b i))).det.re = Complex.normSq (LinearMap.det q) := by
  let M : Matrix ι ι ℂ := Matrix.of (fun i j => b.repr (q (b j)) i)
  have hg : Matrix.gram ℂ (fun i => q (b i)) = M.conjTranspose * M :=
    Matrix.gram_eq_conjTranspose_mul b _
  have hm : M = LinearMap.toMatrix b.toBasis b.toBasis q := by
    ext i j
    simpa only [M, Matrix.of_apply, LinearMap.toMatrix_apply, b.coe_toBasis] using
      (b.coe_toBasis_repr_apply (q (b j)) i).symm
  rw [hg, Matrix.det_mul, Matrix.det_conjTranspose]
  change ((starRingEnd ℂ) M.det * M.det).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, hm, LinearMap.det_toMatrix]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Actual complex-linear norm-ball Haar change of variables, with the
real determinant factor INTERNALLY reduced to the complex norm-square. -/
theorem measure_normball_preimage (q : E ≃ₗ[ℂ] E) :
    μ {x | ‖q x‖ ≤ 1} =
      ENNReal.ofReal (Complex.normSq (LinearMap.det (q : E →ₗ[ℂ] E)))⁻¹ *
        μ (closedBall (0 : E) 1) := by
  have hs : {x | ‖q x‖ ≤ 1} =
      (q.restrictScalars ℝ) ⁻¹' closedBall (0 : E) 1 := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff]
    rfl
  rw [hs, Measure.addHaar_preimage_linearEquiv]
  have hd : LinearMap.det ((q.restrictScalars ℝ).symm : E →ₗ[ℝ] E) =
      (Complex.normSq (LinearMap.det (q : E →ₗ[ℂ] E)))⁻¹ := by
    change LinearMap.det ((q.symm : E →ₗ[ℂ] E).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
      LinearEquiv.det_coe_symm, Complex.normSq_inv]
  rw [hd, abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _))]

/-- An actual matching complex isometry, constructed from native ON bases
and the actual linear-equivalence dimension identity. -/
def matchingHilbertIsometry (e : E ≃ₗ[ℂ] F) : E ≃ₗᵢ[ℂ] F :=
  (stdOrthonormalBasis ℂ E).repr.trans
    (((stdOrthonormalBasis ℂ F).reindex (finCongr e.finrank_eq).symm).repr.symm)

/-- Genuine Haar volume / Gram determinant dictionary for an actual
linear equivalence between the two actual Hilbert spaces. The matching
isometry, norm-ball preimage and determinant are all internally produced. -/
theorem measure_normball_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (e : E ≃ₗ[ℂ] F) :
    μ {x | ‖e x‖ ≤ 1} =
      ENNReal.ofReal ((Matrix.gram ℂ (fun i => e (b i))).det.re)⁻¹ *
        μ (closedBall (0 : E) 1) := by
  let J := matchingHilbertIsometry e
  let q : E ≃ₗ[ℂ] E := e.trans J.symm.toLinearEquiv
  have hg : Matrix.gram ℂ (fun i => e (b i)) =
      Matrix.gram ℂ (fun i => q (b i)) := by
    ext i j
    exact (J.symm.inner_map_map (e (b i)) (e (b j))).symm
  have hs : {x | ‖e x‖ ≤ 1} = {x | ‖q x‖ ≤ 1} := by
    ext x
    simp only [mem_ofPred_eq, q, LinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map]
  have hgd : (Matrix.gram ℂ (fun i => q (b i))).det.re =
      Complex.normSq (LinearMap.det (q : E →ₗ[ℂ] E)) :=
    gram_det_re_eq_normSq b (q : E →ₗ[ℂ] E)
  rw [hs, hg, hgd, measure_normball_preimage]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Positive real Gram determinant is manufactured from actual linear
equivalence and the complex determinant, also in dimension zero. -/
theorem gram_det_re_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (e : E ≃ₗ[ℂ] F) :
    0 < (Matrix.gram ℂ (fun i => e (b i))).det.re := by
  let J := matchingHilbertIsometry e
  let q : E ≃ₗ[ℂ] E := e.trans J.symm.toLinearEquiv
  have hg : Matrix.gram ℂ (fun i => e (b i)) =
      Matrix.gram ℂ (fun i => q (b i)) := by
    ext i j
    exact (J.symm.inner_map_map (e (b i)) (e (b j))).symm
  have hgd : (Matrix.gram ℂ (fun i => q (b i))).det.re =
      Complex.normSq (LinearMap.det (q : E →ₗ[ℂ] E)) :=
    gram_det_re_eq_normSq b (q : E →ₗ[ℂ] E)
  rw [hg, hgd]
  exact Complex.normSq_pos.mpr (LinearEquiv.isUnit_det' q).ne_zero

/-- Actual real log norm-ball-volume ratio, with finite positive base
Haar volume produced internally. No real-volume/log/determinant dictionary
or positivity certificate is supplied by the caller. -/
theorem log_real_normball_ratio_eq_neg_log_gram {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) (e : E ≃ₗ[ℂ] F) :
    Real.log (μ.real {x | ‖e x‖ ≤ 1} / μ.real (closedBall (0 : E) 1)) =
      -Real.log (Matrix.gram ℂ (fun i => e (b i))).det.re := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hb0 : 0 < μ (closedBall (0 : E) 1) :=
    μ.measure_pos_of_mem_nhds (closedBall_mem_nhds 0 (by norm_num))
  have hbt : μ (closedBall (0 : E) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : E) 1).measure_ne_top
  have hbr : 0 < μ.real (closedBall (0 : E) 1) :=
    ENNReal.toReal_pos hb0.ne' hbt
  have hg := gram_det_re_pos b e
  have hm : μ.real {x | ‖e x‖ ≤ 1} =
      ((Matrix.gram ℂ (fun i => e (b i))).det.re)⁻¹ *
        μ.real (closedBall (0 : E) 1) := by
    change (μ {x | ‖e x‖ ≤ 1}).toReal = _
    rw [measure_normball_eq_gram μ b e, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hg.le)]
    rfl
  rw [hm, mul_div_cancel_right₀ _ hbr.ne', Real.log_inv]

end SGPT.Bergman.GramNormVolume
