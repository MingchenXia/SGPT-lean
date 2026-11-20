import SGPT.Toric.TropicalConvexity
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

set_option autoImplicit false

noncomputable section
namespace SGPT.Toric
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff ComplexConjugate

/-- Actual real coordinate projection, with the original Euclidean norms. -/
def toricRealCoordinates (n : ℕ) : ComplexModel n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦ Complex.reCLM.comp
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).restrictScalars ℝ)))

/-- Actual imaginary coordinate projection. -/
def toricImagCoordinates (n : ℕ) : ComplexModel n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦ Complex.imCLM.comp
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).restrictScalars ℝ)))

/-- The actual holomorphic differential of the local logarithm. -/
def toricLogDerivative {n : ℕ} (z : ComplexModel n) : ComplexModel n →L[ℂ] ComplexModel n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦ (z i)⁻¹ • PiLp.proj 2 (fun _ : Fin n ↦ ℂ) i))

theorem toricRealCoordinates_apply {n : ℕ} (v : ComplexModel n) (i : Fin n) :
    toricRealCoordinates n v i = (v i).re := rfl

theorem toricImagCoordinates_apply {n : ℕ} (v : ComplexModel n) (i : Fin n) :
    toricImagCoordinates n v i = (v i).im := rfl

theorem toricLogDerivative_apply {n : ℕ} (z v : ComplexModel n) (i : Fin n) :
    toricLogDerivative z v i = v i / z i := by
  change (z i)⁻¹ * v i = v i / z i
  rw [div_eq_mul_inv, mul_comm]

/-- Actual branch smoothness on the previously constructed ratio slit domain. -/
theorem contDiffOn_localToricLog {n : ℕ} (z : ComplexModel n) :
    ContDiffOn ℂ ∞ (localToricLog z) (toricLogDomain z) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℂ ∞ (fun w : ComplexModel n ↦
    Complex.log (w i / z i) + (Real.log ‖z i‖ : ℂ)) w
  have hdiv : ContDiffAt ℂ ∞ (fun w : ComplexModel n ↦ w i / z i) w := by fun_prop
  exact ((Complex.contDiffAt_log (hw i)).comp w hdiv).add contDiffAt_const

/-- The actual local logarithm differential is produced at every torus basepoint. -/
theorem hasFDerivAt_localToricLog {n : ℕ} {z : ComplexModel n}
    (hz : z ∈ complexTorus n) :
    HasFDerivAt (localToricLog z) (toricLogDerivative z) z := by
  have hcoord : ∀ i : Fin n, HasFDerivAt
      (fun w : ComplexModel n ↦ Complex.log (w i / z i) + (Real.log ‖z i‖ : ℂ))
      ((z i)⁻¹ • PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i) z := by
    intro i
    have hratio : HasFDerivAt (fun w : ComplexModel n ↦ w i / z i)
        ((z i)⁻¹ • PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i) z := by
      convert (((z i)⁻¹ • PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i) :
        ComplexModel n →L[ℂ] ℂ).hasFDerivAt (x := z) using 1
      ext v
      change v i / z i = (z i)⁻¹ * v i
      rw [div_eq_mul_inv, mul_comm]
    have h := (hratio.clog (self_mem_toricLogDomain hz i)).add_const
      (Real.log ‖z i‖ : ℂ)
    simpa [div_self (hz i)] using h
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2
    (fun i ↦ Complex.log (z i / z i) + (Real.log ‖z i‖ : ℂ))).comp z
      (hasFDerivAt_pi.mpr hcoord)

theorem twiceRealCoordinates_eq_smul {n : ℕ} (v : ComplexModel n) :
    twiceRealCoordinates v = (2 : ℝ) • toricRealCoordinates n v := by
  ext i
  change 2 * (v i).re = (2 : ℝ) • (v i).re
  rfl

theorem toricRealCoordinates_mul_I {n : ℕ} (v : ComplexModel n) :
    toricRealCoordinates n (Complex.I • v) = -toricImagCoordinates n v := by
  ext i
  change (Complex.I * v i).re = -(v i).im
  simp

/-- The existing genuine affine Hessian chain rule evaluates the actual
twice-real linear pullback; no second-derivative certificate is supplied. -/
theorem realHessian_twiceRealCoordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (z v w : ComplexModel n) :
    realHessian (fun y ↦ f (twiceRealCoordinates y)) z v w =
      4 * realHessian f (twiceRealCoordinates z)
        (toricRealCoordinates n v) (toricRealCoordinates n w) := by
  have hfun : (fun y : ComplexModel n ↦ f (twiceRealCoordinates y)) =
      (fun y ↦ f (0 + ((2 : ℝ) • toricRealCoordinates n) y)) := by
    funext y
    rw [twiceRealCoordinates_eq_smul]
    simp
  rw [hfun, realHessian_comp_affine hf]
  simp only [zero_add, smul_apply]
  rw [← twiceRealCoordinates_eq_smul z, realHessian_smul_left, realHessian_smul_right]
  ring

/-- The actual normalized exterior derivative on logarithmic coordinates. -/
theorem smoothDDC_twiceRealCoordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (z v w : ComplexModel n) :
    smoothDDC (fun y ↦ f (twiceRealCoordinates y)) z ![v, w] =
      (realHessian f (twiceRealCoordinates z)
        (toricRealCoordinates n v) (toricImagCoordinates n w) -
       realHessian f (twiceRealCoordinates z)
        (toricRealCoordinates n w) (toricImagCoordinates n v)) / Real.pi := by
  have hc : ContDiff ℝ 2 (fun y : ComplexModel n ↦ f (twiceRealCoordinates y)) := by
    convert hf.comp ((2 : ℝ) • toricRealCoordinates n).contDiff using 1
    funext y
    rw [twiceRealCoordinates_eq_smul]
    rfl
  rw [smoothDDC_apply_eq_realHessian hc.contDiffAt,
    realHessian_twiceRealCoordinates hf, realHessian_twiceRealCoordinates hf,
    toricRealCoordinates_mul_I, toricRealCoordinates_mul_I]
  simp only [realHessian_eq_fderiv, map_neg]
  ring

/-- The actual full normalized tropical two-form, evaluated on arbitrary real
tangent vectors; the genuine local logarithm and existing holomorphic
pullback theorem remove all second logarithm derivatives. -/
theorem smoothDDC_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) (v w : ComplexModel n) :
    smoothDDC (fun y ↦ f (tropicalization y)) z ![v, w] =
      (realHessian f (tropicalization z)
        (toricRealCoordinates n (toricLogDerivative z v))
        (toricImagCoordinates n (toricLogDerivative z w)) -
       realHessian f (tropicalization z)
        (toricRealCoordinates n (toricLogDerivative z w))
        (toricImagCoordinates n (toricLogDerivative z v))) / Real.pi := by
  have hρ : ContDiff ℝ ∞ (fun y : ComplexModel n ↦ f (twiceRealCoordinates y)) := by
    convert hf.comp ((2 : ℝ) • toricRealCoordinates n).contDiff using 1
    funext y
    rw [twiceRealCoordinates_eq_smul]
    rfl
  have hgerm : (fun y : ComplexModel n ↦ f (tropicalization y)) =ᶠ[𝓝 z]
      (fun y ↦ f (twiceRealCoordinates (localToricLog z y))) := by
    filter_upwards [(isOpen_toricLogDomain z).mem_nhds (self_mem_toricLogDomain hz)]
      with y hy
    rw [twiceRealCoordinates_localToricLog hz hy]
  have hder : fderiv ℝ (localToricLog z) z =
      (toricLogDerivative z).restrictScalars ℝ := by
    rw [(hasFDerivAt_localToricLog hz).differentiableAt.fderiv_restrictScalars ℝ,
      (hasFDerivAt_localToricLog hz).fderiv]
  rw [smoothDDC_congr hgerm,
    HolomorphicDDC.smoothDDC_comp (isOpen_toricLogDomain z) isOpen_univ
      (contDiffOn_localToricLog z) hρ.contDiffOn (mapsTo_univ _ _)
      (self_mem_toricLogDomain hz)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  have hvec : (fun i ↦ fderiv ℝ (localToricLog z) z (![v, w] i)) =
      ![toricLogDerivative z v, toricLogDerivative z w] := by
    ext i
    fin_cases i <;> simp [hder]
  rw [hvec, smoothDDC_twiceRealCoordinates
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    twiceRealCoordinates_localToricLog hz (self_mem_toricLogDomain hz)]

/-- The literal original coordinate second partial derivatives. -/
def tropicalHessianEntry {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  realHessian f x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Actual Euclidean basis expansion of the genuine real Hessian. -/
theorem realHessian_eq_coordinate_sum {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    realHessian f x v w = ∑ i, ∑ j, v i * w j * tropicalHessianEntry f x i j := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : ∑ i, v i • b i = v := b.sum_repr v
  have hw : ∑ i, w i • b i = w := b.sum_repr w
  calc
    realHessian f x v w = realHessian f x (∑ i, v i • b i) (∑ j, w j • b j) := by
      rw [hv, hw]
    _ = _ := by
      rw [realHessian_eq_fderiv,
        show (fderiv ℝ (fderiv ℝ f) x) (∑ i, v i • b i) =
          ∑ i, (fderiv ℝ (fderiv ℝ f) x) (v i • b i) from map_sum _ _ _,
        sum_apply]
      simp only [map_smul, smul_apply, map_sum, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [tropicalHessianEntry, realHessian_eq_fderiv, b]
      ring

/-- The genuine original smooth tropical form in real coordinate evaluation. -/
theorem smoothDDC_tropicalization_coordinate_sum {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) (v w : ComplexModel n) :
    smoothDDC (fun y ↦ f (tropicalization y)) z ![v, w] =
      (∑ i, ∑ j, tropicalHessianEntry f (tropicalization z) i j *
        ((v i / z i).re * (w j / z j).im -
         (w i / z i).re * (v j / z j).im)) / Real.pi := by
  rw [smoothDDC_tropicalization hf hz, realHessian_eq_coordinate_sum,
    realHessian_eq_coordinate_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [toricRealCoordinates_apply, toricImagCoordinates_apply,
    toricLogDerivative_apply]
  ring

/-- Symmetry comes from the actual second derivative of the original function. -/
theorem tropicalHessianEntry_symm {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    tropicalHessianEntry f x i j = tropicalHessianEntry f x j i := by
  simp only [tropicalHessianEntry, realHessian_eq_fderiv]
  have hf2 : ContDiff ℝ 2 f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact (hf2.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- Genuine finite symmetric-coordinate arithmetic used to present the real
alternating form as the original complex wedge expression. -/
theorem symmetric_coordinate_sum_swap {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (a b : Fin n → ℝ) :
    (∑ i, ∑ j, H i j * a i * b j) = ∑ i, ∑ j, H i j * b i * a j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hH j i]
  ring

/-- The original complex wedge expression is an actual real alternating
two-form whenever its genuine coefficient matrix is symmetric. -/
theorem symmetric_complex_coordinate_wedge {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (a b : Fin n → ℂ) :
    Complex.I / (2 * (Real.pi : ℂ)) *
      (∑ i, ∑ j, (H i j : ℂ) * (a i * conj (b j) - b i * conj (a j))) =
    (((∑ i, ∑ j, H i j * ((a i).re * (b j).im -
      (b i).re * (a j).im)) / Real.pi : ℝ) : ℂ) := by
  let S : ℂ := ∑ i, ∑ j, (H i j : ℂ) * a i * conj (b j)
  let T : ℝ := ∑ i, ∑ j, H i j * ((a i).re * (b j).im - (b i).re * (a j).im)
  have hconj : (∑ i, ∑ j, (H i j : ℂ) * b i * conj (a j)) = conj S := by
    dsimp [S]
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
    simp [mul_comm, mul_assoc]
  have hSim : S.im = -T := by
    calc
      S.im = (∑ i, ∑ j, H i j * (a i).im * (b j).re) -
          (∑ i, ∑ j, H i j * (a i).re * (b j).im) := by
        simp only [S, Complex.im_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
        ring
      _ = -T := by
        rw [symmetric_coordinate_sum_swap H hH (fun i ↦ (a i).im) (fun i ↦ (b i).re)]
        simp only [T, mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
        ring
  have hsum : (∑ i, ∑ j, (H i j : ℂ) *
      (a i * conj (b j) - b i * conj (a j))) = S - conj S := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    exact congrArg (S - ·) hconj
  rw [hsum]
  change Complex.I / (2 * (Real.pi : ℂ)) * (S - conj S) = ((T / Real.pi : ℝ) : ℂ)
  apply Complex.ext
  · have h2r : (2 : ℂ).re = (2 : ℝ) := by norm_num
    have h2i : (2 : ℂ).im = (0 : ℝ) := by norm_num
    simp only [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, hSim,
      Complex.normSq_apply, h2r, h2i]
    field_simp [Real.pi_ne_zero]
    ring
  · simp [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.mul_re,
      Complex.normSq_apply]

/-- SGPT `eq:ddctrop`, with the literal original complex wedge evaluation,
the actual twice-logarithmic modulus, and the exact source normalization.
This equality on arbitrary tangent vectors specifies the complete two-form. -/
theorem smoothDDC_tropicalization_source {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) (v w : ComplexModel n) :
    (smoothDDC (fun y ↦ f (tropicalization y)) z ![v, w] : ℂ) =
      Complex.I / (2 * (Real.pi : ℂ)) *
        (∑ i, ∑ j, (tropicalHessianEntry f (tropicalization z) i j : ℂ) *
          (z i)⁻¹ * (conj (z j))⁻¹ *
          (v i * conj (w j) - w i * conj (v j))) := by
  rw [smoothDDC_tropicalization_coordinate_sum hf hz]
  rw [← symmetric_complex_coordinate_wedge
    (tropicalHessianEntry f (tropicalization z))
    (tropicalHessianEntry_symm hf (tropicalization z))
    (fun i ↦ v i / z i) (fun i ↦ w i / z i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv, map_mul, map_inv₀]
  ring

end SGPT.Toric
