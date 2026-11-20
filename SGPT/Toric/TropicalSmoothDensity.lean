import SGPT.Toric.TropicalHessian
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open scoped Topology ContDiff BigOperators ComplexConjugate

/-- The actual original open torus; no new model or transferred topology. -/
def tropicalSmoothDomain (n : ℕ) : TopologicalSpace.Opens (ComplexModel n) :=
  ⟨complexTorus n, isOpen_complexTorus n⟩

/-- Genuine logarithm germs supply smoothness of the unchanged tropical pullback. -/
theorem contDiffOn_tropicalSmoothProfile {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun z : ComplexModel n => f (tropicalization z))
      (tropicalSmoothDomain n) := by
  intro z hz
  have hρ : ContDiff ℝ ∞ (fun y : ComplexModel n => f (twiceRealCoordinates y)) := by
    convert hf.comp ((2 : ℝ) • toricRealCoordinates n).contDiff using 1
    funext y
    rw [twiceRealCoordinates_eq_smul]
    rfl
  have hlog := (((contDiffOn_localToricLog z).restrict_scalars ℝ) z
    (self_mem_toricLogDomain hz)).contDiffAt
      ((isOpen_toricLogDomain z).mem_nhds (self_mem_toricLogDomain hz))
  have heq : (fun y : ComplexModel n => f (tropicalization y)) =ᶠ[𝓝 z]
      (fun y => f (twiceRealCoordinates (localToricLog z y))) := by
    filter_upwards [(isOpen_toricLogDomain z).mem_nhds (self_mem_toricLogDomain hz)]
      with y hy
    rw [twiceRealCoordinates_localToricLog hz hy]
  exact ((hρ.contDiffAt.comp z hlog).congr_of_eventuallyEq heq).contDiffWithinAt

/-- Original convexity manufactures all actual smooth PSH constructor fields. -/
theorem isSmoothPshOn_tropicalSmoothProfile {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    IsSmoothPshOn (tropicalSmoothDomain n) (fun z => f (tropicalization z)) := by
  exact isSmoothPshOn_of_psh (contDiffOn_tropicalSmoothProfile hf)
    (plurisubharmonicOn_tropicalPullback_of_convexOn hc)

private theorem tropicalDensity_real_log_coordinate {n : ℕ}
    (z : ComplexModel n) (j : Fin n) :
    toricRealCoordinates n (toricLogDerivative z (coordinateVector j)) =
      (z j)⁻¹.re • EuclideanSpace.basisFun (Fin n) ℝ j := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [toricRealCoordinates_apply, toricLogDerivative_apply, coordinateVector,
      EuclideanSpace.basisFun_apply]
  · simp [toricRealCoordinates_apply, toricLogDerivative_apply, coordinateVector,
      EuclideanSpace.basisFun_apply, hi]

private theorem tropicalDensity_imag_log_coordinate {n : ℕ}
    (z : ComplexModel n) (j : Fin n) :
    toricImagCoordinates n (toricLogDerivative z (coordinateVector j)) =
      (z j)⁻¹.im • EuclideanSpace.basisFun (Fin n) ℝ j := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [toricImagCoordinates_apply, toricLogDerivative_apply, coordinateVector,
      EuclideanSpace.basisFun_apply]
  · simp [toricImagCoordinates_apply, toricLogDerivative_apply, coordinateVector,
      EuclideanSpace.basisFun_apply, hi]

private theorem tropicalDensity_imag_mul_I {n : ℕ} (v : ComplexModel n) :
    toricImagCoordinates n (Complex.I • v) = toricRealCoordinates n v := by
  ext i
  change (Complex.I * v i).im = (v i).re
  simp

/-- The actual full two-form reads back to the original matrix in every dimension. -/
theorem normalizedHermitianMatrix_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    normalizedHermitianMatrix (smoothDDC (fun y => f (tropicalization y)) z) =
      fun j k => (tropicalHessianEntry f (tropicalization z) j k : ℂ) *
        (z j)⁻¹ * conj ((z k)⁻¹) := by
  ext j k
  have h00 := smoothDDC_tropicalization hf hz (coordinateVector j) (coordinateVector k)
  have h01 := smoothDDC_tropicalization hf hz (coordinateVector j)
    (Complex.I • coordinateVector k)
  rw [map_smul, toricRealCoordinates_mul_I, tropicalDensity_imag_mul_I] at h01
  simp only [tropicalDensity_real_log_coordinate, tropicalDensity_imag_log_coordinate,
    realHessian_eq_fderiv, map_smul, map_neg, smul_apply, neg_apply, smul_eq_mul] at h00 h01
  have hsym := tropicalHessianEntry_symm hf (tropicalization z) k j
  change tropicalHessianEntry f (tropicalization z) k j =
    tropicalHessianEntry f (tropicalization z) j k at hsym
  change (Real.pi : ℂ) * ((smoothDDC _ z ![coordinateVector j,
    Complex.I • coordinateVector k] : ℂ) -
    Complex.I * (smoothDDC _ z ![coordinateVector j, coordinateVector k] : ℂ)) = _
  rw [h00, h01]
  simp only [tropicalHessianEntry, realHessian_eq_fderiv] at hsym ⊢
  rw [hsym]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im]
  all_goals field_simp [Real.pi_ne_zero]; ring

/-- This is the original second derivative, identified by the existing genuine DDC theorem. -/
theorem complexHessian_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    complexHessian (fun y => f (tropicalization y)) z =
      fun j k => (tropicalHessianEntry f (tropicalization z) j k : ℂ) *
        (z j)⁻¹ * conj ((z k)⁻¹) := by
  have hs := ((contDiffOn_tropicalSmoothProfile hf) z hz).contDiffAt
    ((isOpen_complexTorus n).mem_nhds hz)
  rw [← normalizedHermitianMatrix_smoothDDC
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  exact normalizedHermitianMatrix_tropicalization hf hz

/-- Actual finite matrix multiplication and the original real embedding supply the determinant. -/
theorem det_complexHessian_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    (complexHessian (fun y => f (tropicalization y)) z).det =
      ((Matrix.det ((fun j k : Fin n => tropicalHessianEntry f (tropicalization z) j k) :
        Matrix (Fin n) (Fin n) ℝ) /
        (∏ i : Fin n, Complex.normSq (z i)) : ℝ) : ℂ) := by
  classical
  let H : Matrix (Fin n) (Fin n) ℝ :=
    fun j k => tropicalHessianEntry f (tropicalization z) j k
  let α : Fin n → ℂ := fun j => (z j)⁻¹
  have hM : complexHessian (fun y => f (tropicalization y)) z =
      Matrix.diagonal α * (H.map Complex.ofRealHom) * Matrix.diagonal (fun i => conj (α i)) := by
    rw [complexHessian_tropicalization hf hz]
    ext j k
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    change (H j k : ℂ) * α j * conj (α k) = α j * (H j k : ℂ) * conj (α k)
    ring
  have hprod : (∏ i, α i) * (∏ i, conj (α i)) =
      (((∏ i : Fin n, Complex.normSq (z i))⁻¹ : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    have hpoint (i : Fin n) : α i * conj (α i) = ((Complex.normSq (z i))⁻¹ : ℝ) := by
      dsimp [α]
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_inv]
    simp_rw [hpoint]
    push_cast
    rw [Finset.prod_inv_distrib]
  have hdet : (H.map Complex.ofRealHom).det = (H.det : ℂ) :=
    (Complex.ofRealHom.map_det H).symm
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hdet]
  change (∏ i, α i) * (H.det : ℂ) * (∏ i, conj (α i)) = _
  calc
    _ = (H.det : ℂ) * ((∏ i, α i) * (∏ i, conj (α i))) := by ring
    _ = _ := by
      rw [hprod, ← Complex.ofReal_mul]
      rfl

/-- Exact signed density with the original factorial and squared-log normalization. -/
theorem smoothDensity_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    smoothDensity (fun y => f (tropicalization y)) z =
      (n.factorial : ℝ) *
        Matrix.det ((fun j k : Fin n => tropicalHessianEntry f (tropicalization z) j k) :
        Matrix (Fin n) (Fin n) ℝ) /
        (Real.pi ^ n * ∏ i : Fin n, Complex.normSq (z i)) := by
  rw [smoothDensity, det_complexHessian_tropicalization hf hz, Complex.ofReal_re]
  ring

/-- Completed all-dimensional exterior geometry is reused; no wedge proof is repeated. -/
theorem actualTopPowerDensity_tropicalization {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    actualTopPowerDensity (smoothDDC (fun y => f (tropicalization y)) z) =
      (n.factorial : ℝ) *
        Matrix.det ((fun j k : Fin n => tropicalHessianEntry f (tropicalization z) j k) :
        Matrix (Fin n) (Fin n) ℝ) /
        (Real.pi ^ n * ∏ i : Fin n, Complex.normSq (z i)) := by
  have hs := ((contDiffOn_tropicalSmoothProfile hf) z hz).contDiffAt
    ((isOpen_complexTorus n).mem_nhds hz)
  rw [actualTopPowerDensity_smoothDDC
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  exact smoothDensity_tropicalization hf hz

/-- Actual smooth convex source input, with the original volume restricted to the true open torus. -/
theorem smoothMeasure_tropicalization_eq_withDensity {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
      (isSmoothPshOn_tropicalSmoothProfile hf hc) =
      (volume.restrict (complexTorus n)).withDensity (fun z : ComplexModel n =>
        ENNReal.ofReal ((n.factorial : ℝ) *
          Matrix.det ((fun j k : Fin n => tropicalHessianEntry f (tropicalization z) j k) :
        Matrix (Fin n) (Fin n) ℝ) /
          (Real.pi ^ n * ∏ i : Fin n, Complex.normSq (z i)))) := by
  unfold smoothMeasure
  apply withDensity_congr_ae
  apply ae_restrict_of_forall_mem (isOpen_complexTorus n).measurableSet
  intro z hz
  change ENNReal.ofReal (smoothDensity (fun y => f (tropicalization y)) z) = _
  exact congrArg ENNReal.ofReal (smoothDensity_tropicalization hf hz)

end SGPT.Toric
