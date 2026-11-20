import SGPT.Bergman.Quant2SharpSectionBound
import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian
import SGPT.Bergman.Quant2SharpSubmean
import SGPT.Bergman.Quant2SharpDensityLimsup
import SGPT.Bergman.SourcePartialBergmanDensity
import SGPT.Bergman.SourcePartialBergmanTrace
import Mathlib.Order.Filter.ENNReal

/-!
# Quant2SharpSpectral

Spectral normal form of the curvature, Gaussian normalization and the pointwise sharp upper bound of normalized Bergman kernels.

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SGPT/Bergman/KodairaTransport/SourcePhysicalCurvatureWedge.lean`.
section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open Bundle Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original smooth metric manufactures actual smooth logarithms on the
actual frame domain, with no supplied curvature or Hessian hypothesis. -/
theorem sourcePhysicalChartWeight_smooth
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L) :
    ContDiffOn ℝ ∞ (sourcePhysicalChartWeight L v c e)
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let := e.property
  have hlog := (hL c e).log (fun z hz =>
    (sq_pos_of_pos (frameNorm_pos L.Fiber e.val hz.2)).ne')
  exact hlog.sub ((hv c).mono (fun _ hz => hz.1))

/-- Exact Chern/obstacle identity in the SAME original chart and frame.
The Chern form is manufactured from the original physical metric internally. -/
theorem sourcePhysicalCurvature_eq_negDDC
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target)
    (he : c.val.symm a ∈ e.val.baseSet) :
    (sourceNativeFirstChernForm L hL).val.coeff c a +
      smoothDDC (fun z => v (c.val.symm z)) a =
      smoothDDC (fun z => -sourcePhysicalChartWeight L v c e z) a := by
  let := e.property
  let U := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hlog : ContDiffOn ℝ ∞
      (fun z => Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)) U :=
    (hL c e).log (fun z hz => (sq_pos_of_pos (frameNorm_pos L.Fiber e.val hz.2)).ne')
  have hvU : ContDiffOn ℝ ∞ (fun z => v (c.val.symm z)) U :=
    (hv c).mono (fun _ hz => hz.1)
  have hfun : (fun z => -sourcePhysicalChartWeight L v c e z) =
      (fun z => -Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2) + v (c.val.symm z)) := by
    funext z
    simp only [sourcePhysicalChartWeight, neg_sub]
    ring
  have hadd : smoothDDC (fun z => -sourcePhysicalChartWeight L v c e z) a =
      smoothDDC (fun z => -Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)) a +
        smoothDDC (fun z => v (c.val.symm z)) a := by
    rw [hfun, smoothDDC_add hU hlog.neg hvU ⟨ha, he⟩]
  have hown := sourceNativeFirstChernForm_isOwn L hL
  have hchern := hown c e a ha he
  exact (congrArg (fun B : CoordinateRealTwoForm n =>
    B + smoothDDC (fun z => v (c.val.symm z)) a) hchern).trans hadd.symm

/-- The actual quadratic normal form is exactly the existing actual Levi
form. This exposes the sign and normalization used by the Gaussian. -/
theorem hermitianHessianQuadratic_eq_leviForm
    (p : ComplexModel n → ℝ) (a z : ComplexModel n) :
    hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) z = leviForm p a z := by
  simp only [hermitianHessianQuadratic, leviForm, realHessian_eq_fderiv]

/-- Actual directional curvature from the SAME physical Taylor Hessian;
no sign, nonzero vector, or positive dimension premise is added. -/
theorem sourcePhysicalCurvature_complexDiagonal
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target)
    (he : c.val.symm a ∈ e.val.baseSet) (z : ComplexModel n) :
    ((sourceNativeFirstChernForm L hL).val.coeff c a +
      smoothDDC (fun w => v (c.val.symm w)) a) ![z, Complex.I • z] =
      -hermitianHessianQuadratic
        (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a) z / Real.pi := by
  have hU : IsOpen (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hp : ContDiffAt ℝ 2 (sourcePhysicalChartWeight L v c e) a :=
    ((sourcePhysicalChartWeight_smooth L hL v hv c e).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (hU.mem_nhds ⟨ha, he⟩)
  rw [sourcePhysicalCurvature_eq_negDDC L hL v hv c e ha he,
    smoothDDC_complexDiagonal_eq_leviForm hp.neg]
  change leviForm (-sourcePhysicalChartWeight L v c e) a z / Real.pi = _
  rw [leviForm_neg, hermitianHessianQuadratic_eq_leviForm]

/-- Genuine all-dimensional top exterior power of the SAME original physical
curvature, with its computed π/factorial normalization and no positivity flag. -/
theorem sourcePhysicalCurvature_actualTopPowerDensity
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target)
    (he : c.val.symm a ∈ e.val.baseSet) :
    actualTopPowerDensity ((sourceNativeFirstChernForm L hL).val.coeff c a +
      smoothDDC (fun w => v (c.val.symm w)) a) =
      (n.factorial : ℝ) / Real.pi ^ n *
        (complexHessian (fun z => -sourcePhysicalChartWeight L v c e z) a).det.re := by
  have hU : IsOpen (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hp : ContDiffAt ℝ 2 (fun z => -sourcePhysicalChartWeight L v c e z) a :=
    (((sourcePhysicalChartWeight_smooth L hL v hv c e).neg).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (hU.mem_nhds ⟨ha, he⟩)
  rw [sourcePhysicalCurvature_eq_negDDC L hL v hv c e ha he,
    actualTopPowerDensity_smoothDDC hp]
  rfl

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/runtime/prerequisite-original-sources/SourceActualSpectralGaussian.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere Matrix
open scoped BigOperators Matrix ComplexConjugate

variable {n : ℕ}

/-- Actual real eigenvalues of the actual normalized physical two-form. -/
def sourceCurvatureEigenvalues (A : CoordinateRealTwoForm n) (hA : IsOneOne A) : Fin n → ℝ :=
  (normalizedHermitianMatrix_isHermitian A hA).eigenvalues

/-- The genuine complex-linear diagonalizing map produced from that SAME form.
Conjugation of the eigenvector matrix implements the source's first-slot convention. -/
def sourceCurvatureDiagonalizer (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    ComplexModel n →ₗ[ℂ] ComplexModel n :=
  (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm
      ((normalizedHermitianMatrix_isHermitian A hA).eigenvectorUnitary.val.map (starRingEnd ℂ))

/-- The actual pulled-back curvature has the manufactured real spectral diagonal. -/
theorem sourceCurvatureDiagonalizer_diagonal (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    normalizedHermitianMatrix (compLinearMap A (sourceCurvatureDiagonalizer A hA)) =
      Matrix.diagonal (fun j => (sourceCurvatureEigenvalues A hA j : ℂ)) := by
  let hH := normalizedHermitianMatrix_isHermitian A hA
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.val
  have hSM : standardMatrix (sourceCurvatureDiagonalizer A hA) = U.map (starRingEnd ℂ) := by
    rw [standardMatrix, sourceCurvatureDiagonalizer, LinearEquiv.apply_symm_apply]
  have htrans : (U.map (starRingEnd ℂ))ᵀ = star U := by ext j k; simp
  have hmapmap : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by ext j k; simp
  rw [normalizedHermitianMatrix_compLinearMap hA, hSM, htrans, hmapmap]
  have h := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  exact h

/-- The exact real change-of-variables factor is one; it is proved from the
actual unitary diagonalizer, never passed as a Jacobian certificate. -/
theorem sourceCurvatureDiagonalizer_normSq_det (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    Complex.normSq (LinearMap.det (sourceCurvatureDiagonalizer A hA)) = 1 := by
  let hH := normalizedHermitianMatrix_isHermitian A hA
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.val
  have hSM : standardMatrix (sourceCurvatureDiagonalizer A hA) = U.map (starRingEnd ℂ) := by
    rw [standardMatrix, sourceCurvatureDiagonalizer, LinearEquiv.apply_symm_apply]
  have h1 : (star U) * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have h2 : (starRingEnd ℂ) (Matrix.det U) * Matrix.det U = 1 := by
    have h := congrArg Matrix.det h1
    rwa [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
      Matrix.det_conjTranspose, Complex.star_def] at h
  have hU : Complex.normSq (Matrix.det U) = 1 := by
    have h3 : ((Complex.normSq (Matrix.det U) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3
  have hconj : (U.map (starRingEnd ℂ)).det = (starRingEnd ℂ) U.det :=
    (RingHom.map_det (starRingEnd ℂ) U).symm
  rw [← det_standardMatrix, hSM, hconj, Complex.normSq_conj, hU]

/-- The spectral product is the density of the actual genuine top exterior
power, including dimension zero and signed indefinite curvature. -/
theorem sourceCurvature_actualTopPowerDensity_eq_eigenvalues
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    actualTopPowerDensity A = (n.factorial : ℝ) / Real.pi ^ n *
      ∏ j, sourceCurvatureEigenvalues A hA j := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity A hA,
    normalizedTopPowerDensity, complexTopCoefficient_eq,
    (normalizedHermitianMatrix_isHermitian A hA).det_eq_prod_eigenvalues]
  have hprod : (∏ j, (sourceCurvatureEigenvalues A hA j : ℂ)) =
      ((∏ j, sourceCurvatureEigenvalues A hA j : ℝ) : ℂ) := by push_cast; rfl
  change ((((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) *
      (∏ j, (sourceCurvatureEigenvalues A hA j : ℂ))).re = _
  rw [hprod, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Exact same-eigenvalue Gaussian/wedge normalization on the strictly
positive locus. Positivity is a spectral sign condition, not a Gaussian output. -/
theorem sourceCurvature_gaussian_actualTopPowerDensity
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (hpos : ∀ j, 0 < sourceCurvatureEigenvalues A hA j) :
    actualTopPowerDensity A = (n.factorial : ℝ) /
      (∫ z : Fin n → ℂ, sourceDiagonalGaussian (sourceCurvatureEigenvalues A hA) z) := by
  rw [sourceCurvature_actualTopPowerDensity_eq_eigenvalues A hA,
    sourceDiagonalGaussian_integral hpos, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod : (∏ j, sourceCurvatureEigenvalues A hA j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => (hpos j).ne')
  field_simp [hprod, Real.pi_ne_zero]

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/runtime/prerequisite-original-sources/SourceActualSpectralExponent.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere Matrix
open scoped BigOperators Matrix ComplexConjugate

variable {n : ℕ}

/-- The actual diagonal coefficient matrix yields the actual two-form's
quadratic expression. The physical consumer manufactures the diagonal internally. -/
theorem sourceActualDiagonalForm_quadratic
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) (d : Fin n → ℝ)
    (hdiag : normalizedHermitianMatrix A = Matrix.diagonal (fun j => (d j : ℂ)))
    (z : ComplexModel n) :
    Real.pi * A ![z, Complex.I • z] = ∑ j, d j * ‖z j‖ ^ 2 := by
  have hz : (∑ j, z j • coordinateVector j : ComplexModel n) = z := by
    ext k
    rw [show ((∑ j, z j • coordinateVector j : ComplexModel n)).ofLp k =
      ∑ j, (z j • coordinateVector j : ComplexModel n).ofLp k by simp]
    rw [Finset.sum_eq_single k]
    · simp [coordinateVector]
    · intro j _ hj
      simp [coordinateVector, Ne.symm hj]
    · simp
  have hkey (j k : Fin n) :
      (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k) =
        if j = k then (d j : ℂ) else 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k) hdiag
    simpa only [normalizedHermitianMatrix_apply', Matrix.diagonal_apply] using h
  have hinner (j : Fin n) :
      (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) z =
        conj (z j) * (d j : ℂ) := by
    have hexp := hermitianEntry_sum_right Finset.univ (fun k => z k)
      coordinateVector (coordinateVector j) (A := A)
    rw [hz] at hexp
    rw [hexp, Finset.mul_sum]
    calc
      (∑ k, (Real.pi : ℂ) *
          (conj (z k) * hermitianEntry A (coordinateVector j) (coordinateVector k))) =
          ∑ k, conj (z k) *
            ((Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = conj (z j) * (d j : ℂ) := by simp_rw [hkey]; simp
  have hleft : hermitianEntry A z z =
      ∑ j, z j * hermitianEntry A (coordinateVector j) z := by
    simpa only [hz] using
      (hermitianEntry_sum_left hA Finset.univ (fun j => z j) coordinateVector z)
  have hQ : (Real.pi : ℂ) * hermitianEntry A z z =
      ∑ j, (d j : ℂ) * (‖z j‖ ^ 2 : ℝ) := by
    rw [hleft, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (Real.pi : ℂ) * (z j * hermitianEntry A (coordinateVector j) z) =
          z j * ((Real.pi : ℂ) * hermitianEntry A (coordinateVector j) z) := by ring
      _ = z j * (conj (z j) * (d j : ℂ)) := by rw [hinner]
      _ = (d j : ℂ) * (‖z j‖ ^ 2 : ℝ) := by
        rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        ring
  have hreal := congrArg Complex.re hQ
  simp [hermitianEntry, Complex.mul_re] at hreal
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hreal

/-- The actual internally produced spectral coordinate map diagonalizes the
actual original exponent, with all eigenvalue signs retained. -/
theorem sourceCurvatureDiagonalizer_quadratic
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) (z : ComplexModel n) :
    Real.pi * A ![sourceCurvatureDiagonalizer A hA z,
      Complex.I • sourceCurvatureDiagonalizer A hA z] =
      ∑ j, sourceCurvatureEigenvalues A hA j * ‖z j‖ ^ 2 := by
  have h := sourceActualDiagonalForm_quadratic
    (compLinearMap A (sourceCurvatureDiagonalizer A hA))
    (isOneOne_compLinearMap hA (sourceCurvatureDiagonalizer A hA))
    (sourceCurvatureEigenvalues A hA) (sourceCurvatureDiagonalizer_diagonal A hA) z
  simpa only [compLinearMap_apply, map_smul] using h

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SGPT/Bergman/KodairaTransport/SourcePhysicalGaussianNormalization.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open Bundle Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff BigOperators

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual physical Chern curvature plus the original smooth obstacle.
This is the very same form whose top wedge is the source sharp density. -/
def sourcePhysicalCurvature (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (c : ComplexChart n X) (a : ComplexModel n) : CoordinateRealTwoForm n :=
  (sourceNativeFirstChernForm L hL).val.coeff c a +
    smoothDDC (fun z => v (c.val.symm z)) a

/-- The original smooth metric and obstacle manufacture the actual type
(1,1) identity; the caller never supplies a spectral or curvature certificate. -/
theorem sourcePhysicalCurvature_isOneOne (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target) (he : c.val.symm a ∈ e.val.baseSet) :
    IsOneOne (sourcePhysicalCurvature L hL v c a) := by
  have hU : IsOpen (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hp : ContDiffAt ℝ 2 (fun z => -sourcePhysicalChartWeight L v c e z) a :=
    (((sourcePhysicalChartWeight_smooth L hL v hv c e).neg).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (hU.mem_nhds ⟨ha, he⟩)
  dsimp only [sourcePhysicalCurvature]
  rw [sourcePhysicalCurvature_eq_negDDC L hL v hv c e ha he]
  exact smoothDDC_isOneOne hp

/-- The same original physical data produce actual diagonal coordinates,
their true Jacobian, and the SAME-eigenvalue Gaussian/wedge identity. Every
spectral object is an output, including all zero-dimensional endpoints. -/
theorem sourcePhysicalCurvature_exists_spectral_gaussian
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target) (he : c.val.symm a ∈ e.val.baseSet) :
    ∃ (d : Fin n → ℝ) (S : ComplexModel n →ₗ[ℂ] ComplexModel n),
      Complex.normSq (LinearMap.det S) = 1 ∧
      normalizedHermitianMatrix (compLinearMap (sourcePhysicalCurvature L hL v c a) S) =
        Matrix.diagonal (fun j => (d j : ℂ)) ∧
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
        (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j ∧
      ((∀ j, 0 < d j) →
        Integrable (sourceDiagonalGaussian d) ∧
        actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
          (n.factorial : ℝ) / (∫ z : Fin n → ℂ, sourceDiagonalGaussian d z)) := by
  let A := sourcePhysicalCurvature L hL v c a
  have hA : IsOneOne A := sourcePhysicalCurvature_isOneOne L hL v hv c e ha he
  refine ⟨sourceCurvatureEigenvalues A hA, sourceCurvatureDiagonalizer A hA,
    sourceCurvatureDiagonalizer_normSq_det A hA, sourceCurvatureDiagonalizer_diagonal A hA,
    sourceCurvature_actualTopPowerDensity_eq_eigenvalues A hA, ?_⟩
  intro hpos
  exact ⟨sourceDiagonalGaussian_integrable hpos,
    sourceCurvature_gaussian_actualTopPowerDensity A hA hpos⟩

/-- Exact same-section Taylor quadratic after the internally produced actual
spectral coordinate change. No exponent-matching output is a caller premise. -/
theorem sourcePhysicalHessian_exists_spectral_gaussian
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    (hv : ChartSmooth (n := n) v) (c : ComplexChart n X) (e : AtlasFrame L)
    {a : ComplexModel n} (ha : a ∈ c.val.target) (he : c.val.symm a ∈ e.val.baseSet) :
    ∃ (d : Fin n → ℝ) (S : ComplexModel n →ₗ[ℂ] ComplexModel n),
      Complex.normSq (LinearMap.det S) = 1 ∧
      (∀ z : ComplexModel n, hermitianHessianQuadratic
        (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a) (S z) =
          -∑ j, d j * ‖z j‖ ^ 2) ∧
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
        (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j := by
  let A := sourcePhysicalCurvature L hL v c a
  have hA : IsOneOne A := sourcePhysicalCurvature_isOneOne L hL v hv c e ha he
  let S := sourceCurvatureDiagonalizer A hA
  refine ⟨sourceCurvatureEigenvalues A hA, S,
    sourceCurvatureDiagonalizer_normSq_det A hA, ?_,
    sourceCurvature_actualTopPowerDensity_eq_eigenvalues A hA⟩
  intro z
  have hQ := sourceCurvatureDiagonalizer_quadratic A hA z
  have hphysical := sourcePhysicalCurvature_complexDiagonal L hL v hv c e ha he (S z)
  change A ![S z, Complex.I • S z] = _ at hphysical
  change Real.pi * A ![S z, Complex.I • S z] = _ at hQ
  rw [hphysical] at hQ
  have hpi := Real.pi_ne_zero
  field_simp at hQ
  linarith

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalSpectralUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Bergman.NativeHermitianMetric
/-- Original physical data produce every spectral object and the exact
curvature normalization; no spectral identity is a caller hypothesis. -/
theorem sourceSharp_original_Bergman_actual_spectral_upper
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (φ : X → EReal) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ (ρ : ComplexModel n → ℝ) (d : Fin n → ℝ)
      (S : ComplexModel n →ₗ[ℂ] ComplexModel n), ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
      Complex.normSq (LinearMap.det S) = 1 ∧
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
        (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j ∧
      ((∀ j, 0 < d j) → limsup (fun k : ℕ => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop ≤
        (ENNReal.ofReal (ρ a * ∏ j, Real.pi / d j))⁻¹) ∧
      ((∃ j, d j ≤ 0) → limsup (fun k : ℕ => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop = 0) := by
  intro c a
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have hat : a ∈ c.val.target := c.val.map_source hx
  have hea : c.val.symm a ∈ e.val.baseSet := by
    simpa only [a, c.val.left_inv hx] using he
  obtain ⟨d,S,hS,hQ,hwedge⟩ := sourcePhysicalHessian_exists_spectral_gaussian L hL v hv c e hat hea
  obtain ⟨ρ,hρsm,hmap,hρ,hupper⟩ := sourceSharp_original_Bergman_signed_limsup L T hL hT v hv μ hμ x e f he hf φ
  exact ⟨ρ,d,S,hρsm,hmap,hρ,hS,hwedge,hupper S d hS hQ⟩
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpBergmanNormalization.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Filter
open SGPT.Bergman.SingularWeightedHilbert
open scoped Topology BigOperators ENNReal
/-- Exact original n!/k^n normalization, including the harmless totalized
k=0 coefficient, is retained before taking the kernel upper limsup. -/
theorem sourceSharp_original_normalization_limsup (n : ℕ) (B : ℕ → ℝ≥0∞) :
    limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k * B k) atTop =
      ENNReal.ofReal (n.factorial : ℝ) *
        limsup (fun (k : ℕ) => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) * B k) atTop := by
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1
  funext k
  rw [sourceBergmanNormalization, div_eq_mul_inv,
    ENNReal.ofReal_mul (Nat.cast_nonneg n.factorial)]
  exact mul_assoc _ _ _

/-- Exact positive-spectrum Gaussian normalization against the SAME chart
volume density; this is the book's n! pi^-n curvature density ratio. -/
theorem sourceSharp_positive_normalization_identity {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ j, 0 < d j) {ρ A : ℝ} (hρ : 0 < ρ)
    (hA : A = (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j) :
    ENNReal.ofReal (n.factorial : ℝ) *
      (ENNReal.ofReal (ρ * ∏ j, Real.pi / d j))⁻¹ = ENNReal.ofReal (A / ρ) := by
  have hdprod : 0 < ∏ j, d j := Finset.prod_pos (fun j _ => hd j)
  have hprod : (∏ j, Real.pi / d j) = Real.pi ^ n / ∏ j, d j := by
    rw [Finset.prod_div_distrib]
    simp
  have hmass : 0 < ρ * ∏ j, Real.pi / d j :=
    mul_pos hρ (Finset.prod_pos (fun j _ => div_pos Real.pi_pos (hd j)))
  rw [← ENNReal.ofReal_inv_of_pos hmass,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n.factorial)]
  congr 1
  rw [hprod, hA]
  field_simp [ne_of_gt hρ, ne_of_gt hdprod, Real.pi_ne_zero]
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalBetaUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Bergman.NativeHermitianMetric
/-- Actual original beta density, with its exact n!/k^n normalization and
the SAME native measure, has the physical curvature upper bound. The zero
and negative spectral branch is retained separately, without global
positivity, projectivity, or a maximizing section. -/
theorem sourceSharp_original_beta_curvature_upper
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (φ : X → EReal) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ (ρ : ComplexModel n → ℝ) (d : Fin n → ℝ)
      (S : ComplexModel n →ₗ[ℂ] ComplexModel n), ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
      Complex.normSq (LinearMap.det S) = 1 ∧
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
        (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j ∧
      limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k * sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop ≤
        ENNReal.ofReal (actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) / ρ a) ∧
      ((∃ j, d j ≤ 0) → limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k * sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop = 0) := by
  intro c a
  obtain ⟨ρ,d,S,hρsm,hmap,hρ,hS,hwedge,hupper⟩ :=
    sourceSharp_original_Bergman_actual_spectral_upper L T hL hT v hv μ hμ x e f he hf φ
  refine ⟨ρ,d,S,hρsm,hmap,hρ,hS,hwedge,?_,?_⟩
  · rw [sourceSharp_original_normalization_limsup]
    by_cases hd : ∀ j, 0 < d j
    · calc
        _ ≤ ENNReal.ofReal (n.factorial : ℝ) *
            (ENNReal.ofReal (ρ a * ∏ j, Real.pi / d j))⁻¹ := mul_le_mul_right (hupper.1 hd) _
        _ = _ := sourceSharp_positive_normalization_identity d hd hρ hwedge
    · have hbad : ∃ j, d j ≤ 0 := by simpa only [not_forall, not_lt] using hd
      rw [hupper.2 hbad, mul_zero]
      exact zero_le
  · intro hbad
    rw [sourceSharp_original_normalization_limsup, hupper.2 hbad, mul_zero]
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalPointwiseUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Bergman.NativeHermitianMetric
/-- The pointwise sharp upper is manufactured from original smooth bundle,
obstacle and measure data alone. Actual atlas frames, spectral objects,
chart measure identity and both signed branches are outputs. -/
theorem sourceSharp_original_beta_pointwise_upper
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (φ : X → EReal) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ (ρ : ComplexModel n → ℝ) (d : Fin n → ℝ)
      (S : ComplexModel n →ₗ[ℂ] ComplexModel n), ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
      Complex.normSq (LinearMap.det S) = 1 ∧
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) =
        (n.factorial : ℝ) / Real.pi ^ n * ∏ j, d j ∧
      limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k * sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop ≤
        ENNReal.ofReal (actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) / ρ a) ∧
      ((∃ j, d j ≤ 0) → limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k * sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop = 0) := by
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
  exact sourceSharp_original_beta_curvature_upper L T hL hT v hv μ hμ x e f he hf φ
end SGPT.Bergman.SharpLocalUpper
end
end
