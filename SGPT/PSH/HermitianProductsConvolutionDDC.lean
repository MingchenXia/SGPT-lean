import SGPT.PSH.HermitianProductsConvolution
import SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

/-!
# The actual scalar `ddc` current on the shared radial kernel tests

The current action and the scalar radial convolution are related through
their genuine second derivatives, with the source normalization unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentDensityMatrix LocalCurrentDeterminant
  TopDegreeDensity LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalCurrentL1Ddc LocalCurrentPullbackDdc
open scoped Topology Distributions ContDiff

attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- The bounded scalar current acts on an arbitrary compact test by the
literal finite second-derivative integral formula. -/
theorem ddcMul_oneCurrent_test_integral {p : ComplexModel (m + 1) → ℝ}
    (hp : IsLocallyBoundedPshOn U p) (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    ddcMul (oneCurrent U) p γ φ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      (topDensity ((wedgeLM m (isOneOne_coeffForm a b) γ : formSpan (m + 1) (m + 1)) :
        RealForm (m + 1) (2 * (m + 1))) *
        ∫ y, dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) φ) y * p y) := by
  rw [ddcMul, ← l1Current_coe_eq_mulBorel hp, ddc_apply_apply]
  have hloc : LocallyIntegrableOn (fun y => ((p y : EReal)).toReal) U volume := by
    simpa only [EReal.toReal_coe] using locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
  simp_rw [l1Current_apply hloc, EReal.toReal_coe]

/-- Two test derivatives give the symmetric real Hessian, in the same order
as the coefficient expansion of the source `ddc` operator. -/
theorem dTest_twice_apply (φ : 𝓓(U, ℝ)) (v w y : ComplexModel (m + 1)) :
    dTest w (dTest v φ) y = realHessian φ y v w := by
  have hφ : ContDiff ℝ 2 (φ : ComplexModel (m + 1) → ℝ) := φ.contDiff.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hfun : (dTest v φ : ComplexModel (m + 1) → ℝ) =
      fun x => fderiv ℝ (φ : ComplexModel (m + 1) → ℝ) x v := funext (dTest_apply v φ)
  rw [dTest_apply, hfun, fderiv_fderiv_apply_eq_realHessian hφ]
  simpa only [realHessian_eq_fderiv] using
    hφ.contDiffAt.isSymmSndFDerivAt (by norm_num) w v

/-- Translating a kernel translates its real Hessian without changing its
constant tangent arguments. -/
theorem realHessian_comp_sub_const (κ : ComplexModel (m + 1) → ℝ)
    (z y v w : ComplexModel (m + 1)) :
    realHessian (fun x => κ (x - z)) y v w = realHessian κ (y - z) v w := by
  simp only [realHessian, iteratedFDeriv_comp_sub]

/-- The actual radial test derivatives are exactly the derivatives of the
same scalar kernel used in decreasing PSH regularization. -/
theorem radialKernelTest_dTest_twice {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V)
    (v w y : ComplexModel (m + 1)) :
    dTest w (dTest v (radialKernelTest S hK hKU j z hz)) y =
      realHessian (S.kernel j) (y - z) v w := by
  rw [dTest_twice_apply]
  exact realHessian_comp_sub_const (S.kernel j) z y v w

/-- Testing the actual scalar `ddc` current against the shared radial kernel
equals the smooth `ddc` of the actual scalar radial pairing. The compact
indicator is justified by the support of the same translated kernel. -/
theorem ddcMul_radialKernel_pairing {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p)
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V)
    (γ : formSpan (m + 1) m) :
    ddcMul (oneCurrent U) p γ (radialKernelTest S hK hKU j z hz) =
      formDensity
        (smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z) γ := by
  classical
  let φ := radialKernelTest S hK hKU j z hz
  let g := K.indicator p
  have hg : LocallyIntegrable g volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1) hK hKU).locallyIntegrable
  have hκ : ContDiff ℝ 2 (S.kernel j) :=
    (S.kernel_contDiff j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hconv : ContDiff ℝ 2 (translationPairing volume g (S.kernel j)) :=
    contDiff_translationPairing hg (S.kernel_hasCompactSupport j) hκ
  change ddcMul (oneCurrent U) p γ φ =
    formDensity (smoothDDC (translationPairing volume g (S.kernel j)) z) γ
  rw [ddcMul_oneCurrent_test_integral hp, formDensity_apply, ← wedgeDensity_apply,
    smoothDDC_eq_sum hconv.contDiffAt, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul, wedgeDensity_apply]
  simp only [coe_wedgeLM_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [realHessian_translationPairing hg (S.kernel_hasCompactSupport j) hκ]
  have hsupport : tsupport
      (dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) φ)) ⊆ K :=
    ((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)).trans
      (S.translated_tsupport j z hz)
  have hint :
      (∫ y, dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) φ) y * p y) =
        ∫ y, g y * realHessian (S.kernel j) (y - z)
          (realBasis (m + 1) a) (realBasis (m + 1) b) := by
    apply integral_congr_ae
    filter_upwards [] with y
    have hd : dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) φ) y =
        realHessian (S.kernel j) (y - z)
          (realBasis (m + 1) a) (realBasis (m + 1) b) :=
      radialKernelTest_dTest_twice S hK hKU j z hz _ _ y
    rw [hd]
    by_cases hy : y ∈ K
    · simp only [g, indicator_of_mem hy]
      ring
    · have hzero : dTest (realBasis (m + 1) b)
          (dTest (realBasis (m + 1) a) φ) y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy' => hy (hsupport hy'))
      rw [← hd, hzero]
      simp only [mul_zero, zero_mul]
  rw [hint]
  ring

/-- Equality of full real one-one forms: smoothing the actual scalar current
with the shared radial tests is the `ddc` of the actual scalar radial pairing. -/
theorem testedForm_ddcMul_eq_smoothDDC {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p)
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) :
    testedForm (ddcMul (oneCurrent U) p) (radialKernelTest S hK hKU j z hz) =
      smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z := by
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact
      (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1) hK hKU).locallyIntegrable
  have hκ : ContDiff ℝ 2 (S.kernel j) :=
    (S.kernel_contDiff j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hconv : ContDiff ℝ 2
      (translationPairing volume (K.indicator p) (S.kernel j)) :=
    contDiff_translationPairing hg (S.kernel_hasCompactSupport j) hκ
  apply eq_of_forall_topDensity_eq (testedForm_isOneOne _ _)
    (smoothDDC_isOneOne hconv.contDiffAt)
  intro γ
  rw [← testedForm_pairing, ddcMul_radialKernel_pairing hp]
  rfl

/-- The smooth residual is convolved through exactly the same current tests
as the scalar PSH factor. This is an actual full one-one form, not a selected
coefficient or a promised approximation. -/
def smoothResidualConvolution {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U)
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) : RealForm (m + 1) 2 :=
  testedForm (LocalBedfordTaylorForms.wedgeForm rfl (oneCurrent U) hσ)
    (radialKernelTest S hK hKU j z hz)

/-- The full residual convolution has the literal convolution coefficient
against every complementary test form. -/
theorem smoothResidualConvolution_pairing {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ y ∈ U, σ y ∈ formSpan (m + 1) 1)
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V)
    (γ : formSpan (m + 1) m) :
    topDensity (coordinateWedge (γ : RealForm (m + 1) (2 * m))
        (smoothResidualConvolution hσ S hK hKU j z hz)) =
      ∫ y, S.kernel j (y - z) * formDensity (σ y) γ := by
  unfold smoothResidualConvolution
  rw [← testedForm_pairing, LocalBedfordTaylorSmoothDensity.wedgeForm_oneCurrent_apply
    rfl hσ hσS]
  rfl

/-- Positivity of the original full corrected current makes its shared-kernel
smooth coefficient form semipositive. The residual is convolved with exactly
the same kernels as the scalar PSH approximation. -/
theorem radial_correctedForm_isSemipositive {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p)
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U)
    (hpositive : IsPositive (ddcMul (oneCurrent U) p +
      LocalBedfordTaylorForms.wedgeForm rfl (oneCurrent U) hσ))
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) :
    IsSemipositiveOneOne
      (smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z +
        smoothResidualConvolution hσ S hK hKU j z hz) := by
  have htested := radialKernelForm_isSemipositive S hK hKU hpositive j z hz
  rw [testedForm_add, testedForm_ddcMul_eq_smoothDDC hp] at htested
  exact htested

end SGPT.PSH.HermitianProducts
