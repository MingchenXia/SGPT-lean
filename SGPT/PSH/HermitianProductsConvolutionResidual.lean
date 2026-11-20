import SGPT.PSH.HermitianProductsConvolutionDDC

/-!
# The literal smooth residual convolution

Dual-basis current smoothing of a smooth real one-one form is its actual
Bochner convolution against the shared radial kernels. This identifies the
error term in the positivity proof for bounded Hermitian products.
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
  LocalBedfordTaylorForms LocalBedfordTaylorLocality LocalCurrentPullbackDdc
  LocalBedfordTaylorSmoothDensity
open scoped Topology Distributions ContDiff

attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- Every real one-one form is reconstructed from its actual complementary
wedge densities against the dual basis. -/
theorem form_eq_sum_dualForm_density {α : RealForm (m + 1) 2} (hα : IsOneOne α) :
    α = ∑ i, formDensity α (formBasis (m + 1) m i) • dualForm m i := by
  classical
  apply eq_of_forall_topDensity_eq hα
    (isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _)
  intro γ
  have hs : topDensity (coordinateWedge (γ : RealForm (m + 1) (2 * m))
      (∑ i, formDensity α (formBasis (m + 1) m i) • dualForm m i)) =
      ∑ i, formDensity α (formBasis (m + 1) m i) * (formBasis (m + 1) m).repr γ i := by
    rw [← wedgeDensity_apply, map_sum]
    simp only [map_smul, smul_eq_mul, wedgeDensity_apply, topDensity_dualForm]
  rw [hs]
  change formDensity α γ = _
  conv_lhs => rw [← (formBasis (m + 1) m).sum_repr γ, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem integrable_density_test
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    Integrable (fun y => φ y * formDensity (σ y) γ) := by
  have := ProductTestForms.realForm_finiteDimensional (n := m + 1) 2
  let L : RealForm (m + 1) 2 →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (wedgeDensity (γ : RealForm (m + 1) (2 * m)))
  have hL : ContDiffOn ℝ ∞ (fun y => formDensity (σ y) γ) U :=
    L.contDiff.comp_contDiffOn hσ
  exact (smoothMulTest U.isOpen hL φ φ.tsupport_subset).continuous.integrable_of_hasCompactSupport
    (smoothMulTest U.isOpen hL φ φ.tsupport_subset).hasCompactSupport

private theorem test_smul_eq_sum
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ11 : ∀ y ∈ U, IsOneOne (σ y)) (φ : 𝓓(U, ℝ)) (y : ComplexModel (m + 1)) :
    φ y • σ y = ∑ i, (φ y * formDensity (σ y) (formBasis (m + 1) m i)) • dualForm m i := by
  by_cases hy : y ∈ U
  · conv_lhs => rw [form_eq_sum_dualForm_density (hσ11 y hy)]
    simp only [Finset.smul_sum, smul_smul]
  · simp only [testFunction_eq_zero_of_notMem φ hy, zero_smul, zero_mul,
      Finset.sum_const_zero]

/-- Compact scalar tests times smooth one-one forms are genuinely Bochner
integrable; their values outside the original open domain do not matter. -/
theorem integrable_test_smul_smoothForm
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y)) (φ : 𝓓(U, ℝ)) :
    Integrable (fun y => φ y • σ y) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_density_test hσ (formBasis (m + 1) m i) φ).smul_const (dualForm m i))
  exact hi.congr (Eventually.of_forall fun y => (test_smul_eq_sum hσ11 φ y).symm)

/-- The actual smooth-current test reconstruction is the literal integral
of the full smooth one-one form against the scalar test. -/
theorem testedForm_smoothCurrent_eq_integral
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y)) (φ : 𝓓(U, ℝ)) :
    testedForm (wedgeForm rfl (oneCurrent U) hσ) φ = ∫ y, φ y • σ y := by
  classical
  unfold testedForm
  simp_rw [wedgeForm_oneCurrent_apply rfl hσ
    (fun y hy => oneOne_mem_formSpan (hσ11 y hy))]
  change (∑ i, (∫ y, φ y * formDensity (σ y) (formBasis (m + 1) m i)) • dualForm m i) = _
  simp_rw [test_smul_eq_sum hσ11 φ]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_density_test hσ (formBasis (m + 1) m i) φ).smul_const (dualForm m i))]
  exact Finset.sum_congr rfl fun i _ => (integral_smul_const
    (fun y => φ y * formDensity (σ y) (formBasis (m + 1) m i)) (dualForm m i)).symm

/-- The residual in the shared-kernel positivity formula is exactly the
Bochner convolution of the original smooth residual form. -/
theorem smoothResidualConvolution_eq_integral {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y))
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) :
    smoothResidualConvolution hσ S hK hKU j z hz =
      ∫ y, S.kernel j (y - z) • σ y :=
  testedForm_smoothCurrent_eq_integral hσ hσ11 (radialKernelTest S hK hKU j z hz)

/-- A modulus of continuity of the original residual on the kernel support
gives the exact same norm bound for its actual convolution error. -/
theorem smoothResidualConvolution_norm_sub_le {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y))
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) {ε : ℝ}
    (hbound : ∀ y, S.kernel j (y - z) ≠ 0 → ‖σ y - σ z‖ ≤ ε) :
    ‖smoothResidualConvolution hσ S hK hKU j z hz - σ z‖ ≤ ε := by
  let φ := radialKernelTest S hK hKU j z hz
  have hφ : Integrable (fun y => φ y) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hφpos (y) : 0 ≤ φ y := S.kernel_nonneg j (y - z)
  have hunit : (∫ y, φ y) = 1 := by
    change (∫ y, S.kernel j (y - z)) = 1
    rw [integral_sub_right_eq_self, S.kernel_integral_one]
  have hI : Integrable (fun y => φ y • σ y) :=
    integrable_test_smul_smoothForm hσ hσ11 φ
  have hI₀ : Integrable (fun y => φ y • σ z) := hφ.smul_const (σ z)
  have hdiff : Integrable (fun y => φ y • (σ y - σ z)) := by
    exact (hI.sub hI₀).congr (Eventually.of_forall fun y => (smul_sub (φ y) (σ y) (σ z)).symm)
  have hmean : (∫ y, φ y • σ y) - σ z = ∫ y, φ y • (σ y - σ z) := by
    simp_rw [smul_sub]
    rw [integral_sub hI hI₀, integral_smul_const, hunit, one_smul]
  rw [smoothResidualConvolution_eq_integral hσ hσ11]
  change ‖(∫ y, φ y • σ y) - σ z‖ ≤ ε
  rw [hmean]
  calc
    ‖∫ y, φ y • (σ y - σ z)‖ ≤ ∫ y, ‖φ y • (σ y - σ z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, φ y * ε := by
      apply integral_mono_ae hdiff.norm (hφ.mul_const ε)
      filter_upwards [] with y
      by_cases hy : φ y = 0
      · simp only [hy, zero_smul, norm_zero, zero_mul, le_refl]
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφpos y)]
        exact mul_le_mul_of_nonneg_left (hbound y hy) (hφpos y)
    _ = ε := by rw [integral_mul_const, hunit, one_mul]

/-- Smooth residual convolution converges uniformly on the common buffered
inner domain. The actual kernel support shrinks inside the original compact
buffer; no chosen approximating residual is assumed. -/
theorem smoothResidualConvolution_uniform_error {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y))
    (S : RadialConvolutionSystem V K p R) (hR : 0 < R)
    (hK : IsCompact K) (hKU : K ⊆ U) (hVK : (V : Set (ComplexModel (m + 1))) ⊆ K) :
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ z (hz : z ∈ V),
      ‖smoothResidualConvolution hσ S hK hKU j z hz - σ z‖ ≤ ε := by
  have hUC : UniformContinuousOn σ K :=
    hK.uniformContinuousOn_of_continuous (hσ.continuousOn.mono hKU)
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  have hrad := tendsto_shrinkingBump_rOut (E := ComplexModel (m + 1)) R hR
  change Tendsto (fun j : ℕ => R / ((j : ℝ) + 1)) atTop (𝓝 0) at hrad
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hrad).2 δ hδ)
  refine ⟨N, fun j hj z hz => smoothResidualConvolution_norm_sub_le
    hσ hσ11 S hK hKU j z hz (fun y hy => ?_)⟩
  have hyK : y ∈ K := S.translated_tsupport j z hz
    (subset_tsupport (fun x => S.kernel j (x - z)) hy)
  have hdist : dist y z ≤ R / ((j : ℝ) + 1) := by
    have ht := S.kernel_tsupport j (subset_tsupport (S.kernel j) hy)
    simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using ht
  have hm := hmod y hyK z (hVK hz) (hdist.trans_lt (hN j hj))
  simpa only [dist_eq_norm] using hm.le

private theorem semipositive_norm_error {α β : RealForm (m + 1) 2}
    (hα : IsOneOne α) (hβ : IsOneOne β) {ε : ℝ} (hbound : ‖α - β‖ ≤ ε) :
    IsSemipositiveOneOne (β - α + ε • kahlerForm (m + 1)) := by
  have hbase := (isSemipositiveOneOne_norm_smul_kahlerForm (isOneOne_sub hα hβ)).1
  have hextra := (isSemipositiveOneOne_kahlerForm (n := m + 1)).smul
    (sub_nonneg.mpr hbound)
  have hsum := hbase.add hextra
  have heq : (‖α - β‖ • kahlerForm (m + 1) - (α - β)) +
      (ε - ‖α - β‖) • kahlerForm (m + 1) = β - α + ε • kahlerForm (m + 1) := by
    module
  rw [heq] at hsum
  exact hsum

/-- Actual positivity of the original corrected current and a norm bound for
the genuine residual convolution produce a semipositive smooth form after
adding the explicit Euclidean error term. -/
theorem radial_correctedForm_epsilon_isSemipositive {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p)
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U)
    (hpositive : IsPositive (ddcMul (oneCurrent U) p + wedgeForm rfl (oneCurrent U) hσ))
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V)
    (hσz : IsOneOne (σ z)) {ε : ℝ}
    (hbound : ‖smoothResidualConvolution hσ S hK hKU j z hz - σ z‖ ≤ ε) :
    IsSemipositiveOneOne
      (smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z +
        σ z + ε • kahlerForm (m + 1)) := by
  have hconv11 : IsOneOne (smoothResidualConvolution hσ S hK hKU j z hz) :=
    testedForm_isOneOne _ _
  have hsum := (radial_correctedForm_isSemipositive hp hσ hpositive S hK hKU j z hz).add
    (semipositive_norm_error hconv11 hσz hbound)
  have heq :
      (smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z +
        smoothResidualConvolution hσ S hK hKU j z hz) +
      (σ z - smoothResidualConvolution hσ S hK hKU j z hz + ε • kahlerForm (m + 1)) =
      smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z +
        σ z + ε • kahlerForm (m + 1) := by abel_nf
  rw [heq] at hsum
  exact hsum

/-- For every fixed positive Euclidean error, the SAME radial approximants
of a bounded corrected PSH factor have semipositive actual smooth Hermitian
forms on the whole buffered inner domain from one common index onward. -/
theorem radial_correctedForm_eventually_semipositive
    {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {p : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p)
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ y ∈ U, IsOneOne (σ y))
    (hpositive : IsPositive (ddcMul (oneCurrent U) p + wedgeForm rfl (oneCurrent U) hσ))
    (S : RadialConvolutionSystem V K p R) (hR : 0 < R)
    (hK : IsCompact K) (hKU : K ⊆ U) (hVK : (V : Set (ComplexModel (m + 1))) ⊆ K) :
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ z ∈ V,
      IsSemipositiveOneOne
        (smoothDDC (translationPairing volume (K.indicator p) (S.kernel j)) z +
          σ z + ε • kahlerForm (m + 1)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := smoothResidualConvolution_uniform_error hσ hσ11 S hR hK hKU hVK ε hε
  exact ⟨N, fun j hj z hz => radial_correctedForm_epsilon_isSemipositive
    hp hσ hpositive S hK hKU j z hz (hσ11 z (hKU (hVK hz))) (hN j hj z hz)⟩

end SGPT.PSH.HermitianProducts
