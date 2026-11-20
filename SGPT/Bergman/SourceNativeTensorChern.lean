import SGPT.Bergman.SourceNativeTensorSmoothMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff TensorProduct

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual native physical tensor Chern coefficients are the sum of actual
original coefficients, using the produced smooth metrics on literal
original tensor fibers. No tensor curvature identity is an input. -/
theorem sourceNativeTensor_chern_coeff (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target) :
    (sourceNativeFirstChernForm (tensor L T) (sourceNativeTensor_smooth L T hL hT)).val.coeff c z =
      (sourceNativeFirstChernForm L hL).val.coeff c z +
        (sourceNativeFirstChernForm T hT).val.coeff c z := by
  let p := c.val.symm z
  let E : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
  let F : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber p, inferInstance⟩
  have hpE : p ∈ E.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber p
  have hpF : p ∈ F.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber p
  let S := c.val.target ∩ c.val.symm ⁻¹' (E.val.baseSet ∩ F.val.baseSet)
  have hS : IsOpen S := c.val.isOpen_inter_preimage_symm
    (E.val.open_baseSet.inter F.val.open_baseSet)
  have hzS : z ∈ S := ⟨hz, hpE, hpF⟩
  have hTensor := sourceNativeFirstChernForm_isOwn (tensor L T)
    (sourceNativeTensor_smooth L T hL hT) c (tensorAtlasFrame E F) z hz ⟨hpE, hpF⟩
  have hLeft := sourceNativeFirstChernForm_isOwn L hL c E z hz hpE
  have hRight := sourceNativeFirstChernForm_isOwn T hT c F z hz hpF
  have hEL : ContDiffOn ℝ ∞ (fun w => -Real.log (‖E.val.symm (c.val.symm w) 1‖ ^ 2)) S :=
    (((hL c E).mono (fun _ hw => ⟨hw.1, hw.2.1⟩)).log
      (fun w hw => (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L E hw.2.1))).ne')).neg
  have hFT : ContDiffOn ℝ ∞ (fun w => -Real.log (‖F.val.symm (c.val.symm w) 1‖ ^ 2)) S :=
    (((hT c F).mono (fun _ hw => ⟨hw.1, hw.2.2⟩)).log
      (fun w hw => (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero T F hw.2.2))).ne')).neg
  have heq : (fun w => -Real.log (‖(tensorAtlasFrame E F).val.symm (c.val.symm w) 1‖ ^ 2))
      =ᶠ[𝓝 z] fun w => -Real.log (‖E.val.symm (c.val.symm w) 1‖ ^ 2) +
        -Real.log (‖F.val.symm (c.val.symm w) 1‖ ^ 2) := by
    filter_upwards [hS.mem_nhds hzS] with w hw
    rw [tensorAtlasFrame_norm_one E F hw.2, mul_pow,
      Real.log_mul
        (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L E hw.2.1))).ne'
        (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero T F hw.2.2))).ne']
    ring
  exact hTensor.trans (((smoothDDC_congr heq).trans (smoothDDC_add hS hEL hFT hzS)).trans
    (congrArg₂ (· + ·) hLeft.symm hRight.symm))

/-- The genuine native scalar unit has zero actual Chern coefficient in
every original chart, including dimension zero. -/
theorem sourceNativeUnit_chern_coeff (c : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ c.val.target) :
    (sourceNativeFirstChernForm unit sourceNativeUnit_smooth).val.coeff c z = 0 := by
  have h := sourceNativeFirstChernForm_isOwn unit sourceNativeUnit_smooth c unitAtlasFrame z hz
    (show c.val.symm z ∈ (unitAtlasFrame (n := n) (M := X)).val.baseSet from mem_univ _)
  refine h.trans ?_
  change smoothDDC (fun w => -Real.log
    (‖(Bundle.Trivial.trivialization X ℂ).symm (c.val.symm w) 1‖ ^ 2)) z = 0
  simp only [Bundle.Trivial.trivialization_symm_apply, norm_one, one_pow, Real.log_one, neg_zero]
  exact GlobalPotentialTransforms.smoothDDC_const 0 z

end SGPT.Bergman.NativeHermitianMetric
