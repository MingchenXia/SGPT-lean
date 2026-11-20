import SGPT.Bergman.SiuNSScalarBundle

/-! Compatible smooth local weights manufacture an actual native metric;
the global correcting function is produced by overlap invariance. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.LineBundle.TMetric
open SGPT.PSH.LineBundleMetric SGPT.PSH.GlobalL2 HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Smooth logarithms of squared frame norms with the natural overlap law. -/
structure CompatibleScalarWeights (C : ScalarLineCocycle n X) where
  weight : X → X → ℝ
  smooth : ∀ i, ChartSmoothOn (n := n) (weight i) (C.dom i)
  compatible : ∀ i j p, p ∈ C.dom i → p ∈ C.dom j →
    weight i p = Real.log (‖C.transition i j p‖ ^ 2) + weight j p

namespace CompatibleScalarWeights
variable {C : ScalarLineCocycle n X} (W : CompatibleScalarWeights C) [CompactSpace X]

/-- Local logarithmic ratio to the independent existing smooth metric. -/
def gap (i p : X) : ℝ := Real.log (‖(C.nativeFrame i).val.symm p 1‖ ^ 2) - W.weight i p

theorem gap_invariant (i j : X) {p : X} (hi : p ∈ C.dom i) (hj : p ∈ C.dom j) :
    W.gap i p = W.gap j p := by
  have hn := frameNorm_eq_mul (C.nativeFrame i) (C.nativeFrame j) ⟨hi, hj⟩
  rw [C.nativeFrame_transition i j ⟨hi, hj⟩] at hn
  have ht : ‖C.transition i j p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (C.nonzero i j p ⟨hi, hj⟩))
  have he : ‖(C.nativeFrame j).val.symm p 1‖ ^ 2 ≠ 0 :=
    (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero C.nativeBundle (C.nativeFrame j) hj))).ne'
  dsimp only [gap]
  rw [hn, mul_pow, Real.log_mul ht he, W.compatible i j p hi hj]
  ring

/-- The local ratios glue to this actual global real function. -/
def correction (p : X) : ℝ := W.gap p p

theorem correction_eq_gap (i : X) {p : X} (hp : p ∈ C.dom i) : W.correction p = W.gap i p :=
  W.gap_invariant p i (C.mem_dom p) hp

theorem gap_smooth (i : X) : ChartSmoothOn (n := n) (W.gap i) (C.dom i) := by
  intro c
  exact ((C.nativeBundle_smooth c (C.nativeFrame i)).log (fun z hz =>
    (sq_pos_of_pos (norm_pos_iff.mpr
      (sourceAtlasFrame_ne_zero C.nativeBundle (C.nativeFrame i) hz.2))).ne')).sub (W.smooth i c)

/-- The actual global correction is smooth because it agrees with one
fixed smooth local ratio on each genuine original neighborhood. -/
theorem correction_smooth : ChartSmooth (n := n) W.correction := by
  intro c z hz
  let p := c.val.symm z
  let U := c.val.target ∩ c.val.symm ⁻¹' C.dom p
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm (C.open_dom p)
  have hzU : z ∈ U := ⟨hz, C.mem_dom p⟩
  have hs : ContDiffAt ℝ ∞ (fun w => W.gap p (c.val.symm w)) z :=
    (W.gap_smooth p c).contDiffAt (hU.mem_nhds hzU)
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  exact W.correction_eq_gap p hw.2

/-- The actual native holomorphic bundle with the prescribed metric,
obtained by exponential rescaling of its independent physical norm. -/
def nativeBundle : HermitianHolomorphicLineBundle n X :=
  rescaleExp C.nativeBundle W.correction W.correction_smooth

theorem nativeBundle_smooth : IsSourceSmoothHermitianMetric W.nativeBundle :=
  rescaleExp_smooth C.nativeBundle C.nativeBundle_smooth W.correction W.correction_smooth

/-- The defining actual physical Chern coefficients are exactly the
negative dd^c of the given local log squared norms. -/
theorem nativeBundle_chern_coeff (i : X) (c : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ c.val.target) (hi : c.val.symm z ∈ C.dom i) :
    (sourceNativeFirstChernForm W.nativeBundle W.nativeBundle_smooth).val.coeff c z =
      -smoothDDC (fun w => W.weight i (c.val.symm w)) z := by
  let θ := sourceNativeFirstChernForm C.nativeBundle C.nativeBundle_smooth
  have hθ := sourceNativeFirstChernForm_isOwn C.nativeBundle C.nativeBundle_smooth
  change (sourceNativeFirstChernForm (rescaleExp C.nativeBundle W.correction W.correction_smooth)
    (rescaleExp_smooth C.nativeBundle C.nativeBundle_smooth W.correction W.correction_smooth)).val.coeff c z = _
  rw [rescaleExp_chern_coeff C.nativeBundle C.nativeBundle_smooth θ hθ
    W.correction W.correction_smooth c hz]
  let U := c.val.target ∩ c.val.symm ⁻¹' C.dom i
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm (C.open_dom i)
  have hzU : z ∈ U := ⟨hz, hi⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (‖(C.nativeFrame i).val.symm (c.val.symm w) 1‖ ^ 2)) U :=
    (C.nativeBundle_smooth c (C.nativeFrame i)).log (fun w hw =>
      (sq_pos_of_pos (norm_pos_iff.mpr
        (sourceAtlasFrame_ne_zero C.nativeBundle (C.nativeFrame i) hw.2))).ne')
  have heq : (fun w => W.correction (c.val.symm w)) =ᶠ[𝓝 z]
      fun w => Real.log (‖(C.nativeFrame i).val.symm (c.val.symm w) 1‖ ^ 2) - W.weight i (c.val.symm w) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact W.correction_eq_gap i hw.2
  have hbase := hθ c (C.nativeFrame i) z hz hi
  rw [smoothDDC_neg hU hlog hzU] at hbase
  rw [smoothDDC_congr heq,
    PositiveClasses.smoothDDC_sub hU hlog (W.smooth i c) hzU, hbase]
  abel

end CompatibleScalarWeights
end SGPT.BDivisor.NSKodaira
