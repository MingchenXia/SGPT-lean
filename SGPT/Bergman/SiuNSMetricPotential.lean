import SGPT.LineBundle.TMetricRescale
import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Foundations.Analysis.Pending.ProductTestForms

/-! Exponential rescaling of the actual native physical metric, with its
actual original Chern coefficient formula. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.LineBundle.TMetric
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Same holomorphic bundle, with physical squared norms multiplied by exp(-f). -/
def rescaleExp (L : HermitianHolomorphicLineBundle n X) (f : X → ℝ)
    (hf : ChartSmooth (n := n) f) : HermitianHolomorphicLineBundle n X :=
  rescale L (fun x => Real.exp (-f x))
    (Real.continuous_exp.comp (ProductTestForms.ChartSmooth.continuous hf).neg)
    (fun _ => Real.exp_pos _)

/-- The actual rescaled physical metric is smooth in every native frame. -/
theorem rescaleExp_smooth (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (f : X → ℝ)
    (hf : ChartSmooth (n := n) f) : IsSourceSmoothHermitianMetric (rescaleExp L f hf) := by
  apply (isSourceSmoothHermitianMetric_rescale_iff _ _ _ _).mpr
  intro c e
  exact (((hf c).mono inter_subset_left).neg.exp).mul (hL c e)

/-- Exponential rescaling changes the actual negative log frame norm by f. -/
theorem rescaleExp_frame_log (L : HermitianHolomorphicLineBundle n X)
    (f : X → ℝ) (hf : ChartSmooth (n := n) f)
    (e : AtlasFrame (rescaleExp L f hf)) {x : X} (hx : x ∈ e.val.baseSet) :
    -Real.log (‖e.val.symm x 1‖ ^ 2) =
      -Real.log (‖(ofAtlasFrame L _ _ _ e).val.symm x 1‖ ^ 2) + f x := by
  let E := ofAtlasFrame L (fun x => Real.exp (-f x)) _ (fun _ => Real.exp_pos _) e
  have hn : ‖e.val.symm x 1‖ ^ 2 = Real.exp (-f x) * ‖E.val.symm x 1‖ ^ 2 :=
    norm_toRescale_sq L _ _ _ x (E.val.symm x 1)
  rw [hn, Real.log_mul (Real.exp_ne_zero _)
    (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L E hx))).ne', Real.log_exp]
  dsimp only [E]
  ring

/-- Native Chern forms obey the actual smooth potential formula, on every
original chart target. -/
theorem rescaleExp_chern_coeff (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) (f : X → ℝ) (hf : ChartSmooth (n := n) f)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target) :
    (sourceNativeFirstChernForm (rescaleExp L f hf) (rescaleExp_smooth L hL f hf)).val.coeff c z =
      θ.val.coeff c z + smoothDDC (fun w => f (c.val.symm w)) z := by
  let e : AtlasFrame (rescaleExp L f hf) :=
    ⟨trivializationAt ℂ (rescaleExp L f hf).Fiber (c.val.symm z), inferInstance⟩
  have he : c.val.symm z ∈ e.val.baseSet := mem_baseSet_trivializationAt _ _ _
  let E := ofAtlasFrame L (fun x => Real.exp (-f x)) _ (fun _ => Real.exp_pos _) e
  let U := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hzU : z ∈ U := ⟨hz, he⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => -Real.log (‖E.val.symm (c.val.symm w) 1‖ ^ 2)) U :=
    ((hL c E).log (fun w hw =>
      (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L E hw.2))).ne')).neg
  have heq : (fun w => -Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2)) =ᶠ[𝓝 z]
      fun w => -Real.log (‖E.val.symm (c.val.symm w) 1‖ ^ 2) + f (c.val.symm w) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact rescaleExp_frame_log L f hf e hw.2
  rw [sourceNativeFirstChernForm_isOwn _ _ c e z hz he,
    smoothDDC_congr heq, smoothDDC_add hU hlog ((hf c).mono inter_subset_left) hzU,
    ← hθ c E z hz he]

/-- A prescribed smooth background with the actual potential coefficients
is the Chern form of the manufactured native rescaled metric. -/
theorem rescale_exp_isOwnFirstChernForm (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (θ η : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) (f : X → ℝ) (hf : ChartSmooth (n := n) f)
    (hη : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      η.val.coeff c z = θ.val.coeff c z + smoothDDC (fun w => f (c.val.symm w)) z) :
    IsOwnFirstChernForm (rescaleExp L f hf) η := by
  intro c e z hz he
  rw [hη c z hz, ← rescaleExp_chern_coeff L hL θ hθ f hf c hz]
  exact sourceNativeFirstChernForm_isOwn _ _ c e z hz he

end SGPT.BDivisor.NSKodaira
