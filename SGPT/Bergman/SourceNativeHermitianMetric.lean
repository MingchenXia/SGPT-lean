import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.PSH.BookLineBundleMetrics
import SGPT.Foundations.Analysis.Pending.BlanchardWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.PSH SGPT.PSH.LineBundleMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual original physical inner product, as the book's Hermitian
form. No auxiliary fiber metric, trivialization or positivity certificate. -/
def sourceFiberHermitianForm (L : HermitianHolomorphicLineBundle n X) (x : X) :
    HermitianForm (L.Fiber x) where
  toSesq := innerₛₗ ℂ
  pos' v hv := by
    refine ⟨‖v‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr hv), ?_⟩
    simpa only [innerₛₗ_apply_apply, Complex.ofReal_pow] using!
      (inner_self_eq_norm_sq_to_K v)

/-- Exact same physical quadratic form, for EVERY actual fiber vector. -/
theorem sourceFiberHermitianForm_normSq (L : HermitianHolomorphicLineBundle n X)
    (x : X) (v : L.Fiber x) : (sourceFiberHermitianForm L x).normSq v = ‖v‖ ^ 2 := by
  change (inner ℂ v v).re = ‖v‖ ^ 2
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

/-- Frame smoothness on the actual original bundle manufactures the book
HermitianMetric condition for EVERY local holomorphic section, retaining
the original physical fiber Hermitian forms exactly. -/
def sourceNativeHermitianMetric (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) : HermitianMetric (n := n) L.Fiber where
  form := sourceFiberHermitianForm L
  smooth := by
    intro s U hU hs c z hz
    let p := c.val.symm z
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
    let W := U ∩ e.val.baseSet
    have hW : IsOpen W := hU.inter e.val.open_baseSet
    have hp : p ∈ W := ⟨hz.2, mem_baseSet_trivializationAt ℂ L.Fiber p⟩
    let S := c.val.target ∩ c.val.symm ⁻¹' W
    have hS : IsOpen S := c.val.isOpen_inter_preimage_symm hW
    have hzS : z ∈ S := ⟨hz.1, hp⟩
    let g : X → ℂ := fun x => (e.val (TotalSpace.mk' ℂ x (s x))).2
    have hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g W :=
      (e.val.mdifferentiableOn_section_iff (IB := 𝓘(ℂ, ComplexModel n))
        (s := s) hW inter_subset_right).mp (hs.mono inter_subset_left)
    have hnorm : ContDiffAt ℝ ∞ (fun w => Complex.normSq (g (c.val.symm w))) z := by
      apply SGPT.Foundations.Analysis.Pending.BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [hS.mem_nhds hzS] with w hw
      exact differentiableAt_comp_chart_symm c hw.1
        ((hg _ hw.2).mdifferentiableAt (hW.mem_nhds hw.2))
    have hframe : ContDiffAt ℝ ∞ (fun w => ‖e.val.symm (c.val.symm w) 1‖ ^ 2) z :=
      (hL c e).contDiffAt
        ((c.val.isOpen_inter_preimage_symm e.val.open_baseSet).mem_nhds ⟨hz.1, hp.2⟩)
    have heq : (fun w => (sourceFiberHermitianForm L (c.val.symm w)).normSq
        (s (c.val.symm w))) =ᶠ[𝓝 z]
        fun w => Complex.normSq (g (c.val.symm w)) *
          ‖e.val.symm (c.val.symm w) 1‖ ^ 2 := by
      filter_upwards [hS.mem_nhds hzS] with w hw
      rw [sourceFiberHermitianForm_normSq,
        eq_coeff_smul_frame (L := L.Fiber) p s hw.2.2, norm_smul, mul_pow,
        Complex.normSq_eq_norm_sq]
      rfl
    exact ((hnorm.mul hframe).congr_of_eventuallyEq heq).contDiffWithinAt

/-- The produced whole book metric has the literal original squared norm,
including zero vectors, with no metric-comparison hypothesis. -/
theorem sourceNativeHermitianMetric_normSq (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (x : X) (v : L.Fiber x) :
    ((sourceNativeHermitianMetric L hL).form x).normSq v = ‖v‖ ^ 2 :=
  sourceFiberHermitianForm_normSq L x v

end SGPT.Bergman.NativeHermitianMetric
