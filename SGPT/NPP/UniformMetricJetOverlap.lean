import SGPT.NPP.MetricJetActualBaseDerivative

/-!
# Uniform value and actual first base derivative of local metric-jet overlap

All constants are manufactured from actual smooth derivative bounds on an
actual compact product ball. Blueprint: `dnt-big-uniform-metric-jet-overlap.tex`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Envelopes

/-- Uniform actual cubic values and quadratic fibre derivatives from actual
zero identities, with the radius and all derivative constants produced. -/
theorem exists_uniform_local_cubic_bound_of_zero_fiber_two_jet
    {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ComplexModel n × ComplexModel n → G} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    (h0V : (0 : ComplexModel n) ∈ V)
    (hzero : ∀ z ∈ U, F (z, 0) = 0)
    (hVzero : ∀ z ∈ U, fiberPartial F (z, 0) = 0)
    (hVVzero : ∀ z ∈ U, fiberPartial (fiberPartial F) (z, 0) = 0)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧ closedBall (0 : ComplexModel n) r ⊆ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ closedBall z r,
        ∀ v ∈ closedBall (0 : ComplexModel n) r,
          ‖fiberPartial F (a, v)‖ ≤ M * ‖v‖ ^ 2 ∧ ‖F (a, v)‖ ≤ M * ‖v‖ ^ 3 := by
  have hW := hU.prod hV
  have hq : (z, (0 : ComplexModel n)) ∈ U ×ˢ V := ⟨hz, h0V⟩
  obtain ⟨d, hd, hdW⟩ := Metric.isOpen_iff.mp hW (z, 0) hq
  let r := d / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hKW : closedBall (z, (0 : ComplexModel n)) r ⊆ U ×ˢ V :=
    (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hdW
  have hprod : ∀ a ∈ closedBall z r, ∀ v ∈ closedBall (0 : ComplexModel n) r,
      (a, v) ∈ closedBall (z, (0 : ComplexModel n)) r := by
    intro a ha v hv
    rw [← closedBall_prod_same]
    exact ⟨ha, hv⟩
  have hrU : closedBall z r ⊆ U := fun a ha =>
    (hKW (hprod a ha 0 (mem_closedBall_self hr.le))).1
  have hrV : closedBall (0 : ComplexModel n) r ⊆ V := fun v hv =>
    (hKW (hprod z (mem_closedBall_self hr.le) v hv)).2
  let H := fiberPartial F
  have hH : ContDiffOn ℝ ∞ H (U ×ˢ V) := contDiffOn_fiberPartial hW hF
  have hDH : ContDiffOn ℝ ∞ (fderiv ℝ H) (U ×ˢ V) := hH.fderiv_of_isOpen hW (by simp)
  have hD2Hsmooth : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ H)) (U ×ˢ V) :=
    hDH.fderiv_of_isOpen hW (by simp)
  have hD2H : ContinuousOn (fderiv ℝ (fderiv ℝ H)) (U ×ˢ V) := hD2Hsmooth.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (z, (0 : ComplexModel n)) r).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ H)) (hD2H.mono hKW)
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hD2bound : ∀ q ∈ closedBall (z, (0 : ComplexModel n)) r,
      ‖fderiv ℝ (fderiv ℝ H) q‖ ≤ M :=
    fun q hq => (hC q hq).trans (le_max_left _ _)
  have hHbound : ∀ a ∈ closedBall z r, ∀ v ∈ closedBall (0 : ComplexModel n) r,
      ‖H (a, v)‖ ≤ M * ‖v‖ ^ 2 := by
    intro a ha v hv
    have hD0 : fderiv ℝ H (a, 0) ((a, v) - (a, 0)) = 0 := by
      have hh := congrArg (fun T => T v) (hVVzero a (hrU ha))
      simpa only [fiberPartial, ContinuousLinearMap.comp_apply, _root_.zero_apply,
        Prod.mk_sub_mk, sub_self, sub_zero, ContinuousLinearMap.inr_apply] using hh
    have HH := norm_sub_fderiv_le_of_secondDerivative_bound hW
      (hH.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (convex_closedBall (z, (0 : ComplexModel n)) r) hKW hD2bound
      (hprod a ha 0 (mem_closedBall_self hr.le)) (hprod a ha v hv)
    rw [hD0] at HH
    simpa only [show H (a, (0 : ComplexModel n)) = 0 from hVzero a (hrU ha),
      sub_zero, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, sub_zero,
      max_eq_right (norm_nonneg v)] using HH
  refine ⟨r, hr, hrU, hrV, M, hM, fun a ha v hv => ⟨hHbound a ha v hv, ?_⟩⟩
  have hseg : segment ℝ (0 : ComplexModel n) v ⊆ closedBall 0 r :=
    (convex_closedBall (0 : ComplexModel n) r).segment_subset (mem_closedBall_self hr.le) hv
  have hnorm : ∀ w ∈ segment ℝ (0 : ComplexModel n) v, ‖w‖ ≤ ‖v‖ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simp only [sub_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hder : ∀ w ∈ segment ℝ (0 : ComplexModel n) v,
      ‖fiberPartial F (a, w)‖ ≤ M * ‖v‖ ^ 2 := by
    intro w hw
    exact (hHbound a ha w (hseg hw)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hnorm w hw) 2) hM)
  have hdf : ∀ w ∈ segment ℝ (0 : ComplexModel n) v,
      HasFDerivWithinAt (fun t => F (a, t)) (fiberPartial F (a, w))
        (segment ℝ (0 : ComplexModel n) v) w := by
    intro w hw
    have hPair : (a, w) ∈ U ×ˢ V := ⟨hrU ha, hrV (hseg hw)⟩
    have hf : DifferentiableAt ℝ F (a, w) :=
      (hF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hPair)
    have Hf : HasFDerivAt (fun t => F (a, t)) (fiberPartial F (a, w)) w :=
      hf.hasFDerivAt.comp w
        ((hasFDerivAt_const (𝕜 := ℝ) a w).prodMk (hasFDerivAt_id w))
    exact Hf.hasFDerivWithinAt
  have hh := (convex_segment (0 : ComplexModel n) v).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdf hder (left_mem_segment ℝ 0 v) (right_mem_segment ℝ 0 v)
  simpa only [hzero a (hrU ha), sub_zero, ← pow_succ, mul_assoc] using hh

end SGPT.NPP.DNTBig
