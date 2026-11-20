import SGPT.NPP.SourceEnvelopeMinimumAdmissibility
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Actual quadratic remainder of actual native chart transitions

Complete blueprint: `blueprint/src/dnt-big-chart-transition-remainder.tex`,
written first. The actual second Fréchet derivative bound is manufactured
from actual chart smoothness and compactness, then integrated twice by the
mean value theorem. No envelope regularity or smoothing bound is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

/-- Vector-valued quadratic Taylor remainder, using the actual Fréchet
second derivative and two actual mean value inequalities. -/
theorem norm_sub_fderiv_le_of_secondDerivative_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {Ω : Set E} (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 2 F Ω)
    {S : Set E} (hS : Convex ℝ S) (hSΩ : S ⊆ Ω) {M : ℝ}
    (hM : ∀ w ∈ S, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ M)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  have hd1 : ∀ w ∈ Ω, HasFDerivAt F (fderiv ℝ F w) w := fun w hw =>
    ((hF.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hw)).hasFDerivAt
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) Ω := hF.fderiv_of_isOpen hΩ (by norm_num)
  have hd2 : ∀ w ∈ Ω, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) w) w :=
    fun w hw => ((hDF.differentiableOn (by norm_num)).differentiableAt
      (hΩ.mem_nhds hw)).hasFDerivAt
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans (hM x hx)
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hbound : ∀ w ∈ segment ℝ x y,
      ‖fderiv ℝ F w - fderiv ℝ F x‖ ≤ M * ‖y - x‖ := by
    intro w hw
    have hdist : ‖w - x‖ ≤ ‖y - x‖ := by
      rw [segment_eq_image'] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hMv : ∀ v ∈ segment ℝ x y, ‖fderiv ℝ (fderiv ℝ F) v‖ ≤ M :=
      fun v hv => hM v (hseg hv)
    have hh := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun v hv => (hd2 v (hSΩ (hseg hv))).hasFDerivWithinAt) hMv
      (left_mem_segment ℝ x y) hw
    exact hh.trans (mul_le_mul_of_nonneg_left hdist hM0)
  let g : E → G := fun w => F w - fderiv ℝ F x w
  have hg : ∀ w ∈ Ω, HasFDerivAt g (fderiv ℝ F w - fderiv ℝ F x) w :=
    fun w hw => (hd1 w hw).sub (fderiv ℝ F x).hasFDerivAt
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hg w (hSΩ (hseg hw))).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : g y - g x = F y - F x - fderiv ℝ F x (y - x) := by
    simp only [g, map_sub]
    abel
  rw [heq] at hh
  convert hh using 1
  ring

/-- Actual C² regularity manufactures the local second-derivative constant,
with no assumed numerical Hessian or remainder output. -/
theorem exists_local_quadratic_remainder_of_contDiffOn
    {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ComplexModel n → G} {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ 2 F Ω) {z : ComplexModel n} (hz : z ∈ Ω) :
    ∃ R : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R,
        ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  obtain ⟨d, hd, hdΩ⟩ := Metric.isOpen_iff.mp hΩ z hz
  let R : ℝ := d / 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hKΩ : closedBall z R ⊆ Ω :=
    (closedBall_subset_ball (by dsimp only [R]; linarith)).trans hdΩ
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) Ω := hF.fderiv_of_isOpen hΩ (by norm_num)
  have hD2F : ContinuousOn (fderiv ℝ (fderiv ℝ F)) Ω :=
    hDF.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_closedBall z R).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ F)) (hD2F.mono hKΩ)
  let M : ℝ := max B 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ w ∈ closedBall z R, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ M :=
    fun w hw => (hB w hw).trans (le_max_left _ _)
  exact ⟨R, hR, hKΩ, M, hM0, fun x hx y hy =>
    norm_sub_fderiv_le_of_secondDerivative_bound hΩ hF (convex_closedBall z R) hKΩ hM hx hy⟩

/-- The literal actual holomorphic coordinate transition has its actual
uniform quadratic remainder on a manufactured valid overlap ball. -/
theorem actual_chartTransition_locally_quadratic_remainder
    {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (e d : ComplexChart n Y)
    {z : ComplexModel n} (hz : z ∈ coordinateDomain (id : Y → Y) e d) :
    ∃ R : ℝ, 0 < R ∧ closedBall z R ⊆ coordinateDomain (id : Y → Y) e d ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R,
        ‖coordinateMap (id : Y → Y) e d y - coordinateMap (id : Y → Y) e d x -
          fderiv ℝ (coordinateMap (id : Y → Y) e d) x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  have hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : Y → Y) :=
    contMDiff_id
  exact exists_local_quadratic_remainder_of_contDiffOn (coordinateDomain_isOpen hid e d)
    ((coordinateMap_contDiffOn_real hid e d).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz

end SGPT.NPP.DNTBig
