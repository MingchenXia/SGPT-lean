import SGPT.NPP.UniformMetricJetOverlap

/-!
# Manufactured uniform actual metric polynomial overlap and its actual derivatives

This is the actual metric instantiation of the compact product-ball calculus.
Blueprint: `dnt-big-uniform-metric-jet-overlap.tex`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Envelopes

variable {n : ℕ}

/-- A uniform base patch, radius and constants for the SAME actual metric-jet
overlap, its actual fibre derivative and its actual first base derivative. -/
theorem actual_metricJetOverlap_uniform_cubic_and_derivative_bounds
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hφ : ContDiffOn ℝ ∞ φ U) (hmaps : MapsTo φ U V)
    (hpos : ∀ a ∈ V, ∀ v, v ≠ 0 → 0 < g a v v)
    (hsym : ∀ a ∈ V, ∀ v t, g a v t = g a t v)
    (hlocalEquiv : ∀ a ∈ U, ∃ L : ComplexModel n ≃L[ℝ] ComplexModel n,
      fderiv ℝ φ a = L.toContinuousLinearMap)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ a ∈ closedBall z r, ∀ v ∈ closedBall (0 : ComplexModel n) r,
        ‖metricJetOverlap g φ a v‖ ≤ M * ‖v‖ ^ 3 ∧
        ‖fderiv ℝ (metricJetOverlap g φ a) v‖ ≤ M * ‖v‖ ^ 2 ∧
        ‖fderiv ℝ (fun b => metricJetOverlap g φ b v) a‖ ≤ M * ‖v‖ ^ 3 := by
  obtain ⟨A, B, hA, hzA, hAU, hB, h0B, hR⟩ :=
    exists_product_contDiffOn_metricJetOverlap hU hV hg hφ hmaps hpos hlocalEquiv hz
  let F := fun q : ComplexModel n × ComplexModel n => metricJetOverlap g φ q.1 q.2
  have hzeros : ∀ a ∈ A, F (a, 0) = 0 ∧ fiberPartial F (a, 0) = 0 ∧
      fiberPartial (fiberPartial F) (a, 0) = 0 := by
    intro a ha
    have haU := hAU ha
    obtain ⟨L, hL⟩ := hlocalEquiv a haU
    have hgφ : DifferentiableAt ℝ g (φ a) :=
      ((hg.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps haU)))
    obtain ⟨h0, h1, h2⟩ := metricJetOverlap_zero_two_jet hU
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) haU hgφ
      (hpos _ (hmaps haU)) (hsym _ (hmaps haU)) L hL
    have hFdiff : DifferentiableAt ℝ F (a, 0) :=
      ((hR.differentiableOn (by simp)).differentiableAt ((hA.prod hB).mem_nhds ⟨ha, h0B⟩))
    refine ⟨h0, ?_, ?_⟩
    · rw [← fderiv_fiber_slice hFdiff]
      exact h1
    · rw [← second_fderiv_fiber_slice hA hB hR ha h0B]
      exact h2
  have hBF := contDiffOn_basePartial (hA.prod hB) hR
  have hBzeros : ∀ a ∈ A, basePartial F (a, 0) = 0 ∧
      fiberPartial (basePartial F) (a, 0) = 0 ∧
      fiberPartial (fiberPartial (basePartial F)) (a, 0) = 0 := by
    intro a ha
    exact basePartial_zero_fiber_two_jet hA hB hR h0B
      (fun b hb => (hzeros b hb).1) (fun b hb => (hzeros b hb).2.1)
      (fun b hb => (hzeros b hb).2.2) ha
  obtain ⟨r₁, hr₁, hr₁A, hr₁B, M₁, hM₁, hbound₁⟩ :=
    exists_uniform_local_cubic_bound_of_zero_fiber_two_jet hA hB hR h0B
      (fun a ha => (hzeros a ha).1) (fun a ha => (hzeros a ha).2.1)
      (fun a ha => (hzeros a ha).2.2) hzA
  obtain ⟨r₂, hr₂, _, _, M₂, hM₂, hbound₂⟩ :=
    exists_uniform_local_cubic_bound_of_zero_fiber_two_jet hA hB hBF h0B
      (fun a ha => (hBzeros a ha).1) (fun a ha => (hBzeros a ha).2.1)
      (fun a ha => (hBzeros a ha).2.2) hzA
  let r := min r₁ r₂
  let M := max M₁ M₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hM : 0 ≤ M := hM₁.trans (le_max_left _ _)
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  refine ⟨r, hr, ((closedBall_subset_closedBall hrr₁).trans hr₁A).trans hAU,
    M, hM, fun a ha v hv => ?_⟩
  have ha₁ := closedBall_subset_closedBall hrr₁ ha
  have hv₁ := closedBall_subset_closedBall hrr₁ hv
  have ha₂ := closedBall_subset_closedBall hrr₂ ha
  have hv₂ := closedBall_subset_closedBall hrr₂ hv
  have hFdiff : DifferentiableAt ℝ F (a, v) :=
    ((hR.differentiableOn (by simp)).differentiableAt
      ((hA.prod hB).mem_nhds ⟨hr₁A ha₁, hr₁B hv₁⟩))
  refine ⟨(hbound₁ a ha₁ v hv₁).2.trans ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) _)
  · rw [fderiv_fiber_slice hFdiff]
    exact (hbound₁ a ha₁ v hv₁).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) _))
  · rw [fderiv_base_slice hFdiff]
    exact (hbound₂ a ha₂ v hv₂).2.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (norm_nonneg _) _))

end SGPT.NPP.DNTBig
