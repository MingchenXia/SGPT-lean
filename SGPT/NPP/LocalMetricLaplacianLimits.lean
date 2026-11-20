import SGPT.NPP.LocalMetricLaplacian

/-!
# Genuine local smooth limits for the metric Laplacian

This implements the approximation nodes of
`blueprint/src/dnt-big-local-laplacian.tex`, written before this file. The
pointwise traces, smooth approximants, uniform convergence, test functions,
metric, and volume are the actual analytic objects. No Hessian or regularity
certificate is assigned to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent
open SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- Quantitative continuity of an actual local distributional pairing.
The functions may take arbitrary values outside the open set. -/
theorem abs_integral_sub_mul_laplacian_le_on (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f g : Y → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) (hχU : tsupport χ ⊆ U)
    {ε : ℝ} (hfg : ∀ y ∈ U, |f y - g y| ≤ ε) :
    |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) -
      ∫ y, g y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      ε * ∫ y, |laplacian w.form.val χ y| ∂(kahlerVolume w) := by
  have hfi := integrable_mul_laplacian_of_tsupport_subset w hU hf hχ hχU
  have hgi := integrable_mul_laplacian_of_tsupport_subset w hU hg hχ hχU
  have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
  rw [← integral_sub hfi hgi]
  calc
    |∫ y, (f y * laplacian w.form.val χ y - g y * laplacian w.form.val χ y)
        ∂(kahlerVolume w)|
        ≤ ∫ y, |f y * laplacian w.form.val χ y - g y * laplacian w.form.val χ y|
          ∂(kahlerVolume w) := abs_integral_le_integral_abs
    _ ≤ ∫ y, ε * |laplacian w.form.val χ y| ∂(kahlerVolume w) := by
      refine integral_mono (hfi.sub hgi).abs
        (integral_continuous (continuous_const.mul hL.abs) _) fun y => ?_
      by_cases hy : y ∈ U
      · rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hfg y hy) (abs_nonneg _)
      · have hys : y ∉ tsupport χ := fun h => hy (hχU h)
        simp only [laplacian_eq_zero_of_notMem_tsupport _ hys, mul_zero, sub_self,
          abs_zero, le_refl]
    _ = _ := integral_const_mul _ _

/-- Uniform convergence on a neighborhood, with an actual pointwise metric
trace bound on that neighborhood, gives the local distributional bound. -/
theorem abs_integral_mul_laplacian_le_of_smooth_local_limit (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {v : ℕ → Y → ℝ} {f : Y → ℝ}
    (hv : ∀ j, ChartSmooth (n := N) (v j))
    (hconv : TendstoUniformlyOn v f atTop U) {M : ℝ}
    (hM : ∀ j y, y ∈ U → |laplacian w.form.val (v j) y| ≤ M)
    {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχU : tsupport χ ⊆ U) :
    |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      M * ∫ y, χ y ∂(kahlerVolume w) := by
  have hcv : ∀ j, Continuous (v j) := fun j =>
    YauUniformEstimate.continuous_of_chartSmooth (hv j)
  have hf : ContinuousOn f U :=
    hconv.continuousOn (Frequently.of_forall fun j => (hcv j).continuousOn)
  have hcχ := YauUniformEstimate.continuous_of_chartSmooth hχ
  have hj : ∀ j, |∫ y, v j y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      M * ∫ y, χ y ∂(kahlerVolume w) := by
    intro j
    rw [integral_mul_laplacian_comm w (hv j) hχ]
    have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 (hv j)
    calc
      |∫ y, χ y * laplacian w.form.val (v j) y ∂(kahlerVolume w)|
          ≤ ∫ y, |χ y * laplacian w.form.val (v j) y| ∂(kahlerVolume w) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ y, M * χ y ∂(kahlerVolume w) := by
        refine integral_mono (integral_continuous (hcχ.mul hL).abs _)
          (integral_continuous (continuous_const.mul hcχ) _) fun y => ?_
        by_cases hy : y ∈ U
        · rw [abs_mul, abs_of_nonneg (hχ0 y), mul_comm M]
          exact mul_le_mul_of_nonneg_left (hM j y hy) (hχ0 y)
        · have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hχU h)
          simp only [hχy, zero_mul, abs_zero, mul_zero, le_refl]
      _ = _ := integral_const_mul _ _
  set I := ∫ y, |laplacian w.form.val χ y| ∂(kahlerVolume w) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set ε := δ / (I + 1) with hε
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨j, hjclose⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv ε hε0).exists
  have hdist : ∀ y ∈ U, |f y - v j y| ≤ ε := fun y hy => by
    have h := hjclose y hy
    rw [Real.dist_eq] at h
    exact h.le
  have herr := abs_integral_sub_mul_laplacian_le_on w hU hf (hcv j).continuousOn hχ hχU hdist
  have hεI : ε * I < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have htri := abs_add_le
    ((∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)) -
      ∫ y, v j y * laplacian w.form.val χ y ∂(kahlerVolume w))
    (∫ y, v j y * laplacian w.form.val χ y ∂(kahlerVolume w))
  rw [sub_add_cancel] at htri
  linarith [hj j]

/-- Actual smooth local approximations with locally uniform metric trace
bounds produce the book's bounded metric Laplacian on every compact subset.
Continuity of the limit is derived from the approximations. -/
theorem hasBoundedMetricLaplacianOn_of_local_smooth_limits (w : KahlerBackground N Y)
    {U : Set Y} (hU : IsOpen U) {f : Y → ℝ}
    (happrox : ∀ x ∈ U, ∃ V : Set Y, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ v : ℕ → Y → ℝ, (∀ j, ChartSmooth (n := N) (v j)) ∧
        TendstoUniformlyOn v f atTop V ∧ ∃ M : ℝ, 0 ≤ M ∧
          ∀ j y, y ∈ V → |laplacian w.form.val (v j) y| ≤ M) :
    HasBoundedMetricLaplacianOn w U f := by
  have hf : ContinuousOn f U := by
    intro x hx
    obtain ⟨V, hV, hxV, _, v, hv, hconv, _⟩ := happrox x hx
    have hfV : ContinuousOn f V := hconv.continuousOn (Frequently.of_forall fun j =>
      (YauUniformEstimate.continuous_of_chartSmooth (hv j)).continuousOn)
    exact ((hfV x hxV).continuousAt (hV.mem_nhds hxV)).continuousWithinAt
  apply hasBoundedMetricLaplacianOn_of_local_bounds w hU hf
  intro x hx
  obtain ⟨V, hV, hxV, hVU, v, hv, hconv, M, _, hM⟩ := happrox x hx
  exact ⟨V, hV, hxV, hVU, M, fun χ hχ hχ0 hχV =>
    abs_integral_mul_laplacian_le_of_smooth_local_limit w hV hv hconv hM hχ hχ0 hχV⟩

end SGPT.NPP.DNTBig
