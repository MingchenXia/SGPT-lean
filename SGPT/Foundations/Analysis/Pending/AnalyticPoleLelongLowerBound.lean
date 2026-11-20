import SGPT.Foundations.Analysis.Pending.QuasiEquisingularKahlerCurrent
import SGPT.Foundations.Analysis.Pending.AnalyticSingularityPoleLelong
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleAppend

set_option autoImplicit false

/-! # Quantitative analytic-pole Lelong lower bounds -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticPoleLelongLowerBound

open FirstPass FirstPass.NonKahlerLocus QuasiEquisingularKahlerCurrent
  LelongNumberChartTransport

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A genuine local holomorphic presentation at a pole gives its actual
coefficient as a quantitative preferred-chart Lelong lower bound. -/
theorem ofReal_two_mul_le_lelongNumber_of_local_presentation
    {u : M → EReal} {c : ℝ} (hc : 0 < c) {N : ℕ} {g : Fin N → M → ℂ}
    {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    (hg : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U)
    {b : M → ℝ} (hb : BoundedRealGermAt b x)
    (hrep : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog g y + (b y : EReal))
    (hx : u x = ⊥) : ENNReal.ofReal (2 * c) ≤ lelongNumber (n := n) u x := by
  let e := complexChartAt (n := n) x
  let z := e.val x
  let G : Fin N → ComplexModel n → ℂ := fun i w => g i (e.val.symm w)
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hgx : ∀ i, g i x = 0 :=
    (scaled_generatorLog_add_eq_bot_iff g x hc (b x)).mp
      (hrep.eq_of_nhds.symm.trans hx)
  have hgenG : HolomorphicGeneratorsAt G z := by
    refine ⟨e.val.target ∩ e.val.symm ⁻¹' U,
      e.val.isOpen_inter_preimage_symm hU, ?_, ?_⟩
    · refine ⟨e.val.map_source hxsrc, ?_⟩
      change e.val.symm (e.val x) ∈ U
      rw [e.val.left_inv hxsrc]
      exact hxU
    · intro i w hw
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hw.1
        ((hg i).mdifferentiableAt (hU.mem_nhds hw.2))).differentiableWithinAt
  have hGz : ∀ i, G i z = 0 := by
    intro i
    simpa only [G, z, e.val.left_inv hxsrc] using hgx i
  obtain ⟨C, hC⟩ := exists_generatorLog_le hgenG hGz
  obtain ⟨Cb, _, hCb⟩ := hb
  have hcont : ContinuousAt e.val x := e.val.continuousAt hxsrc
  have hlog : ∀ᶠ y in 𝓝 x,
      generatorLog g y ≤ ((2 * Real.log ‖e.val y - z‖ + C : ℝ) : EReal) := by
    filter_upwards [hcont.eventually hC, e.val.open_source.mem_nhds hxsrc] with y hy hys
    simpa only [generatorLog, generatorVector, G, e.val.left_inv hys] using hy
  apply ofReal_le_lelongNumber (show 0 ≤ 2 * c by positivity)
    (C := c * C + Cb)
  refine eventually_nhdsWithin_of_eventually_nhds ?_
  filter_upwards [hlog, hCb, hrep] with y h1 h2 h3
  rw [h3]
  by_cases hbot : generatorLog g y = ⊥
  · rw [hbot, EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
    exact bot_le
  have hga : generatorLog g y = (((generatorLog g y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (generatorLog_ne_top g y) hbot).symm
  rw [hga] at h1 ⊢
  rw [EReal.coe_le_coe_iff] at h1
  rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  change c * (generatorLog g y).toReal + b y ≤
    2 * c * Real.log ‖e.val y - z‖ + (c * C + Cb)
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le, (abs_le.mp h2).2]

/-- A bounded logarithmic germ in any actual holomorphic chart gives the
quantitative coefficient bound for the actual preferred-chart Lelong number. -/
theorem ofReal_two_mul_le_lelongNumber_of_logarithmicTypeAt
    {u : M → EReal} (e : ComplexChart n M) {x : M} (hxs : x ∈ e.val.source)
    {c : ℝ} {N : ℕ} {f : Fin N → ComplexModel n → ℂ}
    (hlog : LogarithmicTypeAt (chartFunction u e) c f (e.val x))
    (hx : u x = ⊥) : ENNReal.ofReal (2 * c) ≤ lelongNumber (n := n) u x := by
  obtain ⟨hc, ⟨U, hU, hxU, hf⟩, b, hb, heq⟩ := hlog
  let S : Set M := e.val.source ∩ e.val ⁻¹' U
  have hS : IsOpen S := e.val.isOpen_inter_preimage hU
  have hxS : x ∈ S := ⟨hxs, hxU⟩
  have hcont : ContinuousAt e.val x := e.val.continuousAt hxs
  apply ofReal_two_mul_le_lelongNumber_of_local_presentation
    hc hS hxS (g := fun i y => f i (e.val y)) (b := fun y => b (e.val y))
  · intro i y hy
    have hfi : DifferentiableAt ℂ (f i) (e.val y) :=
      (hf i).differentiableAt (hU.mem_nhds hy.2)
    exact (hfi.mdifferentiableAt.comp y
      (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property
        hy.1)).mdifferentiableWithinAt
  · exact hb.comp_continuousAt hcont
  · filter_upwards [hcont.eventually heq, e.val.open_source.mem_nhds hxs] with y hy hys
    simpa only [chartFunction, e.val.left_inv hys, generatorLog, generatorVector] using hy
  · exact hx

/-- The same positive coefficient in an actual logarithmic germ supplies
one genuine neighborhood bound for every pole there. -/
theorem eventually_ofReal_two_mul_le_lelongNumber_at_poles
    {u : M → EReal} (e : ComplexChart n M) {x : M} (hxs : x ∈ e.val.source)
    {c : ℝ} {N : ℕ} {f : Fin N → ComplexModel n → ℂ}
    (hlog : LogarithmicTypeAt (chartFunction u e) c f (e.val x)) :
    ∀ᶠ y in 𝓝 x, u y = ⊥ →
      ENNReal.ofReal (2 * c) ≤ lelongNumber (n := n) u y := by
  have hcont : ContinuousAt e.val x := e.val.continuousAt hxs
  have hnear := RegularizedMaxOffPoleAppend.LogarithmicTypeAt.eventually hlog
  filter_upwards [hcont.eventually hnear, e.val.open_source.mem_nhds hxs] with y hy hys
  exact ofReal_two_mul_le_lelongNumber_of_logarithmicTypeAt e hys hy

end

end SGPT.Foundations.Analysis.Pending.AnalyticPoleLelongLowerBound
