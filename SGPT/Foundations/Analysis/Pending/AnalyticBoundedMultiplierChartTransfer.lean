import SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal

set_option autoImplicit false

/-! # Actual preferred-chart transport of analytic bounded multiplier inclusion -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierChartTransfer

open FirstPass FirstPass.HolomorphicIdealSheaves AnalyticBoundedMultiplierIdeal

noncomputable section

/-- The genuine existing manifold multiplier stalk supplies its actual
preferred-chart integral; the resulting bounded density transports by the
actual chart inverse identity, including all poles. -/
theorem mem_boundedMultiplierIdeal_of_preferred_chart_analytic_type
    {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {P : M → EReal} {x : M} {c p q : ℝ}
    {g : Fin N → ComplexModel n → ℂ}
    (htype : LogarithmicTypeAt (chartFunction P (complexChartAt (n := n) x)) c g
      ((complexChartAt (n := n) x).val x))
    (hp : 0 < p) (hqp : (n : ℝ) ≤ (q - p) * c)
    {h : M → ℂ} (hf : (multiplierIdeal (n := n) q P).mem x h) :
    (boundedMultiplierIdeal (n := n) (fun y => (p : EReal) * P y)).mem x h := by
  let e := complexChartAt (n := n) x
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hlocal : (boundedMultiplierIdeal (n := n)
      (fun z => (p : EReal) * chartFunction P e z)).mem (e.val x)
      (fun z => h (e.val.symm z)) :=
    mem_boundedMultiplierIdeal_of_analytic_weighted_integrable htype hp hqp hf.2
  obtain ⟨K, hK, hbound⟩ := hlocal.2
  refine ⟨hf.1, K, hK, ?_⟩
  have hcont : ContinuousAt e.val x := e.val.continuousAt hxsrc
  filter_upwards [e.val.open_source.mem_nhds hxsrc, hcont.eventually hbound] with y hys hy
  simpa only [multiplierDensity, chartFunction, e.val.left_inv hys] using hy

end

end SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierChartTransfer
