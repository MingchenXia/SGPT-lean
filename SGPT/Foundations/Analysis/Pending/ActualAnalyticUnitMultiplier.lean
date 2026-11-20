import SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound
import SGPT.Foundations.Analysis.Pending.IEquivalentMax
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

set_option autoImplicit false

/-! # Actual analytic finite points supply unit multiplier germs -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticUnitMultiplier

open FirstPass FirstPass.HolomorphicIdealSheaves AnalyticSingularityLocalBound

noncomputable section

/-- Analytic type supplies a true lower bound off the poles; its actual chart-ball
weighted mass then produces the unit germ at every positive multiplier level. -/
theorem one_mem_multiplierIdeal_of_analytic_nonpole
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u) {x : M}
    (htype : HasAnalyticSingularityTypeAt
      (chartFunction u (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x)) (hx : u x ≠ ⊥)
    {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := n) c u).mem x (fun _ => (1 : ℂ)) := by
  let e := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hxT : e.val x ∈ e.val.target := e.val.map_source hxs
  have hxchart : chartFunction u e (e.val x) ≠ ⊥ := by
    simpa only [chartFunction, e.val.left_inv hxs] using hx
  obtain ⟨a, b, hbound⟩ :=
    AnalyticSingularityLocalBound.HasAnalyticSingularityTypeAt.eventually_bounded htype hxchart
  have hnbhd : ∀ᶠ z in 𝓝 (e.val x), z ∈ e.val.target ∧
      (a : EReal) ≤ chartFunction u e z := by
    filter_upwards [e.val.open_target.mem_nhds hxT, hbound] with z hz hb
    exact ⟨hz, hb.1⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hBT : ball (e.val x) R ⊆ e.val.target := fun _ hz => (hball hz).1
  refine ⟨holomorphicAt_const (n := n) (M := M) 1, hc,
    ball (e.val x) R, isOpen_ball, mem_ball_self hR, differentiableOn_const (1 : ℂ), ?_, ?_⟩
  · exact IEquivalentMax.aemeasurable_multiplierDensity_restrict isOpen_ball
      ((hu e).mono hBT) hc.ne' continuousOn_const
  · have hpoint : ∀ z ∈ ball (e.val x) R,
        multiplierDensity (chartFunction u e) c (fun _ => (1 : ℂ)) z ≤
          ENNReal.ofReal (Real.exp (-(c * a))) := by
      intro z hz
      simp only [multiplierDensity, norm_one, one_pow, ENNReal.ofReal_one, one_mul]
      rw [← multiplierWeight_coe]
      exact multiplierWeight_antitone hc.le (hball hz).2
    calc
      _ ≤ ∫⁻ z in ball (e.val x) R, ENNReal.ofReal (Real.exp (-(c * a))) :=
        setLIntegral_mono_ae' measurableSet_ball (Eventually.of_forall hpoint)
      _ = ENNReal.ofReal (Real.exp (-(c * a))) * volume (ball (e.val x) R) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

end

end SGPT.Foundations.Analysis.Pending.ActualAnalyticUnitMultiplier
