import SGPT.PSH.GlobalQPSH
import SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- Genuine rational germs give the original connected, uniformly bounded
presentation inside the actual original open domain, including dimension zero. -/
theorem connectedRationalPresentation_iff_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    {u : E → EReal} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    HasAnalyticSingularityTypeAt u x ↔
      ∃ (c : ℚ) (N : ℕ) (f : Fin N → E → ℂ) (b : E → ℝ) (C : ℝ) (V : Set E),
        0 < c ∧ 0 ≤ C ∧ IsOpen V ∧ IsConnected V ∧ x ∈ V ∧ V ⊆ U ∧
        (∀ j, DifferentiableOn ℂ (f j) V) ∧ (∀ y ∈ V, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) V := by
  constructor
  · rintro ⟨c, N, f, hc, ⟨H, hH, hxH, hf⟩, b, ⟨C, hC, hb⟩, heq⟩
    have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
    obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp (hb.and heq)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ((hU.inter hH).inter hW)
      x ⟨⟨hx, hxH⟩, hxW⟩
    refine ⟨c, N, f, b, C, ball x r, hcQ, hC, isOpen_ball,
      isConnected_ball hr, mem_ball_self hr, fun y hy => (hball hy).1.1,
      fun j => (hf j).mono (fun y hy => (hball hy).1.2),
      fun y hy => (hWsub (hball hy).2).1, ?_⟩
    exact fun y hy => (hWsub (hball hy).2).2
  · rintro ⟨c, N, f, b, C, V, hc, hC, hV, _, hxV, _, hf, hb, heq⟩
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    exact ⟨c, N, f, hcR, ⟨V, hV, hxV, hf⟩, b,
      ⟨C, hC, eventually_of_mem (hV.mem_nhds hxV) hb⟩,
      eventually_of_mem (hV.mem_nhds hxV) (fun y hy => heq hy)⟩

namespace VariableComplexAtlas
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual original coordinate representatives with positive rational
bounded-remainder analytic type; this predicate asserts no QPSH closure. -/
def HasRationalAnalyticChartType (A : VariableComplexAtlas X) (u : X → EReal) : Prop :=
  ∀ i, ∀ z ∈ (A.chart i).target, HasAnalyticSingularityTypeAt (A.coordinate u i) z

/-- Reuse the actual main rational scaling producer at every original point. -/
theorem HasRationalAnalyticChartType.pos_rat_smul {u : X → EReal}
    (hu : A.HasRationalAnalyticChartType u) {r : ℚ} (hr : 0 < r) :
    A.HasRationalAnalyticChartType (fun x => ((r : ℝ) : EReal) * u x) := by
  intro i z hz
  exact Pending.QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
    (hu i z hz) hr

/-- The actual parent manufactures the common coefficient and product family;
the original functions and chart coordinates are unchanged. -/
theorem HasRationalAnalyticChartType.add {u w : X → EReal}
    (hu : A.HasRationalAnalyticChartType u) (hw : A.HasRationalAnalyticChartType w) :
    A.HasRationalAnalyticChartType (fun x => u x + w x) := by
  intro i z hz
  exact Pending.RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add
    (hu i z hz) (hw i z hz)

/-- The genuine rational maximum parent retains every actual pole branch. -/
theorem HasRationalAnalyticChartType.max {u w : X → EReal}
    (hu : A.HasRationalAnalyticChartType u) (hw : A.HasRationalAnalyticChartType w) :
    A.HasRationalAnalyticChartType (fun x => max (u x) (w x)) := by
  intro i z hz
  exact Pending.RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max
    (hu i z hz) (hw i z hz)

/-- Original universal testing and genuine dd-bar existence manufacture
finite points in every original neighborhood without an incoming witness. -/
theorem IsQPSH.locallyNondegenerate {u : X → EReal} (hu : A.IsQPSH u) :
    LocallyNondegenerate u := by
  obtain ⟨θ, hθ⟩ := hu
  intro x O hO hxO
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
  have hpsh := hθ.2 U g hg
  obtain ⟨y, hy, hfin⟩ := hpsh.locallyNondegenerate hg.1 x hxU O hO hxO
  exact ⟨y, hy.2, (EReal.add_ne_bot_iff.mp hfin).1⟩

/-- The source connected presentation and proper common zero locus are
produced in every original chart from genuine original QPSH and analytic type. -/
theorem IsQPSH.exists_connected_analytic_presentation {u : X → EReal}
    (hu : A.IsQPSH u) (han : A.HasRationalAnalyticChartType u)
    (i : A.Index) {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    ∃ (c : ℚ) (N : ℕ) (f : Fin N → ComplexModel (A.dimension i) → ℂ)
      (b : ComplexModel (A.dimension i) → ℝ) (C : ℝ)
      (V : Set (ComplexModel (A.dimension i))),
      0 < c ∧ 0 ≤ C ∧ IsOpen V ∧ IsConnected V ∧ z ∈ V ∧ V ⊆ (A.chart i).target ∧
      (∀ j, DifferentiableOn ℂ (f j) V) ∧ (∀ y ∈ V, |b y| ≤ C) ∧
      EqOn (A.coordinate u i)
        (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) V ∧
      ∃ y ∈ V, ∃ j, f j y ≠ 0 := by
  classical
  obtain ⟨c, N, f, b, C, V, hc, hC, hV, hconn, hzV, hVe, hf, hb, heq⟩ :=
    (connectedRationalPresentation_iff_germ (A.chart i).open_target hz).mp (han i z hz)
  obtain ⟨y, hy, hfin⟩ :=
    SGPT.PSH.LocallyNondegenerate.exists_coordinate_ne_bot
      hu.locallyNondegenerate (A.chart i) hV hVe hzV
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnonzero : ∃ j, f j y ≠ 0 := by
    by_contra h
    have hzero : ∀ j, f j y = 0 := by simpa only [not_exists, not_not] using h
    have hbot := (scaled_generatorLog_add_eq_bot_iff f y hcR (b y)).mpr hzero
    exact hfin ((heq hy).trans hbot)
  exact ⟨c, N, f, b, C, V, hc, hC, hV, hconn, hzV, hVe, hf, hb, heq, y, hy, hnonzero⟩

end VariableComplexAtlas
end SGPT.PSH
