import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false

/-! # Actual compact chart balls and actual uniform background positivity cover -/

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.XiaoPositiveCompactChartCover

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual strict background positivity persists quantitatively on an actual compact chart ball. -/
theorem exists_closedBall_lower_bound (w : KahlerBackground n M) (e : ComplexChart n M)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ closedBall z₀ r ⊆ e.val.target ∧
      ∀ z ∈ closedBall z₀ r, ∀ v : ComplexModel n,
        c * ‖v‖ ^ 2 ≤ w.form.val.coeff e z ![v, Complex.I • v] := by
  obtain ⟨m, hm, hmle⟩ :=
    KahlerDomination.exists_lineValue_lower_bound (w.isKahler.1 e z₀ hz₀).2
  have htgt : e.val.target ∈ 𝓝 z₀ := e.val.open_target.mem_nhds hz₀
  have hωc : ContinuousAt (w.form.val.coeff e) z₀ :=
    ((w.form.val.smooth e).continuousOn).continuousAt htgt
  have hdrift : ∀ᶠ z in 𝓝 z₀, ‖w.form.val.coeff e z - w.form.val.coeff e z₀‖ < m / 2 := by
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hωc (m / 2) (half_pos hm)
  obtain ⟨R, hR, hRB⟩ := Metric.mem_nhds_iff.mp (inter_mem htgt hdrift)
  have hsmall : ∀ z ∈ closedBall z₀ (R / 2),
      z ∈ e.val.target ∧ ‖w.form.val.coeff e z - w.form.val.coeff e z₀‖ < m / 2 := by
    intro z hz
    apply hRB
    exact (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (half_lt_self hR)))
  refine ⟨R / 2, m / 2, half_pos hR, half_pos hm,
    fun z hz => (hsmall z hz).1, fun z hz v => ?_⟩
  have hdiff := (hsmall z hz).2
  have hsplit : w.form.val.coeff e z ![v, Complex.I • v] =
      w.form.val.coeff e z₀ ![v, Complex.I • v] +
        (w.form.val.coeff e z - w.form.val.coeff e z₀) ![v, Complex.I • v] := by simp
  have hneg := neg_le_of_abs_le
    (KahlerDomination.abs_lineValue_le (w.form.val.coeff e z - w.form.val.coeff e z₀) v)
  have hcenter := hmle v
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hdiff.le (sq_nonneg ‖v‖)]

/-- An actual compact chart ball with an actual uniform positive background lower bound. -/
structure PositiveChartPatch (w : KahlerBackground n M) where
  chart : ComplexChart n M
  basePoint : M
  mem_source : basePoint ∈ chart.val.source
  radius : ℝ
  radius_pos : 0 < radius
  target_closedBall : closedBall (chart.val basePoint) radius ⊆ chart.val.target
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  lowerBound : ∀ z ∈ closedBall (chart.val basePoint) radius, ∀ v : ComplexModel n,
    lowerConstant * ‖v‖ ^ 2 ≤ w.form.val.coeff chart z ![v, Complex.I • v]

namespace PositiveChartPatch

variable {w : KahlerBackground n M}

/-- The actual compact coordinate set of the actual positivity patch. -/
def compactSet (p : PositiveChartPatch w) : Set (ComplexModel n) :=
  closedBall (p.chart.val p.basePoint) p.radius

/-- The actual open-ball chart source neighborhood of the actual positivity patch. -/
def sourceNeighborhood (p : PositiveChartPatch w) : Set M :=
  p.chart.val.source ∩ p.chart.val ⁻¹' ball (p.chart.val p.basePoint) p.radius

/-- The coordinate ball is genuinely compact in the actual finite complex model. -/
theorem isCompact_compactSet (p : PositiveChartPatch w) : IsCompact p.compactSet :=
  isCompact_closedBall _ _

/-- The actual source neighborhood genuinely contains a neighborhood of the actual base point. -/
theorem sourceNeighborhood_mem_nhds (p : PositiveChartPatch w) :
    p.sourceNeighborhood ∈ 𝓝 p.basePoint := by
  refine inter_mem (p.chart.val.open_source.mem_nhds p.mem_source) ?_
  exact p.chart.val.continuousAt p.mem_source (ball_mem_nhds _ p.radius_pos)

end PositiveChartPatch

/-- Every actual point has an actual compact positivity patch produced from its actual preferred chart. -/
theorem exists_patch_at (w : KahlerBackground n M) (x : M) :
    ∃ p : PositiveChartPatch w, p.basePoint = x := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨r, c, hr, hc, htarget, hbound⟩ :=
    exists_closedBall_lower_bound w e (e.val.map_source hx)
  exact ⟨⟨e, x, hx, r, hr, htarget, c, hc, hbound⟩, rfl⟩

/-- Actual compactness gives an actual finite positivity-patch cover independently of every test form. -/
theorem exists_finite_cover [CompactSpace M] (w : KahlerBackground n M) :
    ∃ t : Finset (PositiveChartPatch w), ∀ x : M,
      ∃ p ∈ t, x ∈ p.sourceNeighborhood := by
  classical
  choose p hp using (fun x : M => exists_patch_at w x)
  have hmem : ∀ x : M, (p x).sourceNeighborhood ∈ 𝓝 x := by
    intro x
    simpa only [hp x] using (p x).sourceNeighborhood_mem_nhds
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => (p x).sourceNeighborhood) (fun x _ => hmem x)
  refine ⟨t.image p, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (p y).sourceNeighborhood := by
    simpa using ht (mem_univ x)
  exact ⟨p y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩

end

end SGPT.Foundations.Analysis.Pending.XiaoPositiveCompactChartCover
