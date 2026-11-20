import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
import SGPT.Foundations.Analysis.Pending.ChartPartition
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

/-! # Actual precompact simultaneous slot-chart partition

Genuine local potentials and a true half-radius coordinate ball produce
compact collars before the actual finite smooth partition theorem.
No preselected geometric cover or potential is a hypothesis.
-/

open Set TopologicalSpace
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualPrecompactSlotChartPartition

open FirstPass FirstPass.PositiveClasses GlobalSlotStokes ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem exists_precompact_chart_at
    (η : Fin n → ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm n M) (x : M) :
    ∃ (J : SlotChart η κ) (D : Opens (ComplexModel n)),
      x ∈ J.chart.val.source ∧ J.chart.val x ∈ D ∧
      IsCompact (closure (D : Set (ComplexModel n))) ∧
      closure (D : Set (ComplexModel n)) ⊆ J.domain := by
  obtain ⟨J, hx⟩ := SlotChart.exists_mem_source η κ x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp J.domain.isOpen (J.chart.val x) hx.2
  let D : Opens (ComplexModel n) := ⟨Metric.ball (J.chart.val x) (r / 2), Metric.isOpen_ball⟩
  have hhalf : 0 < r / 2 := half_pos hr
  have hcl : closure (D : Set (ComplexModel n)) ⊆
      Metric.closedBall (J.chart.val x) (r / 2) := Metric.closure_ball_subset_closedBall
  refine ⟨J, D, hx.1, Metric.mem_ball_self hhalf,
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl, ?_⟩
  exact hcl.trans ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hball)

variable [CompactSpace M]

/-- Actual half-radius coordinate collars and compactness internally supply
the finite chart-smooth partition on precompact simultaneous slot sources. -/
theorem exists_precompact_chart_partition
    (η : Fin n → ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm n M) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ) (J : Fin m → SlotChart η κ)
      (D : Fin m → Opens (ComplexModel n)),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧
      (∀ a x, 0 ≤ χ a x) ∧
      (∀ a, IsCompact (closure (D a : Set (ComplexModel n)))) ∧
      (∀ a, closure (D a : Set (ComplexModel n)) ⊆ (J a).domain) ∧
      (∀ a, tsupport (χ a) ⊆ (J a).chart.val.source ∩ (J a).chart.val ⁻¹' D a) ∧
      (∀ a, HasCompactSupport (χ a)) ∧ ∀ x, ∑ a, χ a x = 1 := by
  classical
  let ι := {p : SlotChart η κ × Opens (ComplexModel n) //
    IsCompact (closure (p.2 : Set (ComplexModel n))) ∧
      closure (p.2 : Set (ComplexModel n)) ⊆ p.1.domain}
  let S (p : ι) : Opens M := ⟨p.val.1.chart.val.source ∩ p.val.1.chart.val ⁻¹' p.val.2,
    p.val.1.chart.val.isOpen_inter_preimage p.val.2.isOpen⟩
  have hcover (x : M) : ∃ p : ι, x ∈ S p := by
    obtain ⟨J, D, hxs, hxD, hcompact, hclosure⟩ := exists_precompact_chart_at η κ x
    exact ⟨⟨(J, D), hcompact, hclosure⟩, hxs, hxD⟩
  obtain ⟨m, χ, idx, hsm, h0, hsupp, hcpt, h1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  exact ⟨m, χ, (fun a => (idx a).val.1), (fun a => (idx a).val.2), hsm, h0,
    (fun a => (idx a).property.1), (fun a => (idx a).property.2), hsupp, hcpt, h1⟩

end
end SGPT.Foundations.Analysis.Pending.ActualPrecompactSlotChartPartition
