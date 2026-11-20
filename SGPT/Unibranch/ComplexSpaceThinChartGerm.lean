import SGPT.Unibranch.ComplexSpaceUnibranchConnectedGerm

/-! Original thinness supplies actual analytic-chart germ noncontainment.
Blueprint: complex-space-thin-chart-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.LocalEmbedding

/-- Genuine original empty interior rules out actual chart-germ containment;
the desired local noncontainment is manufactured, not an input. -/
theorem not_eventually_chartGerm_le_of_interior_empty
    {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (c : e.carrier)
    {Z : Set X.obj.left} (hZ : interior Z = ∅) (B : Set e.ambient)
    (hrep : e.toPoint ⁻¹' Z = Subtype.val ⁻¹' B) :
    ¬ AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := e.dim) B c.val := by
  intro hAB
  let E := (complexChartAt (n := e.dim) c.val).val
  let q := E c.val
  have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
  have ht : Tendsto (fun y : e.ambient => E y-q) (𝓝 c.val) (𝓝 0) := by
    have h := ((E.continuousAt hp).sub (continuousAt_const : ContinuousAt (fun _ : e.ambient => q) c.val)).tendsto
    change Tendsto (fun y : e.ambient => E y-q) (𝓝 c.val) (𝓝 (E c.val-q)) at h
    simpa only [q,sub_self] using h
  have hev : ∀ᶠ y in 𝓝 c.val,y ∈ e.carrier → y ∈ B := by
    filter_upwards [ht.eventually hAB,E.open_source.mem_nhds hp] with y hy hys hyC
    have hyA : E y-q ∈ AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val := by
      change E y-q+q ∈ E.target ∩ E.symm ⁻¹' e.carrier
      rw [sub_add_cancel]
      exact ⟨E.map_source hys,by simpa only [mem_preimage,E.left_inv hys] using hyC⟩
    have hyB := hy hyA
    change E y-q+q ∈ E.target ∩ E.symm ⁻¹' B at hyB
    rw [sub_add_cancel] at hyB
    simpa only [mem_preimage,E.left_inv hys] using hyB.2
  have hcB : ∀ᶠ d : e.carrier in 𝓝 c,d.val ∈ B := by
    filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hev] with d hd
    exact hd d.property
  have hcZ : ∀ᶠ d : e.carrier in 𝓝 c,e.toPoint d ∈ Z := by
    filter_upwards [hcB] with d hd
    exact (Set.ext_iff.mp hrep d).mpr hd
  have hnhds : Z ∈ 𝓝 (e.toPoint c) := by
    rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
    exact eventually_map.mpr hcZ
  have hin := mem_interior_iff_mem_nhds.mpr hnhds
  rw [hZ] at hin
  exact hin

end SGPT.Unibranch.LocalEmbedding
