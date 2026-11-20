import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

set_option autoImplicit false

/-! # Actual bounded-remainder rational analytic types pull back holomorphically -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback

open FirstPass FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {k n : ℕ} {Y X : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Compose the actual finite holomorphic family and bounded remainder in
every genuine target chart, retaining the rational coefficient and poles. -/
theorem hasManifoldAnalyticSingularityType_comp {ι : Y → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {v : X → EReal} (hv : HasManifoldAnalyticSingularityType (n := n) v) :
    HasManifoldAnalyticSingularityType (n := k) (fun y => v (ι y)) := by
  intro e z hz
  let d := complexChartAt (n := n) (ι (e.val.symm z))
  let F := HolomorphicMaps.coordinateMap ι e d
  have hzd : z ∈ HolomorphicMaps.coordinateDomain ι e d :=
    ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hι e d
  have hFc : ContDiffOn ℂ ∞ F (HolomorphicMaps.coordinateDomain ι e d) :=
    HolomorphicMaps.coordinateMap_contDiffOn hι e d
  have hFz : ContinuousAt F z :=
    (HolomorphicMaps.coordinateMap_contDiffAt hι e d hzd).continuousAt
  obtain ⟨c, N, f, hc, ⟨U, hU, hwU, hfU⟩, b, hb, heq⟩ :=
    hv d (F z) (HolomorphicMaps.coordinateMap_mem_target hzd)
  refine ⟨c, N, fun i y => f i (F y), hc,
    ⟨HolomorphicMaps.coordinateDomain ι e d ∩ F ⁻¹' U,
      hFc.continuousOn.isOpen_inter_preimage hD hU, ⟨hzd, hwU⟩, ?_⟩,
    fun y => b (F y), hb.comp_continuousAt hFz, ?_⟩
  · intro i
    exact (hfU i).comp ((hFc.differentiableOn (by simp)).mono inter_subset_left)
      (fun y hy => hy.2)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually heq] with y hy hey
    have hcoord : chartFunction (fun y => v (ι y)) e y = chartFunction v d (F y) := by
      change v (ι (e.val.symm y)) = v (d.val.symm (d.val (ι (e.val.symm y))))
      rw [d.val.left_inv hy.2]
    rw [hcoord, hey]
    rfl

end

end SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
