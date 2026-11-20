import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Basic

/-! Actual weighted Minkowski inclusions pass to genuine compact Hausdorff limits. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.MinkowskiHausdorffLimit
open Set Filter Metric
open scoped Topology Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {l : Filter ι} [NeBot l]

omit [NormedSpace ℝ E] [NeBot l] in
/-- Choose actual approximating points for every prescribed point of the limit. -/
theorem exists_selection_tendsto {A : Set E} {Aj : ι → Set E}
    (hA : IsCompact A) (hneA : A.Nonempty)
    (hAj : ∀ j, IsCompact (Aj j)) (hneAj : ∀ j, (Aj j).Nonempty)
    (hlim : Tendsto (fun j => hausdorffDist (Aj j) A) l (𝓝 0)) {x : E} (hx : x ∈ A) :
    ∃ u : ι → E, (∀ j, u j ∈ Aj j) ∧ Tendsto u l (𝓝 x) := by
  classical
  choose u hu hd using fun j => (hAj j).exists_infDist_eq_dist (hneAj j) x
  refine ⟨u, hu, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) ?_ hlim
  intro j
  rw [dist_comm, ← hd j]
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded hneA (hneAj j)
    hA.isBounded (hAj j).isBounded
  simpa only [hausdorffDist_comm] using infDist_le_hausdorffDist_of_mem hx hfin

omit [NormedSpace ℝ E] in
/-- Actual moving-set membership survives convergence to a compact Hausdorff limit. -/
theorem mem_of_tendsto_of_hausdorff {C : Set E} {Cj : ι → Set E} {u : ι → E} {x : E}
    (hC : IsCompact C) (hneC : C.Nonempty)
    (hCj : ∀ j, IsCompact (Cj j)) (hneCj : ∀ j, (Cj j).Nonempty)
    (hlim : Tendsto (fun j => hausdorffDist (Cj j) C) l (𝓝 0))
    (hu : Tendsto u l (𝓝 x)) (hmem : ∀ᶠ j in l, u j ∈ Cj j) : x ∈ C := by
  have hzero : Tendsto (fun j => infDist (u j) C) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => infDist_nonneg) ?_ hlim
    filter_upwards [hmem] with j hj
    exact infDist_le_hausdorffDist_of_mem hj
      (hausdorffEDist_ne_top_of_nonempty_of_bounded (hneCj j) hneC (hCj j).isBounded hC.isBounded)
  apply (hC.isClosed.mem_iff_infDist_zero hneC).mpr
  exact tendsto_nhds_unique ((continuous_infDist_pt C).tendsto x |>.comp hu) hzero

/-- Full weighted Minkowski inclusion, for arbitrary real coefficients and every normed dimension. -/
theorem weighted_sum_subset_of_hausdorff_limits {A B C : Set E} {Aj Bj Cj : ι → Set E}
    (hA : IsCompact A) (hneA : A.Nonempty) (hB : IsCompact B) (hneB : B.Nonempty)
    (hC : IsCompact C) (hneC : C.Nonempty)
    (hAj : ∀ j, IsCompact (Aj j)) (hneAj : ∀ j, (Aj j).Nonempty)
    (hBj : ∀ j, IsCompact (Bj j)) (hneBj : ∀ j, (Bj j).Nonempty)
    (hCj : ∀ j, IsCompact (Cj j)) (hneCj : ∀ j, (Cj j).Nonempty)
    (ha : Tendsto (fun j => hausdorffDist (Aj j) A) l (𝓝 0))
    (hb : Tendsto (fun j => hausdorffDist (Bj j) B) l (𝓝 0))
    (hc : Tendsto (fun j => hausdorffDist (Cj j) C) l (𝓝 0)) (α β : ℝ)
    (hinc : ∀ᶠ j in l, α • Aj j + β • Bj j ⊆ Cj j) : α • A + β • B ⊆ C := by
  rintro z ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨u, hu, hux⟩ := exists_selection_tendsto hA hneA hAj hneAj ha hx
  obtain ⟨v, hv, hvy⟩ := exists_selection_tendsto hB hneB hBj hneBj hb hy
  apply mem_of_tendsto_of_hausdorff hC hneC hCj hneCj hc
    ((hux.const_smul α).add (hvy.const_smul β))
  filter_upwards [hinc] with j hj
  exact hj ⟨α • u j, ⟨u j, hu j, rfl⟩, β • v j, ⟨v j, hv j, rfl⟩, rfl⟩

end SGPT.Convex.MinkowskiHausdorffLimit
