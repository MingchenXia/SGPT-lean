import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual Hausdorff convex-carrier closedness, convex-body completeness and Blaschke local compactness. -/

noncomputable section

namespace SGPT.AlmostSemigroup.Hyperspace

open Set Filter Metric TopologicalSpace InnerProductSpace MeasureTheory
open scoped Topology RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
/-- Every point of an actual Hausdorff limit has an actual sequence of member approximants. -/
theorem exists_member_sequence_of_tendsto {u : ℕ → NonemptyCompacts V}
    {K : NonemptyCompacts V} (hu : Tendsto u atTop (𝓝 K)) {x : V} (hx : x ∈ K) :
    ∃ v : ℕ → V, (∀ i, v i ∈ u i) ∧ Tendsto v atTop (𝓝 x) := by
  choose v hv heq using fun i ↦ (u i).isCompact.exists_infDist_eq_dist (u i).nonempty x
  refine ⟨v, hv, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ht := ((Metric.lipschitz_infDist_set x).continuous.tendsto K).comp hu
  change Tendsto (fun i ↦ infDist x (u i : Set V)) atTop
    (𝓝 (infDist x (K : Set V))) at ht
  rw [infDist_zero_of_mem hx] at ht
  convert ht using 1
  funext i
  exact (dist_comm _ _).trans (heq i).symm

omit [NormedSpace ℝ V] in
/-- Actual convergent member points of actual Hausdorff-convergent sets lie in the actual limit carrier. -/
theorem mem_of_tendsto_members {u : ℕ → NonemptyCompacts V}
    {K : NonemptyCompacts V} (hu : Tendsto u atTop (𝓝 K))
    {v : ℕ → V} {x : V} (hv : ∀ i, v i ∈ u i) (hvt : Tendsto v atTop (𝓝 x)) : x ∈ K := by
  have ht := Metric.uniformContinuous_infDist_Hausdorff_dist.continuous.tendsto (x, K)
  have h := ht.comp (hvt.prodMk_nhds hu)
  have hz : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (infDist x (K : Set V))) := by
    change Tendsto (fun i ↦ infDist (v i) (u i : Set V)) atTop
      (𝓝 (infDist x (K : Set V))) at h
    convert h using 1
    funext i
    exact (infDist_zero_of_mem (hv i)).symm
  have heq : infDist x (K : Set V) = 0 := tendsto_nhds_unique hz tendsto_const_nhds
  exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).mpr heq

/-- Genuine convexity of actual carriers is closed in the actual Hausdorff hyperspace. -/
theorem isClosed_convex_carriers : IsClosed {K : NonemptyCompacts V | Convex ℝ (K : Set V)} := by
  apply IsSeqClosed.isClosed
  intro u K hu hlim x hx y hy a b ha hb hab
  obtain ⟨v, hv, hvt⟩ := exists_member_sequence_of_tendsto hlim hx
  obtain ⟨w, hw, hwt⟩ := exists_member_sequence_of_tendsto hlim hy
  apply mem_of_tendsto_members hlim (fun i ↦ hu i (hv i) (hw i) ha hb hab)
  exact (hvt.const_smul a).add (hwt.const_smul b)

/-- The actual nonempty compact carrier of an actual convex body. -/
def carrierMap (K : ConvexBody V) : NonemptyCompacts V :=
  ⟨⟨(K : Set V), K.isCompact⟩, K.nonempty⟩

/-- Convex-body and nonempty-compact Hausdorff metrics coincide on their actual carriers. -/
theorem isometry_carrierMap : Isometry (carrierMap (V := V)) := by
  intro K L
  rw [edist_dist, edist_dist]
  rfl

/-- The actual image consists exactly of the actual convex carriers. -/
theorem range_carrierMap : range (carrierMap (V := V)) =
    {K : NonemptyCompacts V | Convex ℝ (K : Set V)} := by
  ext K
  constructor
  · rintro ⟨L, rfl⟩
    exact L.convex
  · intro hK
    exact ⟨⟨(K : Set V), hK, K.isCompact, K.nonempty⟩, NonemptyCompacts.ext rfl⟩

/-- The actual carrier map is a genuine closed embedding of metric spaces. -/
theorem isClosedEmbedding_carrierMap : Topology.IsClosedEmbedding (carrierMap (V := V)) :=
  ⟨isometry_carrierMap.isEmbedding, by rw [range_carrierMap]; exact isClosed_convex_carriers⟩

/-- The actual bodies lying inside an actual compact ambient set form an actual compact family. -/
theorem isCompact_bodies_subset {K : Set V} (hK : IsCompact K) :
    IsCompact {L : ConvexBody V | (L : Set V) ⊆ K} :=
  isClosedEmbedding_carrierMap.isCompact_preimage
    (NonemptyCompacts.isCompact_subsets_of_isCompact hK)

instance [CompleteSpace V] : CompleteSpace (ConvexBody V) :=
  isometry_carrierMap.isUniformEmbedding.completeSpace
    isClosedEmbedding_carrierMap.isClosed_range.isComplete

/-- Blaschke local compactness is transported from the actual compact-set hyperspace. -/
instance [LocallyCompactSpace V] : LocallyCompactSpace (ConvexBody V) :=
  isClosedEmbedding_carrierMap.locallyCompactSpace

/-- Exact finite-dimensional Euclidean source Blaschke theorem. -/
theorem euclidean_blaschke (n : ℕ) : LocallyCompactSpace (ConvexBody (EuclideanSpace ℝ (Fin n))) :=
  inferInstance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- An actual inner ball persists in every genuinely Hausdorff-close convex body. -/
theorem mem_of_closedBall_subset_of_hausdorff_lt (K L : ConvexBody W)
    {x : W} {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set W))
    (hd : dist K L < r) : x ∈ L := by
  by_contra hx
  obtain ⟨p, hp, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex
    L.nonempty L.isCompact.isComplete L.convex x
  have hxp : x ≠ p := by
    intro heq
    apply hx
    rw [heq]
    exact hp
  have hv : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
  let y : W := x + (r / ‖x - p‖) • (x - p)
  have hy : y ∈ K := by
    apply hball
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [y]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr.le hv.le), div_mul_cancel₀ r (ne_of_gt hv)]
  obtain ⟨z, hz, hzy⟩ := exists_dist_lt_of_hausdorffDist_lt hy hd
    (ConvexBody.hausdorffEDist_ne_top (K := K) (L := L))
  have hs := (norm_eq_iInf_iff_real_inner_le_zero L.convex hp).mp hpmin z hz
  have hid : y - z = (x - p) + (r / ‖x - p‖) • (x - p) - (z - p) := by
    dsimp only [y]
    abel
  have hc := real_inner_le_norm (x - p) (y - z)
  have hcancel : r / ‖x - p‖ * ‖x - p‖ ^ 2 = r * ‖x - p‖ := by
    field_simp
  have hinner : ⟪x - p, y - z⟫_ℝ =
      ‖x - p‖ ^ 2 + r * ‖x - p‖ - ⟪x - p, z - p⟫_ℝ := by
    rw [hid, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hcancel]
  rw [hinner] at hc
  rw [dist_eq_norm] at hzy
  nlinarith [norm_nonneg (y - z)]

/-- Actual interior points eventually belong to the original Hausdorff-convergent convex bodies. -/
theorem eventually_mem_of_mem_interior {u : ℕ → ConvexBody W} {K : ConvexBody W}
    (hu : Tendsto u atTop (𝓝 K)) {x : W} (hx : x ∈ interior (K : Set W)) :
    ∀ᶠ i in atTop, x ∈ u i := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  have hhalf : 0 < r / 2 := half_pos hr
  have hclosed : closedBall x (r / 2) ⊆ (K : Set W) :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans (hball.trans interior_subset)
  have ht := (Metric.tendsto_nhds.mp hu) (r / 2) hhalf
  filter_upwards [ht] with i hi
  apply mem_of_closedBall_subset_of_hausdorff_lt K (u i) hhalf hclosed
  simpa only [dist_comm] using hi

/-- Actual exterior points eventually stay out of the original Hausdorff-convergent bodies. -/
theorem eventually_not_mem_of_not_mem {u : ℕ → ConvexBody W} {K : ConvexBody W}
    (hu : Tendsto u atTop (𝓝 K)) {x : W} (hx : x ∉ K) :
    ∀ᶠ i in atTop, x ∉ u i := by
  have hpos : 0 < infDist x (K : Set W) := (K.isClosed.notMem_iff_infDist_pos K.nonempty).mp hx
  have ht := (Metric.tendsto_nhds.mp hu) (infDist x (K : Set W)) hpos
  filter_upwards [ht] with i hi
  intro hxi
  have h := infDist_le_hausdorffDist_of_mem hxi
    (ConvexBody.hausdorffEDist_ne_top (K := u i) (L := K))
  exact hi.not_ge h

/-- True indicators converge outside the actual null convex frontier. -/
theorem tendsto_indicator_of_not_mem_frontier {u : ℕ → ConvexBody W} {K : ConvexBody W}
    (hu : Tendsto u atTop (𝓝 K)) {x : W} (hx : x ∉ frontier (K : Set W)) :
    Tendsto (fun i ↦ (u i : Set W).indicator (fun _ ↦ (1 : ℝ)) x) atTop
      (𝓝 ((K : Set W).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hxK : x ∈ K
  · have hxInt : x ∈ interior (K : Set W) := by
      by_contra hn
      exact hx ((mem_frontier_iff_notMem_interior hxK).mpr hn)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_of_mem_interior hu hxInt] with i hi
    simp [hi, hxK]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_not_mem_of_not_mem hu hxK] with i hi
    simp [hi, hxK]

/-- A genuinely convergent sequence of bodies has a genuine compact ambient union bound. -/
theorem exists_compact_containing_sequence {u : ℕ → ConvexBody W} {K : ConvexBody W}
    (hu : Tendsto u atTop (𝓝 K)) :
    ∃ B : Set W, IsCompact B ∧ (K : Set W) ⊆ B ∧ ∀ i, (u i : Set W) ⊆ B := by
  let A : Set (NonemptyCompacts W) := carrierMap '' (insert K (range u))
  have hA : IsCompact A := hu.isCompact_insert_range.image isometry_carrierMap.continuous
  let B : Set W := ⋃ L ∈ A, (L : Set W)
  refine ⟨B, NonemptyCompacts.isCompact_biUnion_coe_of_isCompact hA, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨carrierMap K, mem_iUnion.mpr
      ⟨mem_image_of_mem _ (mem_insert K _), hx⟩⟩
  · intro i x hx
    exact mem_iUnion.mpr ⟨carrierMap (u i), mem_iUnion.mpr
      ⟨mem_image_of_mem _ (mem_insert_of_mem _ (mem_range_self i)), hx⟩⟩

/-- Actual Euclidean body volumes converge along the original Hausdorff-convergent sequence. -/
theorem tendsto_euclidean_real_volume {n : ℕ}
    {u : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
    {K : ConvexBody (EuclideanSpace ℝ (Fin n))} (hu : Tendsto u atTop (𝓝 K)) :
    Tendsto (fun i ↦ volume.real (u i : Set (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (volume.real (K : Set (EuclideanSpace ℝ (Fin n))))) := by
  obtain ⟨B, hB, _, huB⟩ := exists_compact_containing_sequence hu
  have hBi : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrable_indicator_iff hB.measurableSet).mpr
      (integrableOn_const (hB.measure_ne_top (μ := volume)))
  have hmeas (i : ℕ) : AEStronglyMeasurable
      ((u i : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ (1 : ℝ))) volume :=
    aestronglyMeasurable_const.indicator (u i).isCompact.measurableSet
  have hbound (i : ℕ) : ∀ᵐ x ∂volume,
      ‖(u i : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ (1 : ℝ)) x‖ ≤
        B.indicator (fun _ ↦ (1 : ℝ)) x := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hxi : x ∈ u i
    · simp only [indicator_of_mem hxi, norm_one, indicator_of_mem (huB i hxi), le_refl]
    · simp only [indicator_of_notMem hxi, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ zero_le_one) x
  have hnull : volume (frontier (K : Set (EuclideanSpace ℝ (Fin n)))) = 0 :=
    K.convex.addHaar_frontier volume
  have hpoint : ∀ᵐ x ∂volume, Tendsto
      (fun i ↦ (u i : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ (1 : ℝ)) x) atTop
      (𝓝 ((K : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ (1 : ℝ)) x)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    exact tendsto_indicator_of_not_mem_frontier hu hx
  have ht := tendsto_integral_of_dominated_convergence (B.indicator (fun _ ↦ (1 : ℝ)))
    hmeas hBi hbound hpoint
  have hi (i : ℕ) : (∫ x, (u i : Set (EuclideanSpace ℝ (Fin n))).indicator
      (fun _ ↦ (1 : ℝ)) x ∂volume) = volume.real (u i : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := volume) (1 : ℝ) (u i).isCompact.measurableSet)
  have hK : (∫ x, (K : Set (EuclideanSpace ℝ (Fin n))).indicator
      (fun _ ↦ (1 : ℝ)) x ∂volume) = volume.real (K : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := volume) (1 : ℝ) K.isCompact.measurableSet)
  simpa only [hi, hK] using ht

/-- Exact SGPT convex-body volume continuity for the true Euclidean Hausdorff metric. -/
theorem continuous_euclidean_real_volume (n : ℕ) :
    Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) ↦
      volume.real (K : Set (EuclideanSpace ℝ (Fin n)))) := by
  apply SeqContinuous.continuous
  intro u K hu
  exact tendsto_euclidean_real_volume hu

/-- The actual nonnegative real Lebesgue volume of an actual Euclidean convex body. -/
def euclideanVolume {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) : NNReal :=
  ⟨volume.real (K : Set (EuclideanSpace ℝ (Fin n))), ENNReal.toReal_nonneg⟩

/-- Exact source nonnegative-volume continuity for the actual Euclidean Hausdorff target. -/
theorem continuous_euclideanVolume (n : ℕ) :
    Continuous (euclideanVolume (n := n)) :=
  (continuous_euclidean_real_volume n).subtype_mk (fun _ ↦ ENNReal.toReal_nonneg)

/-- Exact real max-sup-inf Hausdorff formula on the actual source convex bodies. -/
theorem dist_eq_max_sSup_infDist (K L : ConvexBody V) :
    dist K L = max
      (sSup ((fun x ↦ infDist x (L : Set V)) '' (K : Set V)))
      (sSup ((fun x ↦ infDist x (K : Set V)) '' (L : Set V))) := by
  have hbK : BddAbove ((fun x ↦ infDist x (L : Set V)) '' (K : Set V)) :=
    (K.isCompact.image (continuous_infDist_pt (L : Set V))).bddAbove
  have hbL : BddAbove ((fun x ↦ infDist x (K : Set V)) '' (L : Set V)) :=
    (L.isCompact.image (continuous_infDist_pt (K : Set V))).bddAbove
  apply le_antisymm
  · obtain ⟨x, hx⟩ := K.nonempty
    have hxle := le_csSup hbK (mem_image_of_mem _ hx)
    have hn : 0 ≤ sSup ((fun x ↦ infDist x (L : Set V)) '' (K : Set V)) :=
      infDist_nonneg.trans hxle
    apply hausdorffDist_le_of_infDist (hn.trans (le_max_left _ _))
    · intro x hx
      exact (le_csSup hbK (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    · intro x hx
      exact (le_csSup hbL (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · apply max_le
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨x, hx, rfl⟩
      exact infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top
    · apply csSup_le (L.nonempty.image _)
      rintro _ ⟨x, hx, rfl⟩
      exact (infDist_le_hausdorffDist_of_mem hx
        (ConvexBody.hausdorffEDist_ne_top (K := L) (L := K))).trans_eq (dist_comm L K)


/-- Exact source formula with the actual real infimum of Euclidean differences. -/
theorem dist_eq_max_sSup_iInf_norm (K L : ConvexBody V) :
    dist K L = max
      (sSup ((fun x ↦ ⨅ y : (L : Set V), ‖x - (y : V)‖) '' (K : Set V)))
      (sSup ((fun x ↦ ⨅ y : (K : Set V), ‖x - (y : V)‖) '' (L : Set V))) := by
  simpa only [infDist_eq_iInf, dist_eq_norm] using dist_eq_max_sSup_infDist K L

/-- Actual source convex bodies are exactly the nonempty compact convex sets, allowing empty interior. -/
theorem exists_convexBody_iff (K : Set V) :
    (∃ L : ConvexBody V, (L : Set V) = K) ↔ K.Nonempty ∧ IsCompact K ∧ Convex ℝ K := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.nonempty, L.isCompact, L.convex⟩
  · rintro ⟨hne, hcompact, hconvex⟩
    exact ⟨⟨K, hconvex, hcompact, hne⟩, rfl⟩


end SGPT.AlmostSemigroup.Hyperspace
