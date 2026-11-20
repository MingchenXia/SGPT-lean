import SGPT.AlmostSemigroup.Hyperspace
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace SGPT.AlmostSemigroup.BodyLimits
open Set Filter Metric
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact source closed tail-union liminf of the actual convex-body carriers. -/
def tailLiminf (u : ℕ → ConvexBody V) : Set V :=
  closure (⋃ i : ℕ, {x | ∀ j, i ≤ j → x ∈ u j})

/-- Exact source eq:liminflimsup from a genuine Hausdorff-convergent original subsequence. -/
theorem tailLiminf_subset_limit {u : ℕ → ConvexBody V} {K : ConvexBody V}
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hu : Tendsto (u ∘ φ) atTop (𝓝 K)) :
    tailLiminf u ⊆ (K : Set V) := by
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hnear : ∀ᶠ j in atTop, i ≤ φ j := hφ.tendsto_atTop.eventually_ge_atTop i
  have hzero : (fun j ↦ infDist x (u (φ j) : Set V)) =ᶠ[atTop] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hnear] with j hj
    exact infDist_zero_of_mem (hi (φ j) hj)
  have hsets := Hyperspace.isometry_carrierMap.continuous.tendsto K |>.comp hu
  have hd := ((Metric.lipschitz_infDist_set x).continuous.tendsto (Hyperspace.carrierMap K)).comp hsets
  change Tendsto (fun j ↦ infDist x (u (φ j) : Set V)) atTop (𝓝 (infDist x (K : Set V))) at hd
  have hz : Tendsto (fun j ↦ infDist x (u (φ j) : Set V)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' hzero.symm
  exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).mpr (tendsto_nhds_unique hd hz)

/-- Genuine connected convex carriers meet each actual intermediate sphere. -/
theorem exists_member_dist_eq (K : ConvexBody V) {c p q : V} {r : ℝ}
    (hp : p ∈ K) (hq : q ∈ K) (hpr : dist p c ≤ r) (hrq : r ≤ dist q c) :
    ∃ z ∈ K, dist z c = r :=
  K.convex.isPreconnected.intermediate_value hp hq
    (continuous_id.dist continuous_const).continuousOn ⟨hpr, hrq⟩

variable [ProperSpace V]

/-- Actual convergent member-limit exclusion and one genuine anchor sequence force a uniform body bound. -/
theorem eventually_bounded_of_member_limits {u : ℕ → ConvexBody V} {K : ConvexBody V}
    {c : V} {p : ℕ → V} (hp : ∀ i, p i ∈ u i) (hpc : Tendsto p atTop (𝓝 c))
    (hupper : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (q : ℕ → V) (x : V),
      (∀ i, q i ∈ u (φ i)) → Tendsto q atTop (𝓝 x) → x ∈ K) :
    ∃ R : ℝ, ∀ᶠ i in atTop, (u i : Set V) ⊆ closedBall c R := by
  obtain ⟨R, hRpos, hKR⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 c
  refine ⟨R + 1, ?_⟩
  by_contra hbound
  have hbad : ∃ᶠ i in atTop, ¬ (u i : Set V) ⊆ closedBall c (R + 1) :=
    not_eventually.mp hbound
  have hanchor : ∀ᶠ i in atTop, dist (p i) c ≤ R + 1 := by
    have hdist := tendsto_iff_dist_tendsto_zero.mp hpc
    exact (hdist.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < R + 1))).mono
      (fun _ h ↦ h.le)
  have hbad' : ∃ᶠ i in atTop,
      dist (p i) c ≤ R + 1 ∧ ¬ (u i : Set V) ⊆ closedBall c (R + 1) :=
    hbad.and_eventually hanchor |>.mono (fun _ h ↦ ⟨h.2, h.1⟩)
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  have hex (i : ℕ) : ∃ z ∈ u (φ i), dist z c = R + 1 := by
    obtain ⟨q, hq, hqout⟩ := Set.not_subset.mp (hφbad i).2
    have hqr : R + 1 ≤ dist q c := le_of_lt (lt_of_not_ge hqout)
    exact exists_member_dist_eq (u (φ i)) (hp (φ i)) hq (hφbad i).1 hqr
  choose z hz hzr using hex
  obtain ⟨x, hx, ψ, hψ, hzx⟩ := (isCompact_sphere c (R + 1)).tendsto_subseq
    (fun i ↦ hzr i)
  have hxK := hupper (φ ∘ ψ) (hφ.comp hψ) (z ∘ ψ) x (fun i ↦ hz (ψ i)) hzx
  have hxR : dist x c ≤ R := hKR hxK
  change dist x c = R + 1 at hx
  linarith

/-- The actual source point and member-limit conditions give genuine Hausdorff convergence, with the body bound produced from convexity. -/
theorem tendsto_of_point_member_conditions {u : ℕ → ConvexBody V} {K : ConvexBody V}
    (hlower : ∀ x ∈ K, ∃ p : ℕ → V, (∀ i, p i ∈ u i) ∧ Tendsto p atTop (𝓝 x))
    (hupper : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (q : ℕ → V) (x : V),
      (∀ i, q i ∈ u (φ i)) → Tendsto q atTop (𝓝 x) → x ∈ K) :
    Tendsto u atTop (𝓝 K) := by
  obtain ⟨c, hc⟩ := K.nonempty
  obtain ⟨p, hp, hpc⟩ := hlower c hc
  obtain ⟨R, hbound⟩ := eventually_bounded_of_member_limits hp hpc hupper
  apply (Hyperspace.isCompact_bodies_subset (isCompact_closedBall c R)).tendsto_nhds_of_unique_mapClusterPt hbound
  intro L _ hL
  obtain ⟨φ, hφ, huL⟩ := hL.tendsto_subseq
  have hsets := Hyperspace.isometry_carrierMap.continuous.tendsto L |>.comp huL
  apply ConvexBody.ext
  apply subset_antisymm
  · intro x hx
    obtain ⟨q, hq, hqx⟩ := Hyperspace.exists_member_sequence_of_tendsto hsets hx
    exact hupper φ hφ q x hq hqx
  · intro x hx
    obtain ⟨q, hq, hqx⟩ := hlower x hx
    exact Hyperspace.mem_of_tendsto_members hsets (fun i ↦ hq (φ i))
      (hqx.comp hφ.tendsto_atTop)

/-- SGPT thm:Hausconvcond: the exact genuine Hausdorff point-approximation and subsequence member-limit criterion. -/
theorem tendsto_iff_point_member_conditions {u : ℕ → ConvexBody V} {K : ConvexBody V} :
    Tendsto u atTop (𝓝 K) ↔
      (∀ x ∈ K, ∃ p : ℕ → V, (∀ i, p i ∈ u i) ∧ Tendsto p atTop (𝓝 x)) ∧
      (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (q : ℕ → V) (x : V),
        (∀ i, q i ∈ u (φ i)) → Tendsto q atTop (𝓝 x) → x ∈ K) := by
  constructor
  · intro hu
    have hsets := Hyperspace.isometry_carrierMap.continuous.tendsto K |>.comp hu
    refine ⟨fun _ hx ↦ Hyperspace.exists_member_sequence_of_tendsto hsets hx, ?_⟩
    intro φ hφ q x hq hqx
    exact Hyperspace.mem_of_tendsto_members (hsets.comp hφ.tendsto_atTop) hq hqx
  · exact fun h ↦ tendsto_of_point_member_conditions h.1 h.2

/-- Exact original source strictly-positive index convention, obtained by an actual one-step tail shift. -/
theorem tendsto_iff_point_positive_member_conditions {u : ℕ → ConvexBody V} {K : ConvexBody V} :
    Tendsto u atTop (𝓝 K) ↔
      (∀ x ∈ K, ∃ p : ℕ → V, (∀ i, p i ∈ u i) ∧ Tendsto p atTop (𝓝 x)) ∧
      (∀ (φ : ℕ → ℕ), StrictMono φ → (∀ i, 0 < φ i) → ∀ (q : ℕ → V) (x : V),
        (∀ i, q i ∈ u (φ i)) → Tendsto q atTop (𝓝 x) → x ∈ K) := by
  constructor
  · intro hu
    obtain ⟨hlower, hupper⟩ := tendsto_iff_point_member_conditions.mp hu
    exact ⟨hlower, fun φ hφ _ q x hq hqx ↦ hupper φ hφ q x hq hqx⟩
  · rintro ⟨hlower, hupper⟩
    apply tendsto_of_point_member_conditions hlower
    intro φ hφ q x hq hqx
    have hshift : StrictMono (fun i : ℕ ↦ i + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
    have hpos (i : ℕ) : 0 < φ (i + 1) :=
      lt_of_le_of_lt (Nat.zero_le (φ 0)) (hφ (Nat.zero_lt_succ i))
    exact hupper (fun i ↦ φ (i + 1)) (hφ.comp hshift) hpos (fun i ↦ q (i + 1)) x
      (fun i ↦ hq (i + 1)) (hqx.comp hshift.tendsto_atTop)

end SGPT.AlmostSemigroup.BodyLimits
