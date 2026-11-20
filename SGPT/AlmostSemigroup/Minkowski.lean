import SGPT.AlmostSemigroup.Hyperspace

noncomputable section
namespace SGPT.AlmostSemigroup.Minkowski
open Set Metric
open scoped Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact source def:almostsg:L138, reusing the actual existing convex-body sum carrier. -/
theorem mem_add_iff (K L : ConvexBody V) (x : V) :
    x ∈ K + L ↔ ∃ k ∈ K, ∃ l ∈ L, k + l = x := by
  change x ∈ ((K + L : ConvexBody V) : Set V) ↔ _
  rw [ConvexBody.coe_add]
  exact Set.mem_add

/-- Genuine compact nearest members bound every actual sum member by the two original Hausdorff distances. -/
theorem exists_sum_member_dist_le (K L K' L' : ConvexBody V) {x : V}
    (hx : x ∈ K + L) : ∃ y ∈ K' + L', dist x y ≤ dist K K' + dist L L' := by
  obtain ⟨k, hk, l, hl, rfl⟩ := (mem_add_iff K L x).mp hx
  obtain ⟨k', hk', hkk'⟩ := K'.isCompact.exists_infDist_eq_dist K'.nonempty k
  obtain ⟨l', hl', hll'⟩ := L'.isCompact.exists_infDist_eq_dist L'.nonempty l
  refine ⟨k' + l', (mem_add_iff K' L' _).mpr ⟨k', hk', l', hl', rfl⟩, ?_⟩
  have hdK : dist k k' ≤ dist K K' := by
    rw [← hkk']
    exact infDist_le_hausdorffDist_of_mem hk ConvexBody.hausdorffEDist_ne_top
  have hdL : dist l l' ≤ dist L L' := by
    rw [← hll']
    exact infDist_le_hausdorffDist_of_mem hl ConvexBody.hausdorffEDist_ne_top
  exact (dist_add_add_le k l k' l').trans (add_le_add hdK hdL)

/-- Actual quantitative Minkowski-sum Hausdorff bound in the original normed-space metric. -/
theorem dist_add_le (K L K' L' : ConvexBody V) :
    dist (K + L) (K' + L') ≤ dist K K' + dist L L' := by
  apply hausdorffDist_le_of_mem_dist (by positivity)
  · intro x hx
    exact exists_sum_member_dist_le K L K' L' hx
  · intro x hx
    obtain ⟨y, hy, hd⟩ := exists_sum_member_dist_le K' L' K L hx
    refine ⟨y, hy, ?_⟩
    simpa only [dist_comm K' K, dist_comm L' L] using hd

/-- The true original Minkowski map is genuinely two-Lipschitz for the product Hausdorff metric. -/
theorem lipschitzWith_add :
    LipschitzWith 2 (fun p : ConvexBody V × ConvexBody V ↦ p.1 + p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := dist_add_le p.1 p.2 q.1 q.2
  have h1 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have h2 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  simp only [Prod.dist_eq, NNReal.coe_ofNat]
  linarith

/-- Exact source appendix_almostsg:proposition:11: actual Minkowski sum continuity. -/
theorem continuous_add : Continuous (fun p : ConvexBody V × ConvexBody V ↦ p.1 + p.2) :=
  lipschitzWith_add.continuous

end SGPT.AlmostSemigroup.Minkowski
