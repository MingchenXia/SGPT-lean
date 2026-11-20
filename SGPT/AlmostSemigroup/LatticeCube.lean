import SGPT.AlmostSemigroup.Hyperspace
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
namespace SGPT.AlmostSemigroup.LatticeCube
open Set Metric
open scoped Topology Pointwise

/-- Actual corners of the source coordinate lattice cube around an actual point. -/
def corners {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) : Set (Fin n → ℝ) :=
  Set.pi univ (fun i ↦ {((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) / k,
    (((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) + 1) / k})

/-- Genuine floor inequalities put the original point in the actual lattice-corner convex hull. -/
theorem mem_convexHull_corners {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {k : ℕ} (hk : 0 < k) : (fun i ↦ x i) ∈ convexHull ℝ (corners x k) := by
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  apply mem_convexHull_pi
  intro i _
  have hlo := Int.floor_le ((k : ℝ) * x i)
  have hhi := Int.lt_floor_add_one ((k : ℝ) * x i)
  have hl : ((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) / k ≤ x i :=
    (div_le_iff₀ hkr).mpr (by simpa only [mul_comm] using hlo)
  have hu : x i ≤ (((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) + 1) / k :=
    (le_div_iff₀ hkr).mpr (by simpa only [mul_comm] using hhi.le)
  rw [convexHull_pair, segment_eq_Icc (hl.trans hu)]
  exact ⟨hl, hu⟩

/-- Every actual corner is within the true Euclidean source radius sqrt(n)/k. -/
theorem corner_dist_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {k : ℕ} (hk : 0 < k) {q : Fin n → ℝ} (hq : q ∈ corners x k) :
    dist ((EuclideanSpace.equiv (Fin n) ℝ).symm q) x ≤ Real.sqrt n / k := by
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hcoord (i : Fin n) : |q i - x i| ≤ 1 / (k : ℝ) := by
    have hlo := Int.floor_le ((k : ℝ) * x i)
    have hhi := Int.lt_floor_add_one ((k : ℝ) * x i)
    have hl : ((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) / k ≤ x i :=
      (div_le_iff₀ hkr).mpr (by simpa only [mul_comm] using hlo)
    have hu : x i ≤ (((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) + 1) / k :=
      (le_div_iff₀ hkr).mpr (by simpa only [mul_comm] using hhi.le)
    have hwidth : (((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) + 1) / k -
        ((⌊(k : ℝ) * x i⌋ : ℤ) : ℝ) / k = 1 / (k : ℝ) := by ring
    have hqi := hq i (mem_univ i)
    rcases hqi with hqi | hqi
    · rw [hqi]
      exact abs_le.mpr ⟨by linarith, by linarith [one_div_pos.mpr hkr]⟩
    · rw [hqi]
      exact abs_le.mpr ⟨by linarith [one_div_pos.mpr hkr], by linarith⟩
  have hs : dist ((EuclideanSpace.equiv (Fin n) ℝ).symm q) x ^ 2 ≤
      (n : ℝ) * (1 / (k : ℝ)) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp only [Real.dist_eq]
    change (∑ i, |q i - x i| ^ 2) ≤ (n : ℝ) * (1 / (k : ℝ)) ^ 2
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      pow_le_pow_left₀ (abs_nonneg (q i - x i)) (hcoord i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hsum
  have hrad : (Real.sqrt (n : ℝ) / k) ^ 2 = (n : ℝ) * (1 / (k : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hr : 0 ≤ Real.sqrt (n : ℝ) / k := div_nonneg (Real.sqrt_nonneg _) hkr.le
  nlinarith [dist_nonneg (x := (EuclideanSpace.equiv (Fin n) ℝ).symm q) (y := x)]

/-- The actual scaled standard coordinate lattice in the genuine Euclidean ambient space. -/
def latticeGrid (n k : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  range (fun z : Fin n → ℤ ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i ↦ (z i : ℝ) / k))

/-- Every actual cube corner is an actual point of the actual scaled integer lattice. -/
theorem corner_mem_latticeGrid {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    {q : Fin n → ℝ} (hq : q ∈ corners x k) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm q ∈ latticeGrid n k := by
  have hint (i : Fin n) : ∃ z : ℤ, q i = (z : ℝ) / k := by
    rcases hq i (mem_univ i) with h | h
    · exact ⟨⌊(k : ℝ) * x i⌋, h⟩
    · exact ⟨⌊(k : ℝ) * x i⌋ + 1, by simpa only [mem_singleton_iff, Int.cast_add, Int.cast_one] using h⟩
  choose z hz using hint
  refine ⟨z, ?_⟩
  change (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i ↦ (z i : ℝ) / k) =
    (EuclideanSpace.equiv (Fin n) ℝ).symm q
  apply congrArg (EuclideanSpace.equiv (Fin n) ℝ).symm
  funext i
  exact (hz i).symm

/-- Actual lattice inclusion and the actual corner convex hull imply genuine Euclidean inner-ball containment. -/
theorem mem_of_latticeGrid_closedBall {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) {k : ℕ} (hk : 0 < k)
    (hgrid : (K : Set (EuclideanSpace ℝ (Fin n))) ∩ latticeGrid n k ⊆ L)
    {x : EuclideanSpace ℝ (Fin n)}
    (hball : closedBall x (Real.sqrt n / k) ⊆ (K : Set (EuclideanSpace ℝ (Fin n)))) :
    x ∈ L := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hcorner : e '' corners x k ⊆ (L : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro y ⟨q, hq, rfl⟩
    exact hgrid ⟨hball (corner_dist_le x hk hq), corner_mem_latticeGrid x hq⟩
  have hx : x ∈ convexHull ℝ (e '' corners x k) := by
    have himage := e.toLinearMap.image_convexHull (corners x k)
    change e '' convexHull ℝ (corners x k) = convexHull ℝ (e '' corners x k) at himage
    rw [← himage]
    exact ⟨(fun i ↦ x i), mem_convexHull_corners x hk, e.apply_symm_apply x⟩
  exact convexHull_min hcorner L.convex hx

/-- SGPT lma:latcvb, for the source open-ball inner shrinking; positive body volume is unnecessary. -/
theorem mem_of_latticeGrid_inner {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) {k : ℕ} (hk : 0 < k)
    (hgrid : (K : Set (EuclideanSpace ℝ (Fin n))) ∩ latticeGrid n k ⊆ L)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    (hball : ball x (Real.sqrt n / k) ⊆ (K : Set (EuclideanSpace ℝ (Fin n)))) :
    x ∈ L := by
  apply mem_of_latticeGrid_closedBall K L hk hgrid
  by_cases hr : Real.sqrt (n : ℝ) / k = 0
  · rw [hr, closedBall_zero]
    exact singleton_subset_iff.mpr hx
  · rw [← closure_ball x hr]
    exact closure_minimal hball K.isCompact.isClosed

/-- Exact source inner shrinking, with actual point membership and the actual Euclidean ball. -/
def innerShrinking {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ K ∧ ball x r ⊆ (K : Set (EuclideanSpace ℝ (Fin n)))}

/-- Full source lma:latcvb: actual standard-lattice inclusion contains the exact source sqrt(n)/k inner shrinking. -/
theorem innerShrinking_subset_of_latticeGrid {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) {k : ℕ} (hk : 0 < k)
    (hgrid : (K : Set (EuclideanSpace ℝ (Fin n))) ∩ latticeGrid n k ⊆ L) :
    innerShrinking K (Real.sqrt n / k) ⊆ (L : Set (EuclideanSpace ℝ (Fin n))) :=
  fun _ hx ↦ mem_of_latticeGrid_inner K L hk hgrid hx.1 hx.2

end SGPT.AlmostSemigroup.LatticeCube
