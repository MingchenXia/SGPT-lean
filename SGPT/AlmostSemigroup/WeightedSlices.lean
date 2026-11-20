import SGPT.AlmostSemigroup.BodyFubini
import SGPT.AlmostSemigroup.Minkowski

noncomputable section
namespace SGPT.AlmostSemigroup.WeightedSlices
open Set Filter MeasureTheory
open scoped Topology Pointwise
variable {n : ℕ}
local notation "Body" => ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))

/-- The actual original Euclidean fiber is the genuine head--tail reconstruction preimage. -/
theorem mem_euclideanFiber_iff (K : Body) (x : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) x ↔
      BodySlices.joinEuclidean n (x, y) ∈ K := by
  rw [BodyFubini.euclideanFiber, BodyFubini.splitMeasureEquiv_eq_join_symm]
  change (x, y) ∈ (BodySlices.joinEuclidean n).symm '' (K : Set _) ↔ _
  rw [ContinuousLinearEquiv.image_symm_eq_preimage]
  rfl

/-- The actual canonical head--tail linear map preserves true weighted reconstructed points. -/
theorem join_weighted (a b x y : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    BodySlices.joinEuclidean n (a * x + b * y, a • u + b • v) =
      a • BodySlices.joinEuclidean n (x, u) + b • BodySlices.joinEuclidean n (y, v) := by
  rw [← map_smul, ← map_smul, ← map_add]
  rfl

/-- Actual original member witnesses give an actual member of the genuine weighted sum fiber. -/
theorem weighted_mem_euclideanFiber (K L : Body) (a b x y : ℝ)
    {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) x)
    (hv : v ∈ BodyFubini.euclideanFiber (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) y) :
    a • u + b • v ∈ BodyFubini.euclideanFiber
      ((a • K + b • L : Body) : Set (EuclideanSpace ℝ (Fin (n + 1)))) (a * x + b * y) := by
  rw [mem_euclideanFiber_iff, join_weighted]
  change a • BodySlices.joinEuclidean n (x, u) + b • BodySlices.joinEuclidean n (y, v) ∈
    (a • (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) +
      b • (L : Set (EuclideanSpace ℝ (Fin (n + 1)))))
  exact Set.mem_add.mpr ⟨_, Set.mem_smul_set.mpr ⟨_, (mem_euclideanFiber_iff K x u).mp hu, rfl⟩,
    _, Set.mem_smul_set.mpr ⟨_, (mem_euclideanFiber_iff L y v).mp hv, rfl⟩, rfl⟩

/-- Genuine original slice nonemptiness produces actual weighted coordinate membership in the original sum projection interval. -/
theorem weighted_coordinate_mem_interval (K L : Body) (a b : ℝ)
    (x : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K))
    (y : Icc (BodyExtrema.coordinateMin 0 L) (BodyExtrema.coordinateMax 0 L)) :
    a * (x : ℝ) + b * (y : ℝ) ∈
      Icc (BodyExtrema.coordinateMin 0 (a • K + b • L))
        (BodyExtrema.coordinateMax 0 (a • K + b • L)) := by
  obtain ⟨u, hu⟩ := (BodySlices.euclideanSlice n K x).nonempty
  obtain ⟨v, hv⟩ := (BodySlices.euclideanSlice n L y).nonempty
  have hu' : u ∈ BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) x := by
    rw [BodyFubini.euclideanFiber_eq_sourceSlice n K x]
    exact hu
  have hv' : v ∈ BodyFubini.euclideanFiber (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) y := by
    rw [BodyFubini.euclideanFiber_eq_sourceSlice n L y]
    exact hv
  have hm := weighted_mem_euclideanFiber K L a b x y hu' hv'
  rw [BodyFubini.euclideanFiber, BodyFubini.splitMeasureEquiv_eq_join_symm] at hm
  have hp : a * (x : ℝ) + b * (y : ℝ) ∈ BodySlices.projectionSet
      (BodySlices.splitBody n (a • K + b • L)) :=
    ⟨(a * (x : ℝ) + b * (y : ℝ), a • u + b • v), hm, rfl⟩
  rwa [BodySlices.projectionSet_splitBody_eq_Icc] at hp

/-- The actual weighted sum of the original two source slice bodies is genuinely contained in the original weighted-body fiber. -/
theorem weighted_sourceSlice_subset_euclideanFiber (K L : Body) (a b : ℝ)
    (x : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K))
    (y : Icc (BodyExtrema.coordinateMin 0 L) (BodyExtrema.coordinateMax 0 L)) :
    ((a • BodySlices.euclideanSlice n K x + b • BodySlices.euclideanSlice n L y :
      ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) ⊆
      BodyFubini.euclideanFiber ((a • K + b • L : Body) : Set (EuclideanSpace ℝ (Fin (n + 1))))
        (a * (x : ℝ) + b * (y : ℝ)) := by
  intro z hz
  change z ∈ (a • (BodySlices.euclideanSlice n K x : Set (EuclideanSpace ℝ (Fin n))) +
    b • (BodySlices.euclideanSlice n L y : Set (EuclideanSpace ℝ (Fin n)))) at hz
  obtain ⟨u', hu', v', hv', huv⟩ := Set.mem_add.mp hz
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hu'
  obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hv'
  rw [← huv]
  apply weighted_mem_euclideanFiber K L a b x y
  · rw [BodyFubini.euclideanFiber_eq_sourceSlice n K x]
    exact hu
  · rw [BodyFubini.euclideanFiber_eq_sourceSlice n L y]
    exact hv

end SGPT.AlmostSemigroup.WeightedSlices
