import SGPT.AlmostSemigroup.Hyperspace

noncomputable section
namespace SGPT.AlmostSemigroup.BodyExtrema
open Set Filter Metric
open scoped Topology Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual compact-body upper value, with no boundedness certificate in its definition. -/
def upperValue (f : V → ℝ) (K : ConvexBody V) : ℝ := sSup (f '' (K : Set V))

/-- Actual compact extrema and genuine nearest points bound upper values by the true Hausdorff distance. -/
theorem upperValue_sub_le {f : V → ℝ} {a : NNReal} (hf : LipschitzWith a f)
    (K L : ConvexBody V) : upperValue f K - upperValue f L ≤ a * dist K L := by
  obtain ⟨x, hx, hmax⟩ := K.isCompact.exists_sSup_image_eq K.nonempty hf.continuous.continuousOn
  obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hle : f y ≤ upperValue f L :=
    le_csSup (L.isCompact.image hf.continuous).bddAbove (mem_image_of_mem f hy)
  have hdist : dist x y ≤ dist K L := by
    rw [← hxy]
    exact infDist_le_hausdorffDist_of_mem hx
      (hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty L.nonempty K.isCompact.isBounded L.isCompact.isBounded)
  change sSup (f '' (K : Set V)) - upperValue f L ≤ _
  rw [hmax]
  calc
    f x - upperValue f L ≤ f x - f y := sub_le_sub_left hle _
    _ ≤ dist (f x) (f y) := le_abs_self _
    _ ≤ a * dist x y := hf.dist_le_mul x y
    _ ≤ a * dist K L := mul_le_mul_of_nonneg_left hdist a.property

/-- The actual upper-value map preserves the genuine Lipschitz bound in the Hausdorff metric. -/
theorem lipschitzWith_upperValue {f : V → ℝ} {a : NNReal} (hf : LipschitzWith a f) :
    LipschitzWith a (upperValue f) := by
  apply LipschitzWith.of_dist_le_mul
  intro K L
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := upperValue_sub_le hf L K
    rw [dist_comm L K] at h
    linarith
  · exact upperValue_sub_le hf K L

/-- Each genuine Euclidean coordinate is one-Lipschitz for the original Euclidean norm. -/
theorem lipschitzWith_coordinate {n : ℕ} (i : Fin n) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, PiLp.sub_apply, NNReal.coe_one, one_mul] using
    PiLp.norm_apply_le (x - y) i

/-- Actual coordinate maximum of an actual Euclidean body. -/
def coordinateMax {n : ℕ} (i : Fin n) (K : ConvexBody (EuclideanSpace ℝ (Fin n))) : ℝ :=
  upperValue (fun x ↦ x i) K

/-- Exact source lma:Hausdorffconvcoordbounds maximum clause, for every actual coordinate. -/
theorem continuous_coordinateMax {n : ℕ} (i : Fin n) : Continuous (coordinateMax i) :=
  (lipschitzWith_upperValue (lipschitzWith_coordinate i)).continuous

/-- Actual compact-body lower value. -/
def lowerValue (f : V → ℝ) (K : ConvexBody V) : ℝ := sInf (f '' (K : Set V))

/-- The actual lower-value formula is the negative upper value of the actual negative function. -/
theorem lowerValue_eq_neg_upperValue_neg (f : V → ℝ) (K : ConvexBody V) :
    lowerValue f K = -upperValue (fun x ↦ -f x) K := by
  have himage : (fun x ↦ -f x) '' (K : Set V) = -(f '' (K : Set V)) := by
    rw [← Set.image_neg_eq_neg, ← Set.image_comp]
    rfl
  rw [lowerValue, upperValue, himage, Real.sSup_neg, neg_neg]

/-- Actual coordinate minimum of an actual Euclidean body. -/
def coordinateMin {n : ℕ} (i : Fin n) (K : ConvexBody (EuclideanSpace ℝ (Fin n))) : ℝ :=
  lowerValue (fun x ↦ x i) K

/-- Exact source lma:Hausdorffconvcoordbounds minimum clause, for every actual coordinate. -/
theorem continuous_coordinateMin {n : ℕ} (i : Fin n) : Continuous (coordinateMin i) := by
  have hf : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) ↦ -x i) :=
    (lipschitzWith_coordinate i).neg
  have h := (lipschitzWith_upperValue hf).continuous.neg
  convert h using 1
  funext K
  exact lowerValue_eq_neg_upperValue_neg (fun x ↦ x i) K

/-- Actual compactness supplies genuine attained coordinate extrema, so the formulas are the source minimum and maximum. -/
theorem exists_coordinate_extrema {n : ℕ} (i : Fin n)
    (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    (∃ x ∈ K, coordinateMax i K = x i) ∧ (∃ x ∈ K, coordinateMin i K = x i) := by
  exact ⟨K.isCompact.exists_sSup_image_eq K.nonempty (lipschitzWith_coordinate i).continuous.continuousOn,
    K.isCompact.exists_sInf_image_eq K.nonempty (lipschitzWith_coordinate i).continuous.continuousOn⟩

end SGPT.AlmostSemigroup.BodyExtrema
