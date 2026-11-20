import SGPT.AlmostSemigroup.BodySlices
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace SGPT.AlmostSemigroup.BodyFubini
open Set Filter MeasureTheory
open scoped Topology

/-- Actual first-coordinate/rest Euclidean measurable equivalence. -/
def splitMeasureEquiv (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))))

/-- Exact product Lebesgue measure preservation of actual Euclidean head/tail coordinates. -/
theorem measurePreserving_splitMeasureEquiv (n : ℕ) :
    MeasurePreserving (splitMeasureEquiv n) := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin n))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (n + 1))))

/-- Actual body fibers of an actual closed product-space carrier. -/
def productFiber {V : Type*} (K : Set (ℝ × V)) (t : ℝ) : Set V :=
  {y | (t, y) ∈ K}

/-- The actual original Euclidean body fibers, with their actual Euclidean Lebesgue measure. -/
def euclideanFiber {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := productFiber (splitMeasureEquiv n '' K) t

/-- Genuine product-measure disintegration for an actual original measurable carrier. -/
theorem measure_eq_lintegral_productFiber {V : Type*}
    [MeasureSpace V] [SFinite (volume : Measure V)] {K : Set (ℝ × V)}
    (hK : MeasurableSet K) : volume K = ∫⁻ t : ℝ, volume (productFiber K t) :=
  Measure.prod_apply hK

/-- The genuine measurable head/tail map is exactly the already checked Euclidean geometric map. -/
theorem splitMeasureEquiv_eq_join_symm (n : ℕ) :
    (splitMeasureEquiv n : EuclideanSpace ℝ (Fin (n + 1)) → ℝ × EuclideanSpace ℝ (Fin n)) =
      (BodySlices.joinEuclidean n).symm := by
  funext x
  apply Prod.ext
  · rfl
  · ext j
    change x (Fin.succAbove 0 j) = x j.succ
    simp

/-- Actual fixed-body geometric splitting preserves its exact original Euclidean Lebesgue volume. -/
theorem measure_splitBody (n : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    volume (BodySlices.splitBody n K : Set (ℝ × EuclideanSpace ℝ (Fin n))) =
      volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  change volume ((BodySlices.joinEuclidean n).symm '' (K : Set _)) = _
  rw [← splitMeasureEquiv_eq_join_symm]
  rw [(splitMeasureEquiv n).image_eq_preimage_symm]
  exact ((measurePreserving_splitMeasureEquiv n).symm (splitMeasureEquiv n)).measure_preimage
    K.isCompact.measurableSet.nullMeasurableSet

/-- Exact first-coordinate fiber integral of the actual original Euclidean body. -/
theorem measure_eq_lintegral_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      ∫⁻ t : ℝ, volume (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t) := by
  rw [← measure_splitBody n K, measure_eq_lintegral_productFiber (BodySlices.splitBody n K).isCompact.measurableSet]
  congr 1

/-- Every genuine original fiber is compact, including the actual empty fibers outside the projection interval. -/
theorem isCompact_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) (t : ℝ) :
    IsCompact (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t) := by
  rw [euclideanFiber, splitMeasureEquiv_eq_join_symm]
  by_cases ht : t ∈ BodySlices.projectionSet (BodySlices.splitBody n K)
  · exact (BodySlices.slice (BodySlices.splitBody n K) ⟨t, ht⟩).isCompact
  · have hempty : productFiber ((BodySlices.joinEuclidean n).symm '' (K : Set _)) t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact ht ⟨(t, y), hy, rfl⟩
    rw [hempty]
    exact isCompact_empty

/-- Genuine original fiber-volume measurability comes from the actual closed product carrier. -/
theorem measurable_volume_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    Measurable (fun t : ℝ ↦ volume (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t)) := by
  have h := measurable_measure_prodMk_left (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (BodySlices.splitBody n K).isCompact.measurableSet
  change Measurable (fun t : ℝ ↦ volume (productFiber
    (BodySlices.splitBody n K : Set (ℝ × EuclideanSpace ℝ (Fin n))) t)) at h
  change Measurable (fun t : ℝ ↦ volume (productFiber
    ((BodySlices.joinEuclidean n).symm '' (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) t)) at h
  simpa only [euclideanFiber, splitMeasureEquiv_eq_join_symm] using h

/-- True original real fiber volumes are genuinely integrable because the actual original compact body has finite volume. -/
theorem integrable_real_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    Integrable (fun t : ℝ ↦ volume.real (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t)) := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_volume_euclideanFiber n K).aemeasurable
  rw [← measure_eq_lintegral_euclideanFiber n K]
  exact K.isCompact.measure_ne_top

/-- Exact genuine real-valued Euclidean slice-volume integral, without a Brunn--Minkowski assumption. -/
theorem real_volume_eq_integral_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      ∫ t : ℝ, volume.real (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t) := by
  have h := integral_toReal (μ := (volume : Measure ℝ)) (measurable_volume_euclideanFiber n K).aemeasurable
    (Eventually.of_forall (fun t ↦ (isCompact_euclideanFiber n K t).measure_lt_top))
  rw [← measure_eq_lintegral_euclideanFiber n K] at h
  exact h.symm

/-- The actual integration fiber on the original interval is exactly the already checked source slice body. -/
theorem euclideanFiber_eq_sourceSlice (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (t : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t =
      (BodySlices.euclideanSlice n K t : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [euclideanFiber, splitMeasureEquiv_eq_join_symm]
  rfl

/-- Genuine source Hausdorff slice continuity and actual volume continuity give true continuity of original slice volumes on the entire source interval. -/
theorem continuous_real_euclideanFiber (n : ℕ)
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    Continuous (fun t : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) ↦
      volume.real (euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t)) := by
  have h := (Hyperspace.continuous_euclidean_real_volume n).comp
    (BodySlices.continuous_euclideanSlice n K)
  convert h using 1
  funext t
  rw [euclideanFiber_eq_sourceSlice]
  rfl

end SGPT.AlmostSemigroup.BodyFubini
