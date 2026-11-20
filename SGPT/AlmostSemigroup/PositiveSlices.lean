import SGPT.AlmostSemigroup.BodyFubini
import SGPT.AlmostSemigroup.ConvexIntersection

noncomputable section
namespace SGPT.AlmostSemigroup.PositiveSlices
open Set Filter MeasureTheory
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A genuine ordinary body interior projects to an actual nondegenerate attained interval. -/
theorem projection_extrema_lt_of_nonempty_interior (K : ConvexBody (ℝ × V))
    (hint : (interior (K : Set (ℝ × V))).Nonempty) :
    sInf (BodySlices.projectionSet K) < sSup (BodySlices.projectionSet K) := by
  have h : (interior (BodySlices.projectionSet K)).Nonempty :=
    (hint.image Prod.fst).mono (isOpenMap_fst.image_interior_subset (K : Set (ℝ × V)))
  rw [BodySlices.projectionSet_eq_Icc K, interior_Icc] at h
  exact nonempty_Ioo.mp h

/-- Original Euclidean positive volume gives actual interior in the genuine split coordinates. -/
theorem interior_splitBody_nonempty_of_volume_pos {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    (interior (BodySlices.splitBody n K : Set (ℝ × EuclideanSpace ℝ (Fin n)))).Nonempty := by
  have hint := ConvexIntersection.interior_nonempty_of_measure_pos volume K.convex hK
  change (interior ((BodySlices.joinEuclidean n).symm.toHomeomorph ''
    (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))).Nonempty
  rw [← (BodySlices.joinEuclidean n).symm.toHomeomorph.image_interior]
  exact hint.image _

/-- Positive actual source volume forces distinct actual coordinate extrema. -/
theorem coordinateMin_lt_coordinateMax_of_volume_pos {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    BodyExtrema.coordinateMin 0 K < BodyExtrema.coordinateMax 0 K := by
  have h := projection_extrema_lt_of_nonempty_interior (BodySlices.splitBody n K)
    (interior_splitBody_nonempty_of_volume_pos K hK)
  simpa only [BodySlices.projectionSet_splitBody, BodyExtrema.coordinateMin,
    BodyExtrema.coordinateMax, BodyExtrema.lowerValue, BodyExtrema.upperValue] using h

/-- Genuine actual interior points and attained projection endpoints give an actual interior point in every original strict-interior fiber. -/
theorem exists_interior_point_with_firstCoordinate (K : ConvexBody (ℝ × V))
    (hint : (interior (K : Set (ℝ × V))).Nonempty) {t : ℝ}
    (ht : t ∈ Ioo (sInf (BodySlices.projectionSet K)) (sSup (BodySlices.projectionSet K))) :
    ∃ y : V, (t, y) ∈ interior (K : Set (ℝ × V)) := by
  obtain ⟨p, hp⟩ := hint
  let a := sInf (BodySlices.projectionSet K)
  let b := sSup (BodySlices.projectionSet K)
  have hc := BodySlices.isCompact_projectionSet K
  have hn := BodySlices.nonempty_projectionSet K
  obtain ⟨z, hz, hza⟩ := hc.isClosed.csInf_mem hn hc.bddBelow
  obtain ⟨w, hw, hwb⟩ := hc.isClosed.csSup_mem hn hc.bddAbove
  have ha : z.1 = a := hza
  have hb : w.1 = b := hwb
  rcases lt_trichotomy t p.1 with htp | htp | hpt
  · let r : ℝ := (t - a) / (p.1 - a)
    have hpa : 0 < p.1 - a := by linarith [ht.1]
    have hr : 0 < r := div_pos (sub_pos.mpr ht.1) hpa
    have hr1 : r ≤ 1 := (div_le_one hpa).mpr (by linarith)
    have hq := K.convex.combo_interior_closure_mem_interior hp (subset_closure hz)
      hr (by linarith : 0 ≤ 1 - r) (by ring : r + (1 - r) = 1)
    refine ⟨r • p.2 + (1 - r) • z.2, ?_⟩
    have hf : r * p.1 + (1 - r) * z.1 = t := by
      rw [ha]
      dsimp only [r]
      field_simp [ne_of_gt hpa]
      ring
    have hpair : r • p + (1 - r) • z = (t, r • p.2 + (1 - r) • z.2) := by
      apply Prod.ext
      · exact hf
      · rfl
    rwa [hpair] at hq
  · exact ⟨p.2, by simpa only [htp, Prod.mk.eta] using hp⟩
  · let r : ℝ := (b - t) / (b - p.1)
    have hpb : 0 < b - p.1 := by linarith [ht.2]
    have hr : 0 < r := div_pos (sub_pos.mpr ht.2) hpb
    have hr1 : r ≤ 1 := (div_le_one hpb).mpr (by linarith)
    have hq := K.convex.combo_interior_closure_mem_interior hp (subset_closure hw)
      hr (by linarith : 0 ≤ 1 - r) (by ring : r + (1 - r) = 1)
    refine ⟨r • p.2 + (1 - r) • w.2, ?_⟩
    have hf : r * p.1 + (1 - r) * w.1 = t := by
      rw [hb]
      dsimp only [r]
      field_simp [ne_of_gt hpb]
      ring
    have hpair : r • p + (1 - r) • w = (t, r • p.2 + (1 - r) • w.2) := by
      apply Prod.ext
      · exact hf
      · rfl
    rwa [hpair] at hq

/-- The actual fixed-coordinate continuous embedding pulls back a genuine original interior point to an actual fiber interior neighborhood. -/
theorem interior_productFiber_nonempty (K : ConvexBody (ℝ × V))
    (hint : (interior (K : Set (ℝ × V))).Nonempty) {t : ℝ}
    (ht : t ∈ Ioo (sInf (BodySlices.projectionSet K)) (sSup (BodySlices.projectionSet K))) :
    (interior (BodyFubini.productFiber (K : Set (ℝ × V)) t)).Nonempty := by
  obtain ⟨y, hy⟩ := exists_interior_point_with_firstCoordinate K hint ht
  let U : Set V := (fun z ↦ (t, z)) ⁻¹' interior (K : Set (ℝ × V))
  have hU : IsOpen U := isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  have hsub : U ⊆ BodyFubini.productFiber (K : Set (ℝ × V)) t := by
    intro z hz
    change (t, z) ∈ (K : Set (ℝ × V))
    exact interior_subset (show (t, z) ∈ interior (K : Set (ℝ × V)) from hz)
  refine ⟨y, interior_mono hsub ?_⟩
  rwa [hU.interior_eq]

/-- Actual original positive body volume produces genuine positive original slice volume at every strict-interior projection parameter. -/
theorem euclideanFiber_volume_pos {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : t ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    0 < volume (BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t) := by
  have hint := interior_splitBody_nonempty_of_volume_pos K hK
  have ht' : t ∈ Ioo (sInf (BodySlices.projectionSet (BodySlices.splitBody n K)))
      (sSup (BodySlices.projectionSet (BodySlices.splitBody n K))) := by
    rw [BodySlices.projectionSet_splitBody]
    exact ht
  have h := interior_productFiber_nonempty (BodySlices.splitBody n K) hint ht'
  have hpos := Measure.measure_pos_of_nonempty_interior volume h
  change 0 < volume (BodyFubini.productFiber
    ((BodySlices.joinEuclidean n).symm '' (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) t) at hpos
  simpa only [BodyFubini.euclideanFiber, BodyFubini.splitMeasureEquiv_eq_join_symm] using hpos

/-- The actual finite real volume of each genuine original slice. -/
def density {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) (t : ℝ) : ℝ :=
  volume.real (BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t)

theorem density_nonneg {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (t : ℝ) : 0 ≤ density K t := ENNReal.toReal_nonneg

/-- Genuine checked slice/volume continuity supplies actual closed-interval density continuity. -/
theorem continuousOn_density {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    ContinuousOn (density K) (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr (BodyFubini.continuous_real_euclideanFiber n K)

/-- Genuine finite original fiber measure gives strictly positive real density at every interior parameter. -/
theorem density_pos {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : t ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    0 < density K t :=
  ENNReal.toReal_pos (ne_of_gt (euclideanFiber_volume_pos K hK ht))
    (BodyFubini.isCompact_euclideanFiber n K t).measure_ne_top

/-- An original coordinate outside the actual attained interval has genuinely empty fiber. -/
theorem euclideanFiber_eq_empty_of_not_mem_interval {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) {t : ℝ}
    (ht : t ∉ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    BodyFubini.euclideanFiber (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) t = ∅ := by
  have ht' : t ∉ BodySlices.projectionSet (BodySlices.splitBody n K) := by
    rwa [BodySlices.projectionSet_splitBody_eq_Icc]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [BodyFubini.euclideanFiber, BodyFubini.splitMeasureEquiv_eq_join_symm] at hy
  exact ht' ⟨(t, y), hy, rfl⟩

theorem density_eq_zero_of_not_mem_interval {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) {t : ℝ}
    (ht : t ∉ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    density K t = 0 := by
  simp [density, euclideanFiber_eq_empty_of_not_mem_interval K ht]

/-- The actual interval density mass equals the original finite Euclidean body volume. -/
theorem integral_density_eq_volume {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    (∫ t in BodyExtrema.coordinateMin 0 K..BodyExtrema.coordinateMax 0 K, density K t) =
      volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hle : BodyExtrema.coordinateMin 0 K ≤ BodyExtrema.coordinateMax 0 K := by
    have h := (BodySlices.nonempty_projectionSet (BodySlices.splitBody n K))
    rw [BodySlices.projectionSet_splitBody_eq_Icc] at h
    exact nonempty_Icc.mp h
  rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ density_eq_zero_of_not_mem_interval K ht)]
  exact (BodyFubini.real_volume_eq_integral_euclideanFiber n K).symm

end SGPT.AlmostSemigroup.PositiveSlices
