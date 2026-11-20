import SGPT.AlmostSemigroup.Class
import SGPT.AlmostSemigroup.Hyperspace
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Actual continuous almost-semigroup body extension

The actual source discrepancy is the true L1 distance of body indicators.
The complete-space extension along the actual dense full-semigroup locus
lies in genuine compact positive-volume cutoff images. Their genuine
continuous inverses produce the continuous Euclidean Hausdorff body map
and the exact source volume identity, completing `thm:Okocontapp`.
-/

noncomputable section
namespace SGPT.AlmostSemigroup.OkounkovExtension
open Set Filter MeasureTheory Metric
open scoped Topology symmDiff
open Okounkov Class

/-- Genuine canonical Euclidean-coordinate transport preserves the source lattice-normalized Lebesgue volume. -/
theorem volume_euclidean_image {n : ℕ} {K : Set (Fin n → ℝ)} (hK : MeasurableSet K) :
    volume.real ((EuclideanSpace.equiv (Fin n) ℝ).symm '' K) = volume.real K := by
  change volume.real ((EuclideanSpace.equiv (Fin n) ℝ).toEquiv.symm '' K) = volume.real K
  rw [(EuclideanSpace.equiv (Fin n) ℝ).toEquiv.image_symm_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin n)).measureReal_preimage hK.nullMeasurableSet

/-- The actual Euclidean source body has exactly the actual full-semigroup source volume. -/
theorem volume_bodyMap {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    volume.real (bodyMap S : Set (EuclideanSpace ℝ (Fin n))) = S.val.volume := by
  have hK := isCompact_body C S.semigroup S.semigroup_le_source
    (nonempty_of_generatedGroup_eq_top _ S.generatedGroup_eq_top)
  change volume.real ((EuclideanSpace.equiv (Fin n) ℝ).symm '' body S.semigroup) = S.val.volume
  rw [volume_euclidean_image hK.measurableSet]
  rw [← S.sourceSubset_semigroup]
  exact (BodyGeometry.volume_source_eq_body C S.semigroup S.semigroup_le_source
    S.generatedGroup_eq_top).symm

/-- Genuine body indicator on the actual Euclidean ambient space. -/
def bodyIndicatorFunction {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → ℝ := (K : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ 1)

/-- Genuine compact-body finite measure supplies actual indicator integrability. -/
theorem integrable_bodyIndicatorFunction {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    Integrable (bodyIndicatorFunction K) volume :=
  (integrable_indicator_iff K.isCompact.measurableSet).mpr
    (integrableOn_const (K.isCompact.measure_ne_top (μ := volume)))

/-- Actual body indicator as an actual integrable-function class. -/
def bodyIndicator {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    Lp ℝ 1 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (integrable_bodyIndicatorFunction K).toL1 (bodyIndicatorFunction K)

/-- Actual indicator distance is the actual finite Lebesgue symmetric difference. -/
theorem edist_bodyIndicator {n : ℕ} (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    edist (bodyIndicator K) (bodyIndicator L) =
      volume ((K : Set (EuclideanSpace ℝ (Fin n))) ∆ (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [bodyIndicator, bodyIndicator, Integrable.edist_toL1_toL1]
  have heq : (fun x ↦ edist (bodyIndicatorFunction K x) (bodyIndicatorFunction L x)) =
      ((K : Set (EuclideanSpace ℝ (Fin n))) ∆ (L : Set (EuclideanSpace ℝ (Fin n)))).indicator
        (fun _ ↦ (1 : ENNReal)) := by
    funext x
    by_cases hxK : x ∈ K <;> by_cases hxL : x ∈ L <;>
      simp [bodyIndicatorFunction, hxK, hxL, edist_dist, Real.dist_eq,
        Set.mem_symmDiff, ENNReal.ofReal_one]
  rw [heq, lintegral_indicator (K.isCompact.measurableSet.symmDiff L.isCompact.measurableSet)]
  simp

/-- Exact real L1 body-indicator distance. -/
theorem dist_bodyIndicator {n : ℕ} (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    dist (bodyIndicator K) (bodyIndicator L) =
      volume.real ((K : Set (EuclideanSpace ℝ (Fin n))) ∆ (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [dist_edist, edist_bodyIndicator]
  rfl

/-- Actual indicator norm is exactly actual body volume, including dimension zero. -/
theorem norm_bodyIndicator {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    ‖bodyIndicator K‖ = volume.real (K : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [bodyIndicator, Integrable.norm_toL1]
  have heq : (fun x ↦ edist (bodyIndicatorFunction K x) 0) =
      (K : Set (EuclideanSpace ℝ (Fin n))).indicator (fun _ ↦ (1 : ENNReal)) := by
    funext x
    by_cases hx : x ∈ K <;>
      simp [bodyIndicatorFunction, hx, edist_dist]
  rw [heq, lintegral_indicator K.isCompact.measurableSet]
  simp [measureReal_def]

/-- The genuine finite-body measure identity used by the original source discrepancy formula. -/
theorem volume_symmDiff_eq {n : ℕ} (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    volume.real ((K : Set (EuclideanSpace ℝ (Fin n))) ∆ (L : Set (EuclideanSpace ℝ (Fin n)))) =
      volume.real (K : Set (EuclideanSpace ℝ (Fin n))) +
      volume.real (L : Set (EuclideanSpace ℝ (Fin n))) -
      2 * volume.real ((K : Set (EuclideanSpace ℝ (Fin n))) ∩ (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  have hK := K.isCompact.measure_ne_top (μ := volume)
  have hL := L.isCompact.measure_ne_top (μ := volume)
  have hleft := measureReal_sdiff_add_inter L.isCompact.measurableSet hK
  have hright := measureReal_sdiff_add_inter K.isCompact.measurableSet hL
  rw [inter_comm] at hright
  rw [measureReal_symmDiff_eq K.isCompact.measurableSet L.isCompact.measurableSet hK hL]
  linarith

/-- Genuine canonical transport identifies the actual common source body volume. -/
theorem volume_bodyMap_inter {n : ℕ} {C : AdmissibleCone n} (S T : FullSemigroup C) :
    volume.real ((bodyMap S : Set (EuclideanSpace ℝ (Fin n))) ∩ (bodyMap T : Set (EuclideanSpace ℝ (Fin n)))) =
      (Intersection.intersectionSubset C S.semigroup T.semigroup S.semigroup_le_source).volume := by
  have hK := isCompact_body C S.semigroup S.semigroup_le_source
    (nonempty_of_generatedGroup_eq_top _ S.generatedGroup_eq_top)
  have hL := isCompact_body C T.semigroup T.semigroup_le_source
    (nonempty_of_generatedGroup_eq_top _ T.generatedGroup_eq_top)
  change volume.real (((EuclideanSpace.equiv (Fin n) ℝ).symm '' body S.semigroup) ∩
    ((EuclideanSpace.equiv (Fin n) ℝ).symm '' body T.semigroup)) = _
  rw [← Set.image_inter (EuclideanSpace.equiv (Fin n) ℝ).symm.injective,
    volume_euclidean_image (hK.inter hL).measurableSet]
  exact (Intersection.volume_intersection_eq C S.semigroup T.semigroup S.semigroup_le_source
    T.semigroup_le_source S.generatedGroup_eq_top T.generatedGroup_eq_top).symm

/-- The actual source discrepancy is exactly the distance between genuine body-indicator classes. -/
theorem dist_fullIndicator {n : ℕ} {C : AdmissibleCone n} (S T : FullSemigroup C) :
    dist (bodyIndicator (bodyMap S)) (bodyIndicator (bodyMap T)) = dist S T := by
  rw [dist_bodyIndicator, volume_symmDiff_eq, volume_bodyMap, volume_bodyMap, volume_bodyMap_inter]
  have h := Intersection.distance_eq_volumes C S.semigroup T.semigroup
    S.semigroup_le_source T.semigroup_le_source S.generatedGroup_eq_top T.generatedGroup_eq_top
  rw [S.sourceSubset_semigroup, T.sourceSubset_semigroup] at h
  exact h.symm

/-- The original source full locus embeds isometrically into the genuine L1 space of actual body indicators. -/
theorem isometry_fullIndicator {n : ℕ} (C : AdmissibleCone n) :
    Isometry (fun S : FullSemigroup C ↦ bodyIndicator (bodyMap S)) :=
  Isometry.of_dist_eq dist_fullIndicator

/-- Actual L1 indicator distance is exactly the actual integral of indicator differences. -/
theorem dist_bodyIndicator_eq_integral_norm {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    dist (bodyIndicator K) (bodyIndicator L) =
      ∫ x, ‖bodyIndicatorFunction K x - bodyIndicatorFunction L x‖ ∂volume := by
  rw [dist_eq_norm]
  change ‖(integrable_bodyIndicatorFunction K).toL1 (bodyIndicatorFunction K) -
    (integrable_bodyIndicatorFunction L).toL1 (bodyIndicatorFunction L)‖ = _
  rw [← Integrable.toL1_sub, Integrable.norm_toL1_eq_lintegral_enorm]
  exact (integral_norm_eq_lintegral_enorm
    ((integrable_bodyIndicatorFunction K).sub (integrable_bodyIndicatorFunction L)).aestronglyMeasurable).symm

/-- Actual Hausdorff convergence gives genuine L1 convergence of the actual body indicators. -/
theorem tendsto_bodyIndicator {n : ℕ}
    {u : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
    {K : ConvexBody (EuclideanSpace ℝ (Fin n))} (hu : Tendsto u atTop (𝓝 K)) :
    Tendsto (fun i ↦ bodyIndicator (u i)) atTop (𝓝 (bodyIndicator K)) := by
  obtain ⟨B, hB, hKB, huB⟩ := Hyperspace.exists_compact_containing_sequence hu
  have hBi : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrable_indicator_iff hB.measurableSet).mpr
      (integrableOn_const (hB.measure_ne_top (μ := volume)))
  have hmeas (i : ℕ) : AEStronglyMeasurable
      (fun x ↦ ‖bodyIndicatorFunction (u i) x - bodyIndicatorFunction K x‖) volume :=
    ((integrable_bodyIndicatorFunction (u i)).aestronglyMeasurable.sub
      (integrable_bodyIndicatorFunction K).aestronglyMeasurable).norm
  have hbound (i : ℕ) : ∀ᵐ x ∂volume,
      ‖‖bodyIndicatorFunction (u i) x - bodyIndicatorFunction K x‖‖ ≤
        B.indicator (fun _ ↦ (1 : ℝ)) x := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hxB : x ∈ B
    · by_cases hxi : x ∈ u i <;> by_cases hxK : x ∈ K <;>
        simp [bodyIndicatorFunction, hxi, hxK, hxB]
    · have hxi : x ∉ u i := fun hi ↦ hxB (huB i hi)
      have hxK : x ∉ K := fun hi ↦ hxB (hKB hi)
      simp [bodyIndicatorFunction, hxi, hxK, hxB]
  have hnull : volume (frontier (K : Set (EuclideanSpace ℝ (Fin n)))) = 0 :=
    K.convex.addHaar_frontier volume
  have hpoint : ∀ᵐ x ∂volume, Tendsto
      (fun i ↦ ‖bodyIndicatorFunction (u i) x - bodyIndicatorFunction K x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    have h := ((Hyperspace.tendsto_indicator_of_not_mem_frontier hu hx).sub_const
      (bodyIndicatorFunction K x)).norm
    simpa only [bodyIndicatorFunction, sub_self, norm_zero] using h
  have ht := tendsto_integral_of_dominated_convergence
    (B.indicator (fun _ ↦ (1 : ℝ))) hmeas hBi hbound hpoint
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_bodyIndicator_eq_integral_norm, integral_zero] using ht

/-- The actual Hausdorff body-to-indicator map is continuous for the genuine L1 target. -/
theorem continuous_bodyIndicator (n : ℕ) :
    Continuous (bodyIndicator (n := n)) := by
  apply SeqContinuous.continuous
  intro u K hu
  exact tendsto_bodyIndicator hu

/-- The genuine compact Euclidean height-one section of the original admissible source cone. -/
def sourceBodyAmbient {n : ℕ} (C : AdmissibleCone n) : Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm '' heightOne C.cone

/-- Original source cone hypotheses produce the actual compact ambient body bound. -/
theorem isCompact_sourceBodyAmbient {n : ℕ} (C : AdmissibleCone n) :
    IsCompact (sourceBodyAmbient C) :=
  (isCompact_heightOne C.cone C.closed C.nonnegativeHeight C.zeroHeight).image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous

/-- Each actual full source body lies in the original actual compact height-one section. -/
theorem bodyMap_subset_sourceBodyAmbient {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    (bodyMap S : Set (EuclideanSpace ℝ (Fin n))) ⊆ sourceBodyAmbient C := by
  apply image_mono
  intro x hx
  exact closedCone_subset_source C S.semigroup S.semigroup_le_source
    (nonempty_of_generatedGroup_eq_top _ S.generatedGroup_eq_top) hx

/-- The actual compact ambient family with a genuine positive volume cutoff. -/
def bodyCutoff {n : ℕ} (C : AdmissibleCone n) (δ : ℝ) :
    Set (ConvexBody (EuclideanSpace ℝ (Fin n))) :=
  {K | (K : Set (EuclideanSpace ℝ (Fin n))) ⊆ sourceBodyAmbient C} ∩
  {K | δ ≤ volume.real (K : Set (EuclideanSpace ℝ (Fin n)))}

/-- Actual cutoff families are genuinely compact from actual body volume continuity. -/
theorem isCompact_bodyCutoff {n : ℕ} (C : AdmissibleCone n) (δ : ℝ) : IsCompact (bodyCutoff C δ) :=
  (Hyperspace.isCompact_bodies_subset (isCompact_sourceBodyAmbient C)).inter_right
    (isClosed_le continuous_const (Hyperspace.continuous_euclidean_real_volume n))

/-- Actual source-volume cutoffs place the actual source body in this actual compact family. -/
theorem bodyMap_mem_bodyCutoff {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C)
    {δ : ℝ} (hδ : δ ≤ S.val.volume) : bodyMap S ∈ bodyCutoff C δ :=
  ⟨bodyMap_subset_sourceBodyAmbient S, by
    change δ ≤ volume.real (bodyMap S : Set (EuclideanSpace ℝ (Fin n)))
    rwa [volume_bodyMap]⟩

/-- The inverse canonical coordinate transport preserves the actual Euclidean Lebesgue volume. -/
theorem volume_coordinate_image {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) :
    volume.real ((EuclideanSpace.equiv (Fin n) ℝ) '' K) = volume.real K := by
  change volume.real ((EuclideanSpace.equiv (Fin n) ℝ).toEquiv '' K) = volume.real K
  rw [(EuclideanSpace.equiv (Fin n) ℝ).toEquiv.image_eq_preimage_symm]
  exact (PiLp.volume_preserving_toLp (Fin n)).measureReal_preimage hK.nullMeasurableSet

/-- Actual positive measure of a closed convex set gives genuine nonempty ordinary interior. -/
theorem interior_nonempty_of_positive_volume {n : ℕ} {K : Set (Fin n → ℝ)}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hpositive : 0 < volume.real K) :
    (interior K).Nonempty := by
  by_contra hne
  have hInt : interior K = ∅ := not_nonempty_iff_eq_empty.mp hne
  have hnull := Counting.null_frontier_convex hconvex
  rw [hclosed.frontier_eq, hInt, sdiff_empty] at hnull
  have hz : volume.real K = 0 := by rw [measureReal_def, hnull, ENNReal.toReal_zero]
  linarith

/-- Genuine Euclidean positive-body rigidity reuses the finished coordinate measure-rigidity proof. -/
theorem body_subset_of_volume_inter_eq {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hpositive : 0 < volume.real (K : Set (EuclideanSpace ℝ (Fin n))))
    (heq : volume.real ((K : Set (EuclideanSpace ℝ (Fin n))) ∩ (L : Set (EuclideanSpace ℝ (Fin n)))) =
      volume.real (K : Set (EuclideanSpace ℝ (Fin n)))) : (K : Set (EuclideanSpace ℝ (Fin n))) ⊆ L := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hK := K.isCompact.image e.continuous
  have hL := L.isCompact.image e.continuous
  have hconv : Convex ℝ (e '' (K : Set (EuclideanSpace ℝ (Fin n)))) :=
    K.convex.linear_image e.toLinearMap
  have hpos : 0 < volume.real (e '' (K : Set (EuclideanSpace ℝ (Fin n)))) := by
    rwa [volume_coordinate_image K.isCompact.measurableSet]
  have hinter : volume.real ((e '' (K : Set (EuclideanSpace ℝ (Fin n)))) ∩
      (e '' (L : Set (EuclideanSpace ℝ (Fin n))))) =
      volume.real (e '' (K : Set (EuclideanSpace ℝ (Fin n)))) := by
    rw [← Set.image_inter e.injective,
      volume_coordinate_image (K.isCompact.inter L.isCompact).measurableSet,
      volume_coordinate_image K.isCompact.measurableSet]
    exact heq
  have hsub := Intersection.subset_of_volume_inter_eq hK hL.isClosed hconv
    (interior_nonempty_of_positive_volume hK.isClosed hconv hpos) hinter
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hsub (mem_image_of_mem e hx)
  exact e.injective hxy ▸ hy

/-- Actual body indicators determine every genuine positive-volume compact convex body. -/
theorem body_eq_of_indicator_eq_of_volume_pos {n : ℕ}
    (K L : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hK : 0 < volume.real (K : Set (EuclideanSpace ℝ (Fin n))))
    (hL : 0 < volume.real (L : Set (EuclideanSpace ℝ (Fin n))))
    (heq : bodyIndicator K = bodyIndicator L) : K = L := by
  have hnull : volume ((K : Set (EuclideanSpace ℝ (Fin n))) ∆
      (L : Set (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [← edist_bodyIndicator, heq, edist_self]
  have hnullK : volume ((K : Set (EuclideanSpace ℝ (Fin n))) \ L) = 0 :=
    measure_mono_null (fun _ hx ↦ Or.inl hx) hnull
  have hnullL : volume ((L : Set (EuclideanSpace ℝ (Fin n))) \ K) = 0 := by
    exact measure_mono_null (fun _ hx ↦ Or.inr hx) hnull
  have hmeasureK := measure_sdiff_add_inter (K : Set (EuclideanSpace ℝ (Fin n))) L.isCompact.measurableSet (μ := volume)
  have hmeasureL := measure_sdiff_add_inter (L : Set (EuclideanSpace ℝ (Fin n))) K.isCompact.measurableSet (μ := volume)
  rw [hnullK, zero_add] at hmeasureK
  rw [hnullL, zero_add] at hmeasureL
  apply ConvexBody.ext
  apply subset_antisymm
  · exact body_subset_of_volume_inter_eq K L hK (congrArg ENNReal.toReal hmeasureK)
  · exact body_subset_of_volume_inter_eq L K hL (congrArg ENNReal.toReal hmeasureL)

/-- Genuine compact positive-volume cutoff bodies embed closedly into their actual L1 indicators. -/
theorem isClosedEmbedding_cutoffIndicator {n : ℕ} (C : AdmissibleCone n) (δ : ℝ)
    (hδ : 0 < δ) : Topology.IsClosedEmbedding
      (fun K : bodyCutoff C δ ↦ bodyIndicator K.val) := by
  let : CompactSpace (bodyCutoff C δ) := isCompact_iff_compactSpace.mp (isCompact_bodyCutoff C δ)
  apply ((continuous_bodyIndicator n).comp continuous_subtype_val).isClosedEmbedding
  intro K L heq
  apply Subtype.ext
  exact body_eq_of_indicator_eq_of_volume_pos K.val L.val
    (hδ.trans_le K.property.2) (hδ.trans_le L.property.2) heq

/-- The genuine inverse on the actual positive compact-family L1 image is continuous. -/
def cutoffHomeomorph {n : ℕ} (C : AdmissibleCone n) (δ : ℝ) (hδ : 0 < δ) :
    bodyCutoff C δ ≃ₜ range (fun K : bodyCutoff C δ ↦ bodyIndicator K.val) :=
  (isClosedEmbedding_cutoffIndicator C δ hδ).isEmbedding.toHomeomorph

/-- The actual complete-space extension of the true source indicator isometry. -/
def indicatorExtension {n : ℕ} (C : AdmissibleCone n) : AlmostSpace C →
    Lp ℝ 1 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  IsDenseInducing.extend
    ((isometry_fullToAlmost C).isUniformInducing.isDenseInducing
      (denseRange_fullToAlmost C)) (fun S : FullSemigroup C ↦ bodyIndicator (bodyMap S))

/-- Genuine source density and actual target completeness give uniform continuity. -/
theorem uniformContinuous_indicatorExtension {n : ℕ} (C : AdmissibleCone n) :
    UniformContinuous (indicatorExtension C) :=
  uniformContinuous_uniformly_extend (isometry_fullToAlmost C).isUniformInducing
    (denseRange_fullToAlmost C) (isometry_fullIndicator C).uniformContinuous

/-- The actual indicator extension agrees with the actual original source body indicators. -/
theorem indicatorExtension_source {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    indicatorExtension C (fullToAlmost S) = bodyIndicator (bodyMap S) :=
  uniformly_extend_of_ind (isometry_fullToAlmost C).isUniformInducing
    (denseRange_fullToAlmost C) (isometry_fullIndicator C).uniformContinuous S

/-- The actual source-neighborhood filter converges to the actual indicator extension value. -/
theorem tendsto_source_indicatorExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    Tendsto (fun T : FullSemigroup C ↦ bodyIndicator (bodyMap T))
      (comap fullToAlmost (𝓝 S)) (𝓝 (indicatorExtension C S)) :=
  uniformly_extend_spec (isometry_fullToAlmost C).isUniformInducing
    (denseRange_fullToAlmost C) (isometry_fullIndicator C).uniformContinuous S

/-- Density identifies the actual extension norm with the actual source volume. -/
theorem norm_indicatorExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    ‖indicatorExtension C S‖ = S.val.volume := by
  have heq : (fun T : AlmostSpace C ↦ ‖indicatorExtension C T‖) =
      (fun T : AlmostSpace C ↦ T.val.volume) := by
    apply (denseRange_fullToAlmost C).equalizer
      (uniformContinuous_indicatorExtension C).continuous.norm
      (ConeSubset.continuous_volume.comp continuous_subtype_val)
    funext T
    change ‖indicatorExtension C (fullToAlmost T)‖ = T.val.volume
    rw [indicatorExtension_source, norm_bodyIndicator, volume_bodyMap]
  exact congrFun heq S

/-- Actual positive source volume forces actual extension membership in a genuine compact cutoff image. -/
theorem indicatorExtension_mem_cutoff_range {n : ℕ} {C : AdmissibleCone n}
    (S : AlmostSpace C) {δ : ℝ} (hδ : 0 < δ) (hδS : δ < S.val.volume) :
    indicatorExtension C S ∈ range (fun K : bodyCutoff C δ ↦ bodyIndicator K.val) := by
  let e : FullSemigroup C → AlmostSpace C := fullToAlmost
  have hd := (isometry_fullToAlmost C).isUniformInducing.isDenseInducing
    (denseRange_fullToAlmost C)
  let : NeBot (comap e (𝓝 S)) := hd.comap_nhds_neBot S
  apply (isClosedEmbedding_cutoffIndicator C δ hδ).isClosed_range.mem_of_tendsto
    (tendsto_source_indicatorExtension S)
  have hnear : ∀ᶠ T : AlmostSpace C in 𝓝 S, δ < T.val.volume :=
    (ConeSubset.continuous_volume.comp continuous_subtype_val).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hδS)
  have hfull : ∀ᶠ T : FullSemigroup C in comap e (𝓝 S), δ < T.val.volume :=
    hnear.comap e
  filter_upwards [hfull] with T hT
  exact ⟨⟨bodyMap T, bodyMap_mem_bodyCutoff T hT.le⟩, rfl⟩

/-- Every actual almost semigroup has a genuine bounded positive-volume body realizing its actual indicator limit. -/
theorem exists_body_of_indicatorExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    ∃ K : ConvexBody (EuclideanSpace ℝ (Fin n)),
      (K : Set (EuclideanSpace ℝ (Fin n))) ⊆ sourceBodyAmbient C ∧
      bodyIndicator K = indicatorExtension C S := by
  obtain ⟨K, hK⟩ := indicatorExtension_mem_cutoff_range S
    (half_pos S.property.2) (half_lt_self S.property.2)
  exact ⟨K.val, K.property.1, hK⟩

/-- The actual extension body is chosen from the actual closed compact-family image, not from a limiting-body certificate. -/
def bodyExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    ConvexBody (EuclideanSpace ℝ (Fin n)) := (exists_body_of_indicatorExtension S).choose

/-- The actual extension body lies inside the original genuine compact cone section. -/
theorem bodyExtension_subset_sourceBodyAmbient {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    (bodyExtension S : Set (EuclideanSpace ℝ (Fin n))) ⊆ sourceBodyAmbient C :=
  (exists_body_of_indicatorExtension S).choose_spec.1

/-- Its actual body indicator is the actual complete-space extension value. -/
theorem bodyIndicator_bodyExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    bodyIndicator (bodyExtension S) = indicatorExtension C S :=
  (exists_body_of_indicatorExtension S).choose_spec.2

/-- The actual extension preserves exactly the actual source volume. -/
theorem volume_bodyExtension {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    volume.real (bodyExtension S : Set (EuclideanSpace ℝ (Fin n))) = S.val.volume := by
  rw [← norm_bodyIndicator, bodyIndicator_bodyExtension, norm_indicatorExtension]

/-- Genuine positive-volume indicator rigidity gives exact agreement with the original source body map. -/
theorem bodyExtension_source {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    bodyExtension (fullToAlmost S) = bodyMap S := by
  apply body_eq_of_indicator_eq_of_volume_pos
  · rw [volume_bodyExtension]
    exact S.volume_pos
  · rw [volume_bodyMap]
    exact S.volume_pos
  · rw [bodyIndicator_bodyExtension, indicatorExtension_source]

/-- A fixed actual positive source-volume neighborhood maps into the actual compact cutoff family. -/
def cutoffLift {n : ℕ} {C : AdmissibleCone n} (δ : ℝ) (_hδ : 0 < δ) :
    {S : AlmostSpace C // δ < S.val.volume} → bodyCutoff C δ :=
  fun S ↦ ⟨bodyExtension S.val, bodyExtension_subset_sourceBodyAmbient S.val,
    by
      change δ ≤ volume.real (bodyExtension S.val : Set (EuclideanSpace ℝ (Fin n)))
      rw [volume_bodyExtension]
      exact S.property.le⟩

/-- The genuine indicator embedding proves actual local continuity without assuming body convergence. -/
theorem continuous_cutoffLift {n : ℕ} {C : AdmissibleCone n} (δ : ℝ) (hδ : 0 < δ) :
    Continuous (cutoffLift (C := C) δ hδ) := by
  apply (isClosedEmbedding_cutoffIndicator C δ hδ).isEmbedding.continuous_iff.mpr
  have h := (uniformContinuous_indicatorExtension C).continuous.comp
    (continuous_subtype_val : Continuous (fun S : {S : AlmostSpace C // δ < S.val.volume} ↦ S.val))
  convert h using 1
  funext S
  exact bodyIndicator_bodyExtension S.val

/-- The actual extension is continuous for the genuine Euclidean Hausdorff metric. -/
theorem continuous_bodyExtension {n : ℕ} (C : AdmissibleCone n) :
    Continuous (bodyExtension (C := C)) := by
  rw [continuous_iff_continuousAt]
  intro S
  let δ := S.val.volume / 2
  have hδ : 0 < δ := half_pos S.property.2
  have hδS : δ < S.val.volume := half_lt_self S.property.2
  have hlocal : ContinuousOn (bodyExtension (C := C)) {T | δ < T.val.volume} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_subtype_val.comp (continuous_cutoffLift (C := C) δ hδ)
  exact hlocal.continuousAt
    (((ConeSubset.continuous_volume.comp continuous_subtype_val).isOpen_preimage _
      isOpen_Ioi).mem_nhds hδS)

/-- SGPT `thm:Okocontapp`: genuine unique continuous body extension with the exact source volume identity. -/
theorem existsUnique_continuous_body_extension {n : ℕ} (C : AdmissibleCone n) :
    ∃! F : AlmostSpace C → ConvexBody (EuclideanSpace ℝ (Fin n)),
      Continuous F ∧ (∀ S : FullSemigroup C, F (fullToAlmost S) = bodyMap S) ∧
      ∀ S : AlmostSpace C, volume.real (F S : Set (EuclideanSpace ℝ (Fin n))) = S.val.volume := by
  refine ⟨bodyExtension, ⟨continuous_bodyExtension C, bodyExtension_source, volume_bodyExtension⟩, ?_⟩
  intro F hF
  exact continuous_extension_unique F bodyExtension hF.1 (continuous_bodyExtension C)
    hF.2.1 bodyExtension_source

end SGPT.AlmostSemigroup.OkounkovExtension
