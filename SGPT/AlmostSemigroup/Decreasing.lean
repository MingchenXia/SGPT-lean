import SGPT.AlmostSemigroup.Intersection

/-!
# Actual decreasing semigroups and generated-cone limits

The source limit candidate is the actual standard lattice saturation of the
intersection of the actual closed generated cones. It is not the intersection
of the original source semigroups, which may be empty even at positive volume.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Decreasing

open Set Filter MeasureTheory
open scoped Topology Pointwise
open Okounkov Regularization Intersection

/-- The actual intersection of the original source's actual closed generated cones. -/
def limitCone {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) : AdmissibleCone n where
  cone := ⨅ i, (closedCone (S i) : ConvexCone ℝ ((Fin n → ℝ) × ℝ))
  closed := by
    rw [ConvexCone.coe_iInf]
    exact isClosed_iInter fun i ↦ isClosed_closedCone (S i)
  nonnegativeHeight z hz := C.nonnegativeHeight z
    (closedCone_subset_source C (S 0) (hS 0) (nonempty_of_generatedGroup_eq_top _ (hG 0))
      ((ConvexCone.mem_iInf.mp hz) 0))
  zeroHeight x hx := C.zeroHeight x
    (closedCone_subset_source C (S 0) (hS 0) (nonempty_of_generatedGroup_eq_top _ (hG 0))
      ((ConvexCone.mem_iInf.mp hx) 0))

/-- Height-one membership is precisely the actual source body intersection. -/
theorem heightOne_limitCone {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) :
    heightOne (limitCone C S hS hG).cone = ⋂ i, body (S i) := by
  ext x
  simp [heightOne, limitCone, body]

/-- Genuine semigroup antitonicity gives genuine body antitonicity. -/
theorem body_antitone {n : ℕ} (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hanti : Antitone S) : Antitone (fun i ↦ body (S i)) := by
  intro i j hij x hx
  exact closedCone_mono (hanti hij) hx

/-- Actual compact finite measures give true continuity from above for the actual body sequence. -/
theorem tendsto_body_volume {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (hanti : Antitone S) :
    Tendsto (fun i ↦ volume.real (body (S i))) atTop
      (𝓝 (volume.real (heightOne (limitCone C S hS hG).cone))) := by
  have hcompact (i : ℕ) := isCompact_body C (S i) (hS i)
    (nonempty_of_generatedGroup_eq_top _ (hG i))
  have hmeasure : Tendsto (fun i ↦ volume (body (S i))) atTop
      (𝓝 (volume (heightOne (limitCone C S hS hG).cone))) := by
    simpa only [Function.comp_def, heightOne_limitCone] using
      tendsto_measure_iInter_atTop (fun i ↦ (hcompact i).measurableSet.nullMeasurableSet)
        (body_antitone S hanti) ⟨0, (hcompact 0).measure_lt_top.ne⟩
  let D := limitCone C S hS hG
  have hfinite : volume (heightOne D.cone) ≠ ⊤ :=
    (isCompact_heightOne D.cone D.closed D.nonnegativeHeight D.zeroHeight).measure_lt_top.ne
  simpa only [Function.comp_def, Measure.real] using (ENNReal.tendsto_toReal hfinite).comp hmeasure

/-- The source limit candidate uses actual cone saturation. -/
def limitSemigroup {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) := latticePoints (limitCone C S hS hG).cone

/-- The actual limit candidate is contained in the actual original cone. -/
theorem limitSemigroup_le_source {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) :
    limitSemigroup C S hS hG ≤ latticePoints C.cone := by
  intro z hz
  exact closedCone_subset_source C (S 0) (hS 0) (nonempty_of_generatedGroup_eq_top _ (hG 0))
    ((ConvexCone.mem_iInf.mp hz) 0)

/-- The actual cone limit is contained in every actual regularized source semigroup. -/
theorem limitSemigroup_le_regularized {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (i : ℕ) :
    limitSemigroup C S hS hG ≤ regularizedSemigroup (S i) := by
  intro z hz
  exact (ConvexCone.mem_iInf.mp hz) i

/-- An actual positive-volume admissible cone's standard lattice saturation generates the whole group. -/
theorem generatedGroup_latticePoints_eq_top {n : ℕ} (D : AdmissibleCone n)
    (hvolume : 0 < volume.real (heightOne D.cone)) :
    LatticeSlices.generatedGroup (latticePoints D.cone) = ⊤ := by
  have hbody : (heightOne D.cone).Nonempty := by
    by_contra hbody
    have hempty : heightOne D.cone = ∅ := not_nonempty_iff_eq_empty.mp hbody
    rw [hempty] at hvolume
    simp at hvolume
  obtain ⟨x, hx⟩ := hbody
  have hpointed := ConvexCone.Pointed.of_nonempty_of_isClosed ⟨(x, (1 : ℝ)), hx⟩ D.closed
  change (0 : (Fin n → ℝ) × ℝ) ∈ D.cone at hpointed
  have hzero : (0 : (Fin n → ℤ) × ℤ) ∈ latticePoints D.cone := by
    change latticeCast n 0 ∈ D.cone
    have heq : latticeCast n (0 : (Fin n → ℤ) × ℤ) = 0 := by
      apply Prod.ext
      · funext j
        simp [latticeCast]
      · simp [latticeCast]
    rw [heq]
    exact hpointed
  have hne : (latticePoints D.cone : Set ((Fin n → ℤ) × ℤ)).Nonempty := ⟨0, hzero⟩
  apply generatedGroup_eq_top_of_full_count_limit D (latticePoints D.cone) le_rfl
    (isCompact_heightOne D.cone D.closed D.nonnegativeHeight D.zeroHeight)
    (fun _ hx ↦ closedCone_subset_source D (latticePoints D.cone) le_rfl hne hx) hvolume
  exact Counting.tendsto_cone_lattice_slices D

/-- The actual source limit candidate lies in the original source pseudometric space. -/
def limitSubset {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) : ConeSubset C :=
  sourceSubset C (limitSemigroup C S hS hG) (limitSemigroup_le_source C S hS hG)

/-- The original cone space has the candidate saturation's genuine degreewise counting limit. -/
theorem tendsto_limit_normalizedCardinality {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) :
    Tendsto (limitSubset C S hS hG).normalizedCardinality atTop
      (𝓝 (volume.real (heightOne (limitCone C S hS hG).cone))) := by
  have heq : (limitSubset C S hS hG).normalizedCardinality =
      (Counting.coneSubset (limitCone C S hS hG)).normalizedCardinality := by
    funext k
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    congr 1
  rw [heq]
  exact Counting.tendsto_cone_lattice_slices (limitCone C S hS hG)

/-- The original limsup volume of the actual cone limit is its actual section volume. -/
theorem volume_limitSubset {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) :
    (limitSubset C S hS hG).volume = volume.real (heightOne (limitCone C S hS hG).cone) :=
  (tendsto_limit_normalizedCardinality C S hS hG).limsup_eq

/-- True original source volumes converge to the actual decreasing-cone section's volume. -/
theorem tendsto_source_volume {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (hanti : Antitone S) :
    Tendsto (fun i ↦ (sourceSubset C (S i) (hS i)).volume) atTop
      (𝓝 (volume.real (heightOne (limitCone C S hS hG).cone))) := by
  have heq : (fun i ↦ (sourceSubset C (S i) (hS i)).volume) =
      fun i ↦ volume.real (body (S i)) := by
    funext i
    exact BodyGeometry.volume_source_eq_body C (S i) (hS i) (hG i)
  rw [heq]
  exact tendsto_body_volume C S hS hG hanti

/-- Actual subset deficits and true counting limits compute the exact source-to-limit distance. -/
theorem distance_source_limitSubset {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (i : ℕ) :
    dist (sourceSubset C (S i) (hS i)) (limitSubset C S hS hG) =
      (sourceSubset C (S i) (hS i)).volume - (limitSubset C S hS hG).volume := by
  let Q := limitSubset C S hS hG
  let R := regularizedSubset C (S i) (hS i) (nonempty_of_generatedGroup_eq_top _ (hG i))
  have hQR : Q.val ⊆ R.val := limitSemigroup_le_regularized C S hS hG i
  have hreg := tendsto_regularized_normalizedCardinality C (S i) (hS i)
    (nonempty_of_generatedGroup_eq_top _ (hG i))
  have hcount := tendsto_limit_normalizedCardinality C S hS hG
  have hdisc : Tendsto (normalizedDiscrepancy n Q.slices R.slices) atTop
      (𝓝 (volume.real (body (S i)) - volume.real (heightOne (limitCone C S hS hG).cone))) := by
    apply (hreg.sub hcount).congr'
    exact Eventually.of_forall fun k ↦ (normalizedDiscrepancy_eq_sub_of_subset Q R hQR k).symm
  have hdist : dist Q R = volume.real (body (S i)) -
      volume.real (heightOne (limitCone C S hS hG).cone) := hdisc.limsup_eq
  have hzero := distance_regularization_eq_zero C (S i) (hS i) (hG i)
  have heq := PseudoMetricSpace.dist_eq_of_dist_zero Q hzero
  change dist Q (sourceSubset C (S i) (hS i)) = dist Q R at heq
  rw [dist_comm, heq, hdist, BodyGeometry.volume_source_eq_body C (S i) (hS i) (hG i),
    volume_limitSubset C S hS hG]

/-- The original decreasing source sequence converges to the actual cone saturation even at zero volume. -/
theorem tendsto_source_limitSubset {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (hanti : Antitone S) :
    Tendsto (fun i ↦ sourceSubset C (S i) (hS i)) atTop (𝓝 (limitSubset C S hS hG)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have heq : (fun i ↦ dist (sourceSubset C (S i) (hS i)) (limitSubset C S hS hG)) =
      fun i ↦ (sourceSubset C (S i) (hS i)).volume -
        volume.real (heightOne (limitCone C S hS hG).cone) := by
    funext i
    rw [distance_source_limitSubset C S hS hG i, volume_limitSubset C S hS hG]
  rw [heq]
  simpa only [sub_self] using (tendsto_source_volume C S hS hG hanti).sub
    (tendsto_const_nhds (x := volume.real (heightOne (limitCone C S hS hG).cone)))

/-- SGPT `lma:Sprimeintapp`: an actual full-group source semigroup realizes the actual positive-volume limit. -/
theorem exists_full_semigroup_limit {n : ℕ} (C : AdmissibleCone n)
    (S : ℕ → AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : ∀ i, S i ≤ latticePoints C.cone)
    (hG : ∀ i, LatticeSlices.generatedGroup (S i) = ⊤) (hanti : Antitone S)
    {L : ℝ} (hL : 0 < L)
    (hvolume : Tendsto (fun i ↦ (sourceSubset C (S i) (hS i)).volume) atTop (𝓝 L)) :
    ∃ U : AddSubsemigroup ((Fin n → ℤ) × ℤ), ∃ hU : U ≤ latticePoints C.cone,
      LatticeSlices.generatedGroup U = ⊤ ∧
        Tendsto (fun i ↦ sourceSubset C (S i) (hS i)) atTop (𝓝 (sourceSubset C U hU)) := by
  have heq : L = volume.real (heightOne (limitCone C S hS hG).cone) :=
    tendsto_nhds_unique hvolume (tendsto_source_volume C S hS hG hanti)
  have hpositive : 0 < volume.real (heightOne (limitCone C S hS hG).cone) := heq ▸ hL
  exact ⟨limitSemigroup C S hS hG, limitSemigroup_le_source C S hS hG,
    generatedGroup_latticePoints_eq_top (limitCone C S hS hG) hpositive,
    tendsto_source_limitSubset C S hS hG hanti⟩

end SGPT.AlmostSemigroup.Decreasing
