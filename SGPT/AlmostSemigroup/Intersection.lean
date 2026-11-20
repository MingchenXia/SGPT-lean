import SGPT.AlmostSemigroup.BodyGeometry

/-!
# Actual semigroup intersection counts and distance

The common generated-cone saturation has a genuine count limit. The actual
two regularization deficits squeeze the source intersection's actual deficit
to zero. This gives true intersection counts and the exact source distance
formula before assuming that the source intersection generates the full group.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Intersection

open Set Filter MeasureTheory
open scoped Topology Pointwise
open Okounkov Regularization

/-- The actual intersection of the two closed generated cones, inheriting original admissibility. -/
def commonCone {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    AdmissibleCone n where
  cone := (closedCone S : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) ⊓ closedCone T
  closed := (isClosed_closedCone S).inter (isClosed_closedCone T)
  nonnegativeHeight z hz := C.nonnegativeHeight z (closedCone_subset_source C S hS hne hz.1)
  zeroHeight x hx := C.zeroHeight x (closedCone_subset_source C S hS hne hx.1)

/-- The actual common standard-lattice saturation as a subset of the original source cone. -/
def saturatedIntersectionSubset {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    ConeSubset C :=
  sourceSubset C (latticePoints (commonCone C S T hS hne).cone)
    (fun _ hz ↦ closedCone_subset_source C S hS hne hz.1)

/-- The actual source intersection, retaining its actual additive closure. -/
def intersectionSubset {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) : ConeSubset C :=
  sourceSubset C (S ⊓ T) (fun _ hz ↦ hS hz.1)

/-- Actual regularization intersections are precisely actual common-cone saturation. -/
theorem saturatedIntersectionSubset_eq_inter {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hneS : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    (hneT : (T : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    saturatedIntersectionSubset C S T hS hneS =
      ConeSubset.inter (regularizedSubset C S hS hneS) (regularizedSubset C T hT hneT) := rfl

/-- The original source intersection is the exact intersection in the actual source pseudometric space. -/
theorem intersectionSubset_eq_inter {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone) :
    intersectionSubset C S T hS = ConeSubset.inter (sourceSubset C S hS) (sourceSubset C T hT) := rfl

/-- The common actual saturation counts have the genuine common-body volume limit. -/
theorem tendsto_saturatedIntersection_normalizedCardinality {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    Tendsto (saturatedIntersectionSubset C S T hS hne).normalizedCardinality atTop
      (𝓝 (volume.real (body S ∩ body T))) := by
  let D := commonCone C S T hS hne
  have heq : (saturatedIntersectionSubset C S T hS hne).normalizedCardinality =
      (Counting.coneSubset D).normalizedCardinality := by
    funext k
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    congr 1
  exact heq ▸ Counting.tendsto_cone_lattice_slices D

/-- The actual source intersection discrepancy from common saturation genuinely tends to zero. -/
theorem tendsto_intersection_discrepancy {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤) :
    Tendsto (normalizedDiscrepancy n (intersectionSubset C S T hS).slices
      (saturatedIntersectionSubset C S T hS (nonempty_of_generatedGroup_eq_top S hGS)).slices)
      atTop (𝓝 0) := by
  have hS' := tendsto_regularization_discrepancy C S hS hGS
  have hT' := tendsto_regularization_discrepancy C T hT hGT
  apply squeeze_zero (normalizedDiscrepancy_nonneg n _ _) _ (by simpa using hS'.add hT')
  intro k
  rw [intersectionSubset_eq_inter C S T hS hT,
    saturatedIntersectionSubset_eq_inter C S T hS hT
      (nonempty_of_generatedGroup_eq_top S hGS) (nonempty_of_generatedGroup_eq_top T hGT)]
  simpa only [ConeSubset.slices_inter_fun] using normalizedDiscrepancy_inter_inter n
    (sourceSubset C S hS).slices (sourceSubset C T hT).slices
    (regularizedSubset C S hS (nonempty_of_generatedGroup_eq_top S hGS)).slices
    (regularizedSubset C T hT (nonempty_of_generatedGroup_eq_top T hGT)).slices k

/-- Genuine all-degree source intersection counts, without a full-group hypothesis on the intersection. -/
theorem tendsto_intersection_normalizedCardinality {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤) :
    Tendsto (intersectionSubset C S T hS).normalizedCardinality atTop
      (𝓝 (volume.real (body S ∩ body T))) := by
  have hsat := tendsto_saturatedIntersection_normalizedCardinality C S T hS
    (nonempty_of_generatedGroup_eq_top S hGS)
  have hdisc := tendsto_intersection_discrepancy C S T hS hT hGS hGT
  have h := hsat.sub hdisc
  simp only [sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun k ↦ by
    dsimp only
    rw [normalizedDiscrepancy_eq_sub_of_subset (intersectionSubset C S T hS)
      (saturatedIntersectionSubset C S T hS (nonempty_of_generatedGroup_eq_top S hGS))
      (fun _ hz ↦ ⟨mem_closedCone_of_mem S hz.1, mem_closedCone_of_mem T hz.2⟩) k]
    ring

/-- Actual source intersection volume is the actual common-body volume. -/
theorem volume_intersection_eq {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤) :
    (intersectionSubset C S T hS).volume = volume.real (body S ∩ body T) :=
  (tendsto_intersection_normalizedCardinality C S T hS hT hGS hGT).limsup_eq

/-- SGPT `cor:distapp`, strengthened to include zero-volume source intersections. -/
theorem distance_eq_volumes {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤) :
    dist (sourceSubset C S hS) (sourceSubset C T hT) =
      (sourceSubset C S hS).volume + (sourceSubset C T hT).volume -
        2 * (intersectionSubset C S T hS).volume := by
  have hS' := tendsto_source_of_generatedGroup_eq_top C S hS hGS
  have hT' := tendsto_source_of_generatedGroup_eq_top C T hT hGT
  have hI := tendsto_intersection_normalizedCardinality C S T hS hT hGS hGT
  have hlim := (hS'.add hT').sub (hI.const_mul 2)
  have heq : (fun k : ℕ ↦ (sourceSubset C S hS).normalizedCardinality k +
      (sourceSubset C T hT).normalizedCardinality k -
        2 * (intersectionSubset C S T hS).normalizedCardinality k) =
      fun k : ℕ ↦ (k : ℝ)⁻¹ ^ n * (((sourceSubset C S hS).slices k).card +
        ((sourceSubset C T hT).slices k).card -
          2 * ((sourceSubset C S hS).slices k ∩ (sourceSubset C T hT).slices k).card) := by
    funext k
    rw [intersectionSubset_eq_inter C S T hS hT, ConeSubset.normalizedCardinality,
      ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality, ConeSubset.slices_inter]
    ring
  rw [ConeSubset.dist_eq_distance, ConeSubset.distance_eq_limsup_card, ← heq, hlim.limsup_eq,
    BodyGeometry.volume_source_eq_body C S hS hGS, BodyGeometry.volume_source_eq_body C T hT hGT,
    volume_intersection_eq C S T hS hT hGS hGT]

/-- Actual finite measure and dense convex interior force containment in a closed set. -/
theorem subset_of_volume_inter_eq {n : ℕ} {K L : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hL : IsClosed L) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (heq : volume.real (K ∩ L) = volume.real K) :
    K ⊆ L := by
  have hfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hfinI : volume (K ∩ L) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hfin
  have heq' : volume (K ∩ L) = volume K :=
    (measureReal_eq_measureReal_iff hfinI hfin).mp heq
  have hsum := measure_sdiff_add_inter K hL.measurableSet (μ := volume)
  rw [heq'] at hsum
  have hnull : volume (K \ L) = 0 := (ENNReal.add_left_inj hfin).mp (by simpa using hsum)
  have hopen : IsOpen (interior K \ L) := isOpen_interior.sdiff hL
  have hempty : interior K \ L = ∅ := hopen.eq_empty_of_measure_zero
    (measure_mono_null (sdiff_subset_sdiff_left interior_subset) hnull)
  have hsub : interior K ⊆ L := by
    intro x hx
    by_contra hxL
    have hmem : x ∈ interior K \ L := ⟨hx, hxL⟩
    rw [hempty] at hmem
    exact hmem
  have hdense : closure (interior K) = K := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint, hK.isClosed.closure_eq]
  rw [← hdense]
  exact closure_minimal hsub hL

/-- SGPT `lma:Deltaindclassapp`: actual metric-equivalent source semigroups have equal bodies. -/
theorem body_eq_of_distance_eq_zero {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤)
    (hzero : dist (sourceSubset C S hS) (sourceSubset C T hT) = 0) : body S = body T := by
  have hKS := isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hGS)
  have hKT := isCompact_body C T hT (nonempty_of_generatedGroup_eq_top T hGT)
  have hIS : volume.real (body S ∩ body T) ≤ volume.real (body S) :=
    measureReal_mono inter_subset_left hKS.measure_lt_top.ne
  have hIT : volume.real (body S ∩ body T) ≤ volume.real (body T) :=
    measureReal_mono inter_subset_right hKT.measure_lt_top.ne
  rw [distance_eq_volumes C S T hS hT hGS hGT,
    BodyGeometry.volume_source_eq_body C S hS hGS, BodyGeometry.volume_source_eq_body C T hT hGT,
    volume_intersection_eq C S T hS hT hGS hGT] at hzero
  apply Subset.antisymm
  · apply subset_of_volume_inter_eq hKS hKT.isClosed (convex_body S)
      (BodyGeometry.interior_body_nonempty C S hS hGS)
    linarith
  · apply subset_of_volume_inter_eq hKT hKS.isClosed (convex_body T)
      (BodyGeometry.interior_body_nonempty C T hT hGT)
    rw [inter_comm]
    linarith

/-- The actual standard lattice has the fundamental unit cube's covolume. -/
theorem covolume_standardLattice (n : ℕ) :
    ZLattice.covolume (Counting.standardLattice n) = 1 := by
  unfold Counting.standardLattice
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume),
    ZSpan.volume_real_fundamentalDomain]
  have heq : Matrix.of (Pi.basisFun ℝ (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [heq, Matrix.det_one, abs_one]

/-- A genuine positive count limit through every degree forces the actual integral period to be one. -/
theorem degree_period_eq_one_of_positive_count_limit {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    {a : ℕ} (ha : 0 < a)
    (hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ)) {L : ℝ} (hL : 0 < L)
    (hlimit : Tendsto (sourceSubset C S hS).normalizedCardinality atTop (𝓝 L)) : a = 1 := by
  have hpositive : ∀ᶠ k in atTop, 0 < (sourceSubset C S hS).normalizedCardinality k :=
    (tendsto_order.mp hlimit).1 0 hL
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpositive
  have hdiv : a ∣ N * a + 1 := by
    by_contra hdiv
    have hzero := source_normalizedCardinality_eq_zero_of_not_dvd C S hS hperiod hdiv
    have hp := hN (N * a + 1) ((Nat.le_mul_of_pos_right N ha).trans (Nat.le_succ _))
    rw [hzero] at hp
    exact (lt_irrefl 0) hp
  have hdivone : a ∣ 1 := (Nat.dvd_add_right (dvd_mul_left a N)).mp hdiv
  exact Nat.eq_one_of_dvd_one hdivone

/-- Genuine generated-cone monotonicity follows actual hull and topological closure monotonicity. -/
theorem closedCone_mono {n : ℕ} {S T : AddSubsemigroup ((Fin n → ℤ) × ℤ)} (hST : S ≤ T) :
    closedCone S ≤ closedCone T := by
  apply closure_mono
  exact Submodule.span_mono (image_mono hST)

/-- The actual source intersection body lies in the actual common body. -/
theorem body_intersection_subset {n : ℕ} (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    body (S ⊓ T) ⊆ body S ∩ body T := by
  intro x hx
  exact ⟨closedCone_mono inf_le_left hx, closedCone_mono inf_le_right hx⟩

/-- Genuine all-degree full-body counts force actual period one and actual horizontal index one.
The criterion uses actual counts; the source consumers produce its limit from the checked counting proofs. -/
theorem generatedGroup_eq_top_of_full_count_limit {n : ℕ} (C : AdmissibleCone n)
    (U : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hU : U ≤ latticePoints C.cone)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hbody : body U ⊆ K)
    (hpositive : 0 < volume.real K)
    (hlimit : Tendsto (sourceSubset C U hU).normalizedCardinality atTop (𝓝 (volume.real K))) :
    LatticeSlices.generatedGroup U = ⊤ := by
  let G := LatticeSlices.generatedGroup U
  let L := LatticeSlices.horizontalLattice G
  have hnonzero : ∃ z ∈ U, z ≠ 0 := by
    by_contra hnonzero
    have hzero := tendsto_source_normalizedCardinality_of_no_nonzero C U hU
      (by simpa only [not_exists, not_and, not_not] using hnonzero)
    exact hpositive.ne' (tendsto_nhds_unique hlimit hzero)
  have hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤ := by
    by_contra hspan
    have hzero := tendsto_source_normalizedCardinality_of_lower_rank C U hU hspan
    exact hpositive.ne' (tendsto_nhds_unique hlimit hzero)
  let : IsZLattice ℝ L := ⟨hspan⟩
  obtain ⟨a, ha, hperiod, β, hβ⟩ :=
    LatticeSlices.exists_semigroup_degree_period C U hU hnonzero
  have haone := degree_period_eq_one_of_positive_count_limit C U hU ha hperiod hpositive hlimit
  subst a
  obtain ⟨z, hz, _⟩ := hnonzero
  have hgroup := tendsto_source_period_of_full_rank C U hU ⟨z, hz⟩ ha hperiod hβ
  simp only [mul_one] at hgroup
  have hratio : volume.real (body U) / ZLattice.covolume L =
      volume.real K := tendsto_nhds_unique hgroup hlimit
  have hcovol : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hmono : volume.real (body U) ≤ volume.real K :=
    measureReal_mono hbody hK.measure_lt_top.ne
  have hcovol_le : ZLattice.covolume L ≤ 1 := by
    have heq : volume.real (body U) = volume.real K * ZLattice.covolume L :=
      (div_eq_iff hcovol.ne').mp hratio
    nlinarith
  let : DiscreteTopology (Counting.standardLattice n) := by
    unfold Counting.standardLattice
    infer_instance
  let : IsZLattice ℝ (Counting.standardLattice n) := by
    unfold Counting.standardLattice
    infer_instance
  have hindex : ZLattice.covolume L =
      (L.toAddSubgroup.relIndex (Counting.standardLattice n).toAddSubgroup : ℝ) := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex L (Counting.standardLattice n)
      (LatticeSlices.horizontalLattice_le_standard G)
    simpa only [covolume_standardLattice, div_one] using h
  have hindex_pos : 0 < L.toAddSubgroup.relIndex (Counting.standardLattice n).toAddSubgroup := by
    rw [hindex] at hcovol
    exact_mod_cast hcovol
  have hindex_le : L.toAddSubgroup.relIndex (Counting.standardLattice n).toAddSubgroup ≤ 1 := by
    rw [hindex] at hcovol_le
    exact_mod_cast hcovol_le
  have hindex_one : L.toAddSubgroup.relIndex (Counting.standardLattice n).toAddSubgroup = 1 := by
    omega
  have hstandard : (Counting.standardLattice n).toAddSubgroup ≤ L.toAddSubgroup :=
    AddSubgroup.relIndex_eq_one.mp hindex_one
  have hhorizontal : LatticeSlices.horizontalGroup G = ⊤ := by
    apply top_unique
    intro x _
    have hxL : Counting.integerCast x ∈ L :=
      hstandard (Counting.integerCast_mem_standardLattice x)
    obtain ⟨y, hy, hyx⟩ := (LatticeSlices.mem_horizontalLattice_iff G _).mp hxL
    have hyx' : y = x := Counting.integerCast_injective hyx
    simpa only [hyx'] using hy
  apply top_unique
  rintro ⟨x, k⟩ _
  have hh : (x - k • β, (0 : ℤ)) ∈ G := by
    apply (LatticeSlices.mem_horizontalGroup G _).mp
    rw [hhorizontal]
    trivial
  have hv := G.zsmul_mem hβ k
  have hadd := G.add_mem hh hv
  simpa using hadd

/-- SGPT `lma:intersecS'app`, actual full-group generation clause from actual KK12 counts and index. -/
theorem generatedGroup_intersection_eq_top {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤)
    (hvolume : 0 < (intersectionSubset C S T hS).volume) :
    LatticeSlices.generatedGroup (S ⊓ T) = ⊤ := by
  have hU : S ⊓ T ≤ latticePoints C.cone := fun _ hz ↦ hS hz.1
  have hK := (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hGS)).inter
    (isCompact_body C T hT (nonempty_of_generatedGroup_eq_top T hGT))
  have hpositive : 0 < volume.real (body S ∩ body T) := by
    rw [← volume_intersection_eq C S T hS hT hGS hGT]
    exact hvolume
  exact generatedGroup_eq_top_of_full_count_limit C (S ⊓ T) hU hK
    (body_intersection_subset S T) hpositive
    (tendsto_intersection_normalizedCardinality C S T hS hT hGS hGT)

/-- The actual positive-volume source intersection body is precisely the actual common body. -/
theorem body_intersection_eq {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤)
    (hvolume : 0 < (intersectionSubset C S T hS).volume) :
    body (S ⊓ T) = body S ∩ body T := by
  have hU : S ⊓ T ≤ latticePoints C.cone := fun _ hz ↦ hS hz.1
  have hGU := generatedGroup_intersection_eq_top C S T hS hT hGS hGT hvolume
  have hKU := isCompact_body C (S ⊓ T) hU (nonempty_of_generatedGroup_eq_top _ hGU)
  have hK := (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hGS)).inter
    (isCompact_body C T hT (nonempty_of_generatedGroup_eq_top T hGT))
  have hsub := body_intersection_subset S T
  have hvol : volume.real (body (S ⊓ T)) = volume.real (body S ∩ body T) :=
    tendsto_nhds_unique (tendsto_source_of_generatedGroup_eq_top C (S ⊓ T) hU hGU)
      (tendsto_intersection_normalizedCardinality C S T hS hT hGS hGT)
  have hint : (interior (body S ∩ body T)).Nonempty :=
    (BodyGeometry.interior_body_nonempty C (S ⊓ T) hU hGU).mono (interior_mono hsub)
  apply Subset.antisymm hsub
  apply subset_of_volume_inter_eq hK hKU.isClosed ((convex_body S).inter (convex_body T)) hint
  rw [inter_eq_right.mpr hsub]
  exact hvol

/-- SGPT `lma:intersecS'app`, exact equality of the actual closed generated cones. -/
theorem closedCone_intersection_eq {n : ℕ} (C : AdmissibleCone n)
    (S T : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hS : S ≤ latticePoints C.cone) (hT : T ≤ latticePoints C.cone)
    (hGS : LatticeSlices.generatedGroup S = ⊤) (hGT : LatticeSlices.generatedGroup T = ⊤)
    (hvolume : 0 < (intersectionSubset C S T hS).volume) :
    closedCone (S ⊓ T) = closedCone S ⊓ closedCone T := by
  apply le_antisymm (le_inf (closedCone_mono inf_le_left) (closedCone_mono inf_le_right))
  intro z hz
  have hzC := closedCone_subset_source C S hS (nonempty_of_generatedGroup_eq_top S hGS) hz.1
  by_cases hzero : z.2 = 0
  · have hzC' : (z.1, z.2) ∈ C.cone := hzC
    rw [hzero] at hzC'
    have hspatial : z.1 = 0 := C.zeroHeight z.1 hzC'
    have hz0 : z = 0 := Prod.ext hspatial hzero
    rw [hz0]
    exact (closedCone (S ⊓ T)).zero_mem
  · have hpos : 0 < z.2 := lt_of_le_of_ne (C.nonnegativeHeight z hzC) (Ne.symm hzero)
    have hnormS : z.2⁻¹ • z.1 ∈ body S := by
      have hscaled := (closedCone S).smul_mem (inv_nonneg.mpr hpos.le) hz.1
      have heq : z.2⁻¹ • z = (z.2⁻¹ • z.1, (1 : ℝ)) := by
        apply Prod.ext
        · rfl
        · simp [inv_mul_cancel₀ hpos.ne']
      rw [heq] at hscaled
      exact hscaled
    have hnormT : z.2⁻¹ • z.1 ∈ body T := by
      have hscaled := (closedCone T).smul_mem (inv_nonneg.mpr hpos.le) hz.2
      have heq : z.2⁻¹ • z = (z.2⁻¹ • z.1, (1 : ℝ)) := by
        apply Prod.ext
        · rfl
        · simp [inv_mul_cancel₀ hpos.ne']
      rw [heq] at hscaled
      exact hscaled
    have hnorm : z.2⁻¹ • z.1 ∈ body (S ⊓ T) := by
      rw [body_intersection_eq C S T hS hT hGS hGT hvolume]
      exact ⟨hnormS, hnormT⟩
    have hscaled := (closedCone (S ⊓ T)).smul_mem hpos.le hnorm
    have heq : z.2 • (z.2⁻¹ • z.1, (1 : ℝ)) = z := by
      apply Prod.ext
      · simp [smul_smul, mul_inv_cancel₀ hpos.ne']
      · simp
    rw [heq] at hscaled
    exact hscaled

end SGPT.AlmostSemigroup.Intersection
