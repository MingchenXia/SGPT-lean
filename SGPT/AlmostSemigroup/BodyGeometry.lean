import SGPT.AlmostSemigroup.Regularization
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Genuine full-dimensional geometry of actual source bodies

Full generation and actual finite clearing produce a translated standard
simplex inside the source. Its positive-degree normalization proves actual
full-dimensionality and strict body-volume positivity. Genuine inner-body
lattice counts force actual source points into every body neighborhood;
finite compact covers give the actual Euclidean Hausdorff limit.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.BodyGeometry

open Set Filter MeasureTheory
open scoped Topology Pointwise
open Okounkov

/-- The actual degree-one integer simplex, including its zero spatial vertex. -/
def degreeOneSimplex (n : ℕ) (i : Option (Fin n)) : (Fin n → ℤ) × ℤ :=
  (i.elim 0 (fun j ↦ Pi.single j 1), 1)

/-- Actual full generation clears one common translate of the standard integer simplex into `S`. -/
theorem exists_translated_degreeOneSimplex {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    ∃ f ∈ S, 0 < f.2 + 1 ∧ ∀ i, degreeOneSimplex n i + f ∈ S := by
  have hgroup : Set.range (degreeOneSimplex n) ⊆
      AddSubgroup.closure (S : Set ((Fin n → ℤ) × ℤ)) := by
    change Set.range (degreeOneSimplex n) ⊆ LatticeSlices.generatedGroup S
    rw [hG]
    exact Set.subset_univ _
  obtain ⟨f, hf, hclear⟩ := Conductor.exists_translate_of_finite S
    (nonempty_of_generatedGroup_eq_top S hG) (Set.finite_range _) hgroup
  have hheight : 0 ≤ f.2 := by
    have h := C.nonnegativeHeight (latticeCast n f) (hS hf)
    change (0 : ℝ) ≤ (f.2 : ℝ) at h
    exact_mod_cast h
  exact ⟨f, hf, by omega, fun i ↦ hclear _ (Set.mem_range_self i)⟩

/-- The actual source body spans the whole affine coordinate space. -/
theorem affineSpan_body_eq_top {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : affineSpan ℝ (body S) = ⊤ := by
  classical
  obtain ⟨f, _, hdegree, hclear⟩ := exists_translated_degreeOneSimplex C S hS hG
  let P := affineSpan ℝ (body S)
  let d : ℝ := (f.2 + 1 : ℤ)
  have hd : d ≠ 0 := by
    have hp : 0 < d := by
      change (0 : ℝ) < ((f.2 + 1 : ℤ) : ℝ)
      exact_mod_cast hdegree
    exact hp.ne'
  have hd' : 1 + (f.2 : ℝ) ≠ 0 := by simpa [d, add_comm] using hd
  have hpoint (i : Option (Fin n)) : normalizedPoint (degreeOneSimplex n i + f) ∈ P := by
    apply subset_affineSpan
    apply normalizedPoint_mem_heightOne _ (mem_closedCone_of_mem S (hclear i))
    change (0 : ℤ) < 1 + f.2
    omega
  have hb (i : Fin n) : (Pi.basisFun ℝ (Fin n)) i ∈ P.direction := by
    have hm := P.direction.smul_mem d
      (AffineSubspace.vsub_mem_direction (hpoint (some i)) (hpoint none))
    have heq : d • (normalizedPoint (degreeOneSimplex n (some i) + f) -
        normalizedPoint (degreeOneSimplex n none + f)) = Pi.single i (1 : ℝ) := by
      ext j
      by_cases hij : i = j
      · simp [degreeOneSimplex, normalizedPoint, Counting.integerCast, hij, d]
        field_simp [hd']
        ring
      · simp [degreeOneSimplex, normalizedPoint, Counting.integerCast, hij, d]
    change d • (normalizedPoint (degreeOneSimplex n (some i) + f) -
      normalizedPoint (degreeOneSimplex n none + f)) ∈ P.direction at hm
    rw [heq] at hm
    simpa using hm
  have hdir : P.direction = ⊤ := by
    apply top_le_iff.mp
    rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨_, hpoint none⟩).mp hdir

/-- Genuine convex full-dimensionality produces nonempty ordinary body interior. -/
theorem interior_body_nonempty {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : (interior (body S)).Nonempty :=
  (convex_body S).interior_nonempty_iff_affineSpan_eq_top.mpr (affineSpan_body_eq_top C S hS hG)

/-- SGPT `thm:HausOkounapp`: genuine full-generation source bodies have strictly positive volume. -/
theorem volume_real_body_pos {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : 0 < volume.real (body S) := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
      (interior_body_nonempty C S hS hG))
  · exact (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hG)).measure_lt_top.ne

/-- The actual source limsup volume equals its body volume under full generation. -/
theorem volume_source_eq_body {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    (sourceSubset C S hS).volume = volume.real (body S) :=
  (tendsto_source_of_generatedGroup_eq_top C S hS hG).limsup_eq

/-- The source's actual normalized limsup volume is strictly positive. -/
theorem volume_source_pos {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : 0 < (sourceSubset C S hS).volume := by
  rw [volume_source_eq_body C S hS hG]
  exact volume_real_body_pos C S hS hG

/-- The actual finite-degree spatial source points, scaled by the actual degree. -/
def normalizedSlice {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (k : ℕ) :
    Set (Fin n → ℝ) :=
  (fun x ↦ (k : ℝ)⁻¹ • Counting.integerCast x) ''
    slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)

/-- Normalized actual source points lie in the actual generated body. -/
theorem normalizedSlice_subset_body {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) {k : ℕ} (hk : 0 < k) :
    normalizedSlice S k ⊆ body S := by
  rintro _ ⟨x, hx, rfl⟩
  have hz : 0 < (k : ℤ) := by exact_mod_cast hk
  simpa only [normalizedPoint, Int.cast_natCast, body] using
    normalizedPoint_mem_heightOne (closedCone S : ConvexCone ℝ ((Fin n → ℝ) × ℝ))
      (z := (x, (k : ℤ))) (mem_closedCone_of_mem S hx) hz

/-- A positive-degree actual dilated integer point normalizes into the original body. -/
theorem normalized_integerPoint_mem {n : ℕ} {K : Set (Fin n → ℝ)} {k : ℕ} (hk : 0 < k)
    {x : Fin n → ℤ} (hx : x ∈ Counting.integerPoints ((k : ℝ) • K)) :
    (k : ℝ)⁻¹ • Counting.integerCast x ∈ K := by
  obtain ⟨y, hy, heq⟩ := hx
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← heq, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  exact hy

/-- Missing an actual inner body forces its actual lattice count into the source discrepancy. -/
theorem inner_count_le_discrepancy_of_disjoint {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    {K : Set (Fin n → ℝ)} (hcompact : IsCompact K) (hKB : K ⊆ body S)
    {k : ℕ} (hk : 0 < k) (hmiss : Disjoint (normalizedSlice S k) K) :
    (k : ℝ)⁻¹ ^ n * Counting.integerLatticeCount K k ≤
      normalizedDiscrepancy n (sourceSubset C S hS).slices
        (Regularization.regularizedSubset C S hS hne).slices k := by
  classical
  let F := (Counting.finite_integerPoints_dilate hcompact k).toFinset
  let A := sourceSubset C S hS
  let R := Regularization.regularizedSubset C S hS hne
  have hF (x : Fin n → ℤ) : x ∈ F ↔ x ∈ Counting.integerPoints ((k : ℝ) • K) := by
    simp only [F, Set.Finite.mem_toFinset]
  have hFR : F ⊆ R.slices k := by
    intro x hx
    apply (ConeSubset.mem_slices R k x).mpr
    apply (Counting.mem_slice_iff_integerPoints_heightOne _ k hk x).mpr
    obtain ⟨y, hy, heq⟩ := (hF x).mp hx
    exact ⟨y, hKB hy, heq⟩
  have hAR : A.slices k ⊆ R.slices k :=
    ConeSubset.slices_subset_of_subset A R (Regularization.le_regularizedSemigroup S) k
  have hFA : Disjoint F (A.slices k) := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxA
    exact Set.disjoint_left.mp hmiss
      ⟨x, (ConeSubset.mem_slices A k x).mp hxA, rfl⟩
      (normalized_integerPoint_mem hk ((hF x).mp hxF))
  have hc := Finset.card_le_card (Finset.union_subset hFR hAR)
  rw [Finset.card_union_of_disjoint hFA] at hc
  have hr : (F.card : ℝ) + (A.slices k).card ≤ (R.slices k).card := by exact_mod_cast hc
  have hFcard : F.card = Counting.integerLatticeCount K k :=
    (Nat.card_eq_card_finite_toFinset (Counting.finite_integerPoints_dilate hcompact k)).symm
  rw [← hFcard, Regularization.normalizedDiscrepancy_eq_sub_of_subset A R
    (Regularization.le_regularizedSemigroup S) k, ConeSubset.normalizedCardinality,
    ConeSubset.normalizedCardinality, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Every genuine positive-volume compact inner body meets every sufficiently large source degree. -/
theorem eventually_normalizedSlice_inter_nonempty {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    {K : Set (Fin n → ℝ)} (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hKB : K ⊆ body S) (hvol : 0 < volume.real K) :
    ∀ᶠ k in atTop, (normalizedSlice S k ∩ K).Nonempty := by
  have hcount := Counting.tendsto_integer_lattice_count hcompact hconvex
  have hdisc := Regularization.tendsto_regularization_discrepancy C S hS hG
  have hlo := (tendsto_order.mp hcount).1 (volume.real K / 2) (by linarith)
  have hhi := (tendsto_order.mp hdisc).2 (volume.real K / 2) (by linarith)
  filter_upwards [hlo, hhi, eventually_gt_atTop 0] with k hklo hkhi hk
  by_contra hnone
  have hmiss : Disjoint (normalizedSlice S k) K := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hnone
  have hbound := inner_count_le_discrepancy_of_disjoint C S hS
    (nonempty_of_generatedGroup_eq_top S hG) hcompact hKB hk hmiss
  exact (not_lt_of_ge hbound) (hkhi.trans hklo)

/-- Actual source slices meet every open neighborhood meeting the actual body, eventually in degree. -/
theorem eventually_normalizedSlice_inter_open_nonempty {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hUB : (body S ∩ U).Nonempty) :
    ∀ᶠ k in atTop, (normalizedSlice S k ∩ U).Nonempty := by
  obtain ⟨x, hxB, hxU⟩ := hUB
  have hclosed : IsClosed (body S) :=
    (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hG)).isClosed
  have hxcl : x ∈ closure (interior (body S)) := by
    rw [(convex_body S).closure_interior_eq_closure_of_nonempty_interior
      (interior_body_nonempty C S hS hG), hclosed.closure_eq]
    exact hxB
  obtain ⟨y, hyU, hyB⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hnhds : body S ∩ U ∈ 𝓝 y :=
    inter_mem (Filter.mem_of_superset (isOpen_interior.mem_nhds hyB) interior_subset)
      (hU.mem_nhds hyU)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  have hvol : 0 < volume.real (Metric.closedBall y r) := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
        ⟨y, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)⟩)
    · exact (isCompact_closedBall y r).measure_lt_top.ne
  have hevent := eventually_normalizedSlice_inter_nonempty C S hS hG
    (isCompact_closedBall y r) (convex_closedBall y r)
    (fun z hz ↦ (hball hz).1) hvol
  filter_upwards [hevent] with k hk
  obtain ⟨z, hzS, hzball⟩ := hk
  exact ⟨z, hzS, (hball hzball).2⟩

/-- The actual body in genuine Euclidean coordinates. -/
def euclideanBody {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm '' body S

/-- The actual degreewise normalized source convex hull, in the genuine Euclidean metric. -/
def euclideanDegreeBody {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm '' normalizedSlice S k)

/-- The source degreewise Euclidean convex hull is actually compact, including empty degrees. -/
theorem isCompact_euclideanDegreeBody {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) (k : ℕ) :
    IsCompact (euclideanDegreeBody S k) := by
  apply Set.Finite.isCompact_convexHull ℝ
  exact ((finite_source_slice C S hS (k : ℤ)).image _).image _

/-- The actual Euclidean limiting body is nonempty under genuine full generation. -/
theorem euclideanBody_nonempty {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : (euclideanBody S).Nonempty :=
  ((interior_body_nonempty C S hS hG).mono interior_subset).image _

/-- The genuine degreewise source convex hulls are nonempty at every sufficiently large degree. -/
theorem eventually_euclideanDegreeBody_nonempty {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    ∀ᶠ k in atTop, (euclideanDegreeBody S k).Nonempty := by
  have hevent := eventually_normalizedSlice_inter_nonempty C S hS hG
    (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hG))
    (convex_body S) Set.Subset.rfl (volume_real_body_pos C S hS hG)
  filter_upwards [hevent] with k hk
  obtain ⟨x, hx, _⟩ := hk
  exact ⟨_, subset_convexHull ℝ _ ⟨x, hx, rfl⟩⟩

/-- Genuine Euclidean degreewise convex hulls stay in the genuine Euclidean body. -/
theorem euclideanDegreeBody_subset_body {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) {k : ℕ} (hk : 0 < k) :
    euclideanDegreeBody S k ⊆ euclideanBody S :=
  convexHull_min (Set.image_mono (normalizedSlice_subset_body S hk))
    ((convex_body S).linear_image (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)

/-- Every actual Euclidean body point has actual normalized source points in each Euclidean ball. -/
theorem eventually_euclidean_normalizedSlice_near {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ euclideanBody S) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k in atTop, ∃ y ∈ (EuclideanSpace.equiv (Fin n) ℝ).symm '' normalizedSlice S k,
      dist x y < r := by
  obtain ⟨z, hz, rfl⟩ := hx
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hU : IsOpen (e ⁻¹' Metric.ball (e z) r) := Metric.isOpen_ball.preimage e.continuous
  have hUB : (body S ∩ e ⁻¹' Metric.ball (e z) r).Nonempty :=
    ⟨z, hz, Metric.mem_ball_self hr⟩
  have hevent := eventually_normalizedSlice_inter_open_nonempty C S hS hG hU hUB
  filter_upwards [hevent] with k hk
  obtain ⟨y, hyS, hyU⟩ := hk
  change dist (e y) (e z) < r at hyU
  exact ⟨e y, ⟨y, hyS, rfl⟩, by simpa only [dist_comm] using hyU⟩

/-- SGPT `thm:HausOkounapp`: genuine Euclidean Hausdorff convergence of the actual degreewise bodies. -/
theorem tendsto_hausdorffDist_degreeBody {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    Tendsto (fun k ↦ Metric.hausdorffDist (euclideanDegreeBody S k) (euclideanBody S))
      atTop (𝓝 0) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall fun k ↦ hr.trans_le Metric.hausdorffDist_nonneg
  · intro ε hε
    let r := ε / 3
    have hr : 0 < r := by dsimp [r]; linarith
    have hcompact : IsCompact (euclideanBody S) :=
      (isCompact_body C S hS (nonempty_of_generatedGroup_eq_top S hG)).image
        (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
    obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
      (fun x : euclideanBody S ↦ Metric.ball x.val r) (fun _ ↦ Metric.isOpen_ball)
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hr⟩)
    have hevent (x : euclideanBody S) :=
      eventually_euclidean_normalizedSlice_near C S hS hG x.property hr
    have hall : ∀ᶠ k in atTop, ∀ x ∈ t,
        ∃ y ∈ (EuclideanSpace.equiv (Fin n) ℝ).symm '' normalizedSlice S k,
          dist x.val y < r := by
      exact (Filter.eventually_all_finset t).mpr (fun x _ ↦ hevent x)
    filter_upwards [hall, eventually_gt_atTop 0] with k hk hkpos
    have hbound : Metric.hausdorffDist (euclideanDegreeBody S k) (euclideanBody S) ≤ 2 * r := by
      apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
      · intro x hx
        exact ⟨x, euclideanDegreeBody_subset_body S hkpos hx, by simp; positivity⟩
      · intro x hx
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht hx)
        obtain ⟨y, hy, hcy⟩ := hk c hc
        refine ⟨y, subset_convexHull ℝ _ hy, ?_⟩
        have hxc' : dist x c.val < r := hxc
        exact (dist_triangle x c.val y).trans (by linarith)
    have hsmall : 2 * r < ε := by dsimp [r]; linarith
    exact hbound.trans_lt hsmall

end SGPT.AlmostSemigroup.BodyGeometry
