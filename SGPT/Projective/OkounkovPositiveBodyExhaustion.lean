import SGPT.AlmostSemigroup.BodyGeometry

/-! SAME original body exhaustion/interior BEFORE an admissible ambient cone.
Blueprint: okounkov-positive-body-exhaustion.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set Filter MeasureTheory SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.BodyGeometry
open scoped Pointwise Topology

/-- Every actual positive-height cone-hull point normalizes into the actual source convex hull. -/
theorem normalized_mem_convexHull_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    {z : (Fin n → ℝ) × ℝ}
    (hz : z ∈ PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))))
    (hheight : 0 < z.2) : z.2⁻¹ • z.1 ∈ convexHull ℝ (normalizedSource S) := by
  let H := convexHull ℝ (normalizedSource S)
  have hle : PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) ≤
      coneOver H (convex_convexHull ℝ _) := by
    apply Submodule.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    apply (mem_coneOver H (convex_convexHull ℝ _) (latticeCast n x)).mpr
    by_cases hzero : x = 0
    · subst x
      exact Or.inl (by apply Prod.ext <;> simp [latticeCast]; rfl)
    · have hpos := (hpositive x hx).resolve_left hzero
      refine Or.inr ⟨by change (0 : ℝ) < (x.2 : ℝ); exact_mod_cast hpos, ?_⟩
      exact subset_convexHull ℝ _ ⟨x, ⟨hx, hpos⟩, rfl⟩
  rcases (mem_coneOver H (convex_convexHull ℝ _) z).mp (hle hz) with hzero | hnorm
  · simp [hzero] at hheight
  · exact hnorm.2

/-- The actual generated body is the closure of the genuine positive-degree normalized hull. -/
theorem body_eq_closure_convexHull_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2) :
    body S = closure (convexHull ℝ (normalizedSource S)) := by
  have hclosed : IsClosed (body S) :=
    (isClosed_closedCone S).preimage (continuous_id.prodMk continuous_const)
  have hnorm : normalizedSource S ⊆ body S := by
    rintro y ⟨z, ⟨hz, hpos⟩, rfl⟩
    exact normalizedPoint_mem_heightOne _ (mem_closedCone_of_mem S hz) hpos
  apply Set.Subset.antisymm ?_ (closure_minimal (convexHull_min hnorm (convex_body S)) hclosed)
  intro x hx
  let P : Set ((Fin n → ℝ) × ℝ) := {z | 0 < z.2}
  let T : Set ((Fin n → ℝ) × ℝ) :=
    (PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) :
      Set ((Fin n → ℝ) × ℝ)) ∩ P
  have hP : IsOpen P := isOpen_lt continuous_const continuous_snd
  have hxT : (x, (1 : ℝ)) ∈ closure T := by
    apply mem_closure_iff.mpr
    intro o ho hxo
    obtain ⟨z, hzo, hzcone⟩ := mem_closure_iff.mp hx (o ∩ P) (ho.inter hP)
      ⟨hxo, by change (0 : ℝ) < 1; exact zero_lt_one⟩
    exact ⟨z, hzo.1, hzcone, hzo.2⟩
  have hcontinuous : ContinuousAt (fun z : (Fin n → ℝ) × ℝ => z.2⁻¹ • z.1) (x, 1) :=
    (continuous_snd.continuousAt.inv₀ one_ne_zero).smul continuous_fst.continuousAt
  have hmap : MapsTo (fun z : (Fin n → ℝ) × ℝ => z.2⁻¹ • z.1) T
      (convexHull ℝ (normalizedSource S)) := by
    intro z hz
    exact normalized_mem_convexHull_of_positiveHeight S hpositive hz.1 hz.2
  simpa only [inv_one, one_smul] using hcontinuous.continuousWithinAt.mem_closure hxT hmap

/-- EXACT actual original volume exhaustion, before any ambient cone or boundedness input. -/
theorem volume_body_eq_iSup_inner_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2) :
    volume (body S) = ⨆ t : Finset (positiveSource S), volume (finiteInnerBody S t) := by
  rw [body_eq_closure_convexHull_of_positiveHeight S hpositive,
    measure_closure_of_null_frontier ((convex_convexHull ℝ (normalizedSource S)).addHaar_frontier volume),
    convexHull_normalizedSource_eq_iUnion S]
  exact (finiteInnerBody_directed S).measure_iUnion

/-- Actual full generation clears one common translate of the standard integer simplex into `S`. -/
theorem exists_translated_degreeOneSimplex_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
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
    rcases hpositive f hf with hzero | hpos
    · rw [hzero]; simp
    · exact hpos.le
  exact ⟨f, hf, by omega, fun i ↦ hclear _ (Set.mem_range_self i)⟩

/-- The actual source body spans the whole affine coordinate space. -/
theorem affineSpan_body_eq_top_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤) : affineSpan ℝ (body S) = ⊤ := by
  classical
  obtain ⟨f, _, hdegree, hclear⟩ := exists_translated_degreeOneSimplex_of_positiveHeight S hpositive hG
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
theorem interior_body_nonempty_of_positiveHeight {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤) : (interior (body S)).Nonempty :=
  (convex_body S).interior_nonempty_iff_affineSpan_eq_top.mpr (affineSpan_body_eq_top_of_positiveHeight S hpositive hG)


end SGPT.Okounkov.BodyFromGrowth
