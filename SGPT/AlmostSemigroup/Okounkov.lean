import SGPT.AlmostSemigroup.LatticeSlices
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Combination

/-!
# Actual semigroup growth from native conductors and body exhaustion

The coordinate transport connects the existing generated-group conductor to
the book's actual `(x, degree)` semigroup. Actual positive-degree normalized
source hulls exhaust the generated body and its measure. The actual source
counting limits follow from that exhaustion and the produced conductors,
including divisible-degree independence, the global limsup identity and
the full-generation body-volume identity. No eventual membership, density,
volume exhaustion or source counting convergence is assumed.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Okounkov

open Set
open Filter MeasureTheory
open scoped Pointwise Topology

/-- The coordinate equivalence puts degree first and the original spatial coordinates after it. -/
def gradedCoordinates (R : Type*) [Semiring R] (n : ℕ) :
    ((Fin n → R) × R) ≃ₗ[R] (Fin (n + 1) → R) :=
  (LinearEquiv.prodComm R (Fin n → R) R).trans
    (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R))

/-- The real and integer coordinate transports preserve the source casting exactly. -/
theorem gradedCoordinates_cast {n : ℕ} (z : (Fin n → ℤ) × ℤ) :
    gradedCoordinates ℝ n (latticeCast n z) =
      Counting.integerCast (gradedCoordinates ℤ n z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- The actual finite cone in the book's graded real coordinate space. -/
def finiteCone {n m : ℕ} (v : Fin m → (Fin n → ℤ) × ℤ) :
    PointedCone ℝ ((Fin n → ℝ) × ℝ) :=
  PointedCone.hull ℝ (Set.range (latticeCast n ∘ v))

/-- The coordinate image of the actual native cone is the checked vector-coordinate cone. -/
theorem map_finiteCone {n m : ℕ} (v : Fin m → (Fin n → ℤ) × ℤ) :
    (finiteCone v).map (gradedCoordinates ℝ n).toLinearMap =
      Conductor.generatedCone (gradedCoordinates ℤ n ∘ v) := by
  change (Submodule.span {r : ℝ // 0 ≤ r} (Set.range (latticeCast n ∘ v))).map
    ((gradedCoordinates ℝ n).toLinearMap :
      ((Fin n → ℝ) × ℝ) →ₗ[{r : ℝ // 0 ≤ r}] (Fin (n + 1) → ℝ)) = _
  rw [Submodule.map_span]
  change Submodule.span {r : ℝ // 0 ≤ r} _ =
    Submodule.span {r : ℝ // 0 ≤ r}
      (Set.range (Counting.integerCast ∘ gradedCoordinates ℤ n ∘ v))
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, hz⟩
    exact ⟨i, (gradedCoordinates_cast (v i)).symm.trans hz⟩
  · rintro ⟨i, rfl⟩
    exact ⟨latticeCast n (v i), ⟨i, rfl⟩, gradedCoordinates_cast (v i)⟩

/-- Genuine generated-group membership transports through the coordinate equivalence. -/
theorem gradedCoordinates_mem_generated {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) {x : (Fin n → ℤ) × ℤ}
    (hx : x ∈ LatticeSlices.generatedGroup S) :
    gradedCoordinates ℤ n x ∈ AddSubgroup.closure
      (S.map (gradedCoordinates ℤ n).toAddMonoidHom.toAddHom : Set (Fin (n + 1) → ℤ)) := by
  have hle : LatticeSlices.generatedGroup S ≤
      (AddSubgroup.closure (S.map (gradedCoordinates ℤ n).toAddMonoidHom.toAddHom : Set (Fin (n + 1) → ℤ))).comap
        (gradedCoordinates ℤ n).toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).mpr
    intro z hz
    exact AddSubgroup.subset_closure ⟨z, hz, rfl⟩
  exact hle hx

/-- An actual source graded conductor follows from the checked vector-coordinate conductor. -/
theorem exists_graded_conductor {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    (v : Fin m → (Fin n → ℤ) × ℤ) (hv : ∀ i, v i ∈ S) :
    ∃ f ∈ S, ∀ x ∈ LatticeSlices.generatedGroup S,
      latticeCast n x ∈ finiteCone v → x + f ∈ S := by
  let e := (gradedCoordinates ℤ n).toAddEquiv
  let S' := S.map e.toAddMonoidHom.toAddHom
  have hne' : (S' : Set (Fin (n + 1) → ℤ)).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨e z, z, hz, rfl⟩
  obtain ⟨f', hf', hconductor⟩ := Conductor.exists_conductor_in_generated_group S' hne'
    (e ∘ v) (fun i => ⟨v i, hv i, rfl⟩)
  obtain ⟨f, hf, heq⟩ := hf'
  refine ⟨f, hf, ?_⟩
  intro x hx hcone
  have hx' : e x ∈ AddSubgroup.closure (S' : Set (Fin (n + 1) → ℤ)) := gradedCoordinates_mem_generated S hx
  have hc' : Counting.integerCast (e x) ∈ Conductor.generatedCone (e ∘ v) := by
    change Counting.integerCast (gradedCoordinates ℤ n x) ∈
      Conductor.generatedCone (gradedCoordinates ℤ n ∘ v)
    rw [← map_finiteCone]
    exact ⟨latticeCast n x, hcone, gradedCoordinates_cast x⟩
  obtain ⟨y, hy, hxy⟩ := hconductor (e x) hx' hc'
  have hyx : y = x + f := by
    apply e.injective
    change e y = e x + f' at hxy
    change e f = f' at heq
    rw [hxy, e.map_add, heq]
  exact hyx ▸ hy

/-- The actual degree slice of a finite cone and the actual generated subgroup. -/
def finiteConeGroupSlice {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (v : Fin m → (Fin n → ℤ) × ℤ)
    (d : ℤ) : Set (Fin n → ℤ) :=
  {x | (x, d) ∈ LatticeSlices.generatedGroup S ∧ latticeCast n (x, d) ∈ finiteCone v}

/-- Addition of the produced conductor gives an actual inclusion of the shifted slices. -/
theorem conductor_slice_mapsTo {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (v : Fin m → (Fin n → ℤ) × ℤ)
    {f : (Fin n → ℤ) × ℤ}
    (hconductor : ∀ z ∈ LatticeSlices.generatedGroup S,
      latticeCast n z ∈ finiteCone v → z + f ∈ S) (d : ℤ) :
    Set.MapsTo (fun x => x + f.1) (finiteConeGroupSlice S v d)
      (slice (S : Set ((Fin n → ℤ) × ℤ)) (d + f.2)) := by
  intro x hx
  exact hconductor (x, d) hx.1 hx.2

/-- The lower slice comparison is a genuine translated injection, not a counting certificate. -/
def conductorSliceEmbedding {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (v : Fin m → (Fin n → ℤ) × ℤ)
    {f : (Fin n → ℤ) × ℤ}
    (hconductor : ∀ z ∈ LatticeSlices.generatedGroup S,
      latticeCast n z ∈ finiteCone v → z + f ∈ S) (d : ℤ) :
    finiteConeGroupSlice S v d ↪ slice (S : Set ((Fin n → ℤ) × ℤ)) (d + f.2) where
  toFun x := ⟨x.val + f.1, conductor_slice_mapsTo S v hconductor d x.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val h)

/-- The actual conductor gives the actual finite degreewise lower cardinality bound. -/
theorem conductor_slice_card_le {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (v : Fin m → (Fin n → ℤ) × ℤ)
    {f : (Fin n → ℤ) × ℤ}
    (hconductor : ∀ z ∈ LatticeSlices.generatedGroup S,
      latticeCast n z ∈ finiteCone v → z + f ∈ S) (d : ℤ)
    (hfinite : (slice (S : Set ((Fin n → ℤ) × ℤ)) (d + f.2)).Finite) :
    Nat.card (finiteConeGroupSlice S v d) ≤ Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (d + f.2)) := by
  let := hfinite.to_subtype
  exact Nat.card_le_card_of_injective (conductorSliceEmbedding S v hconductor d)
    (conductorSliceEmbedding S v hconductor d).injective

/-- Every actual integer degree slice is finite under the original cone hypotheses. -/
theorem finite_source_slice {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) (d : ℤ) :
    (slice (S : Set ((Fin n → ℤ) × ℤ)) d).Finite := by
  by_cases hd : 0 ≤ d
  · have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd
    rw [← hcast]
    exact (ConeSubset.finite_slice ⟨(S : Set ((Fin n → ℤ) × ℤ)), hS⟩ d.toNat)
  · have hempty : slice (S : Set ((Fin n → ℤ) × ℤ)) d = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := C.nonnegativeHeight _ (hS hx)
      change 0 ≤ (d : ℝ) at h
      exact hd (by exact_mod_cast h)
    rw [hempty]
    exact Set.finite_empty

/-- Original source hypotheses produce one genuine conductor and all actual lower slice bounds. -/
theorem exists_graded_conductor_slice_bounds {n m : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    (v : Fin m → (Fin n → ℤ) × ℤ) (hv : ∀ i, v i ∈ S) :
    ∃ f ∈ S, f.2 ∈ LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) ∧
      ∀ d : ℤ, Nat.card (finiteConeGroupSlice S v d) ≤
        Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (d + f.2)) := by
  obtain ⟨f, hf, hconductor⟩ := exists_graded_conductor S hne v hv
  exact ⟨f, hf, LatticeSlices.degree_mem_generated S hf,
    fun d => conductor_slice_card_le S v hconductor d (finite_source_slice C S hS _)⟩

/-- The actual source closed cone generated by the semigroup and zero. -/
def closedCone {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    PointedCone ℝ ((Fin n → ℝ) × ℝ) :=
  (PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ)))).closure

/-- Actual semigroup points belong to their actual closed generated cone. -/
theorem mem_closedCone_of_mem {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    {z : (Fin n → ℤ) × ℤ} (hz : z ∈ S) : latticeCast n z ∈ closedCone S :=
  subset_closure (PointedCone.subset_hull ⟨z, hz, rfl⟩)

theorem isClosed_closedCone {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    IsClosed (closedCone S : Set ((Fin n → ℝ) × ℝ)) := isClosed_closure

/-- Nonemptiness and the original closed cone assumptions give the actual generated-cone inclusion. -/
theorem closedCone_subset_source {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    (closedCone S : Set ((Fin n → ℝ) × ℝ)) ⊆ C.cone := by
  obtain ⟨z, hz⟩ := hne
  have hC : C.cone.Pointed :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨latticeCast n z, hS hz⟩ C.closed
  have hh : PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) ≤
      C.cone.toPointedCone hC := by
    apply Submodule.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    exact hS hx
  exact closure_minimal hh C.closed

/-- The source generated cone inherits admissibility from the original source cone. -/
def generatedAdmissibleCone {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) : AdmissibleCone n where
  cone := closedCone S
  closed := isClosed_closedCone S
  nonnegativeHeight z hz := C.nonnegativeHeight z (closedCone_subset_source C S hS hne hz)
  zeroHeight x hx := C.zeroHeight x (closedCone_subset_source C S hS hne hx)

/-- The actual source Okounkov body. -/
def body {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) : Set (Fin n → ℝ) :=
  heightOne (closedCone S : ConvexCone ℝ ((Fin n → ℝ) × ℝ))

/-- Compactness is produced from the original geometric hypotheses. -/
theorem isCompact_body {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) : IsCompact (body S) :=
  isCompact_heightOne (generatedAdmissibleCone C S hS hne).cone
    (generatedAdmissibleCone C S hS hne).closed
    (generatedAdmissibleCone C S hS hne).nonnegativeHeight
    (generatedAdmissibleCone C S hS hne).zeroHeight

theorem convex_body {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Convex ℝ (body S) := Counting.convex_heightOne _

/-- The actual source semigroup lies inside the actual generated-group saturation. -/
theorem source_slice_subset_groupBodySlice {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (k : ℕ) (hk : 0 < k) :
    slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) ⊆
      LatticeSlices.groupBodySlice (LatticeSlices.generatedGroup S) (body S) k := by
  intro x hx
  exact ⟨AddSubgroup.subset_closure hx,
    (Counting.mem_slice_iff_integerPoints_heightOne _ k hk x).mp (mem_closedCone_of_mem S hx)⟩

/-- The actual normalized point of a positive-degree source lattice vector. -/
def normalizedPoint {n : ℕ} (z : (Fin n → ℤ) × ℤ) : Fin n → ℝ :=
  (z.2 : ℝ)⁻¹ • Counting.integerCast z.1

/-- The actual finite inner body used in the source conductor lower bound. -/
def innerBody {n m : ℕ} (v : Fin m → (Fin n → ℤ) × ℤ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range (normalizedPoint ∘ v))

theorem isCompact_innerBody {n m : ℕ} (v : Fin m → (Fin n → ℤ) × ℤ) :
    IsCompact (innerBody v) := (Set.finite_range _).isCompact_convexHull ℝ

theorem convex_innerBody {n m : ℕ} (v : Fin m → (Fin n → ℤ) × ℤ) :
    Convex ℝ (innerBody v) := convex_convexHull ℝ _

/-- Positive scaling puts the actual normalized point into its cone's height-one section. -/
theorem normalizedPoint_mem_heightOne {n : ℕ}
    (K : ConvexCone ℝ ((Fin n → ℝ) × ℝ))
    {z : (Fin n → ℤ) × ℤ} (hz : latticeCast n z ∈ K) (hdeg : 0 < z.2) :
    normalizedPoint z ∈ heightOne K := by
  have hpos : 0 < (z.2 : ℝ) := by exact_mod_cast hdeg
  change (normalizedPoint z, (1 : ℝ)) ∈ K
  have heq : (normalizedPoint z, (1 : ℝ)) = (z.2 : ℝ)⁻¹ • latticeCast n z := by
    apply Prod.ext
    · rfl
    · simp [latticeCast, inv_mul_cancel₀ hpos.ne']
  rw [heq]
  exact K.smul_mem (inv_pos.mpr hpos) hz

/-- Every finite inner body lies in the actual finite cone section. -/
theorem innerBody_subset_heightOne {n m : ℕ}
    (v : Fin m → (Fin n → ℤ) × ℤ) (hdeg : ∀ i, 0 < (v i).2) :
    innerBody v ⊆ heightOne (finiteCone v : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) := by
  apply convexHull_min ?_ (Counting.convex_heightOne _)
  rintro x ⟨i, rfl⟩
  exact normalizedPoint_mem_heightOne _ (PointedCone.subset_hull ⟨i, rfl⟩) (hdeg i)

/-- Actual finite source bodies are contained in the actual full source Okounkov body. -/
theorem innerBody_subset_body {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (v : Fin m → (Fin n → ℤ) × ℤ) (hv : ∀ i, v i ∈ S) (hdeg : ∀ i, 0 < (v i).2) :
    innerBody v ⊆ body S := by
  apply convexHull_min ?_ (convex_body S)
  rintro x ⟨i, rfl⟩
  exact normalizedPoint_mem_heightOne _ (mem_closedCone_of_mem S (hv i)) (hdeg i)

/-- An actual group point in a dilated inner body belongs to the actual finite cone slice. -/
theorem groupBodySlice_inner_subset {n m : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (v : Fin m → (Fin n → ℤ) × ℤ) (hdeg : ∀ i, 0 < (v i).2)
    (d : ℕ) (hd : 0 < d) :
    LatticeSlices.groupBodySlice (LatticeSlices.generatedGroup S) (innerBody v) d ⊆
      finiteConeGroupSlice S v (d : ℤ) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change (x, (d : ℤ)) ∈ latticePoints
    (finiteCone v : ConvexCone ℝ ((Fin n → ℝ) × ℝ))
  apply (Counting.mem_slice_iff_integerPoints_heightOne _ d hd x).mpr
  exact Set.smul_set_mono (innerBody_subset_heightOne v hdeg) hx.2

/-- Original source hypotheses produce a genuine translated injection for every actual inner-body slice. -/
theorem exists_inner_slice_lower_bound {n m : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    (v : Fin m → (Fin n → ℤ) × ℤ) (hv : ∀ i, v i ∈ S)
    (hdeg : ∀ i, 0 < (v i).2) :
    ∃ f ∈ S, f.2 ∈ LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) ∧
      ∀ d : ℕ, 0 < d →
        Nat.card (LatticeSlices.groupBodySlice (LatticeSlices.generatedGroup S) (innerBody v) d) ≤
          Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) ((d : ℤ) + f.2)) := by
  obtain ⟨f, hf, hconductor⟩ := exists_graded_conductor S hne v hv
  refine ⟨f, hf, LatticeSlices.degree_mem_generated S hf, ?_⟩
  intro d hd
  let := (finite_source_slice C S hS ((d : ℤ) + f.2)).to_subtype
  let e₀ : LatticeSlices.groupBodySlice (LatticeSlices.generatedGroup S) (innerBody v) d ↪
      finiteConeGroupSlice S v (d : ℤ) :=
    ⟨Set.inclusion (groupBodySlice_inner_subset S v hdeg d hd), Set.inclusion_injective _⟩
  let e := e₀.trans (conductorSliceEmbedding S v hconductor (d : ℤ))
  exact Nat.card_le_card_of_injective e e.injective

/-- The actual source semigroup as an allowed subset of its original source cone. -/
def sourceSubset {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) : ConeSubset C :=
  ⟨(S : Set ((Fin n → ℤ) × ℤ)), hS⟩

theorem card_sourceSubset_slices {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) (k : ℕ) :
    ((sourceSubset C S hS).slices k).card =
      Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) :=
  (Nat.card_eq_card_finite_toFinset ((sourceSubset C S hS).finite_slice k)).symm

/-- The produced source conductor degree is an actual nonnegative multiple of the period. -/
theorem conductor_degree_nat_multiple {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    {a : ℕ} (ha : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ))
    {f : (Fin n → ℤ) × ℤ} (hf : f ∈ S) :
    ∃ b : ℕ, f.2 = ((b * a : ℕ) : ℤ) := by
  have hnonneg : 0 ≤ f.2 := by
    have h := C.nonnegativeHeight _ (hS hf)
    change 0 ≤ (f.2 : ℝ) at h
    exact_mod_cast h
  have hcast : (f.2.toNat : ℤ) = f.2 := Int.toNat_of_nonneg hnonneg
  have hdiv : a ∣ f.2.toNat := Int.natCast_dvd_natCast.mp
    (hcast.symm ▸ LatticeSlices.degree_dvd_of_mem S ha hf)
  obtain ⟨b, hb⟩ := hdiv
  exact ⟨b, by rw [← hcast, hb, Nat.mul_comm]⟩

/-- A fixed conductor shift changes actual normalized counts by a ratio tending to one. -/
theorem tendsto_shifted_normalization {n a b : ℕ} (ha : 0 < a)
    (c : ℕ → ℕ) {L : ℝ}
    (h : Tendsto (fun k : ℕ => (((k * a : ℕ) : ℝ)⁻¹ ^ n) * (c k : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ => ((((k + b) * a : ℕ) : ℝ)⁻¹ ^ n) * (c k : ℝ))
      atTop (𝓝 L) := by
  have hr : Tendsto (fun k : ℕ => ((k : ℝ) / ((k : ℝ) + (b : ℝ))) ^ n)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_natCast_div_add_atTop (b : ℝ)).pow n
  have hprod := hr.mul h
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hkb0 : (k : ℝ) + (b : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul, Nat.cast_add, div_pow, mul_inv_rev, mul_pow]
  field_simp [hk0, ha0, hkb0]
  calc
    (k : ℝ) ^ n * (1 / (k : ℝ)) ^ n * (c k : ℝ) = (c k : ℝ) := by
      rw [← mul_pow]
      simp [hk0]
    _ = ((k : ℝ) + (b : ℝ)) ^ n * (c k : ℝ) * (1 / ((k : ℝ) + (b : ℝ))) ^ n := by
      rw [mul_right_comm, ← mul_pow]
      simp [hkb0]

/-- Genuine source conductors yield convergent lower sequences under the actual period counts. -/
theorem exists_asymptotic_inner_lower_bound {n m : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    [IsZLattice ℝ (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S))]
    {β : Fin n → ℤ} {a : ℕ} (ha : 0 < a)
    (hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ)) (hβ : (β, (a : ℤ)) ∈ LatticeSlices.generatedGroup S)
    (v : Fin m → (Fin n → ℤ) × ℤ) (hv : ∀ i, v i ∈ S) (hdeg : ∀ i, 0 < (v i).2) :
    ∃ b : ℕ, ∃ lower : ℕ → ℝ,
      Tendsto lower atTop (𝓝 (MeasureTheory.volume.real (innerBody v) /
        ZLattice.covolume (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)))) ∧
      ∀ᶠ k in atTop, lower k ≤ (sourceSubset C S hS).normalizedCardinality ((k + b) * a) := by
  obtain ⟨f, hf, _, hbound⟩ := exists_inner_slice_lower_bound C S hS hne v hv hdeg
  obtain ⟨b, hb⟩ := conductor_degree_nat_multiple C S hS hperiod hf
  let c : ℕ → ℕ := fun k =>
    Nat.card (LatticeSlices.groupBodySlice (LatticeSlices.generatedGroup S) (innerBody v) (k * a))
  refine ⟨b, fun k => ((((k + b) * a : ℕ) : ℝ)⁻¹ ^ n) * (c k : ℝ), ?_, ?_⟩
  · exact tendsto_shifted_normalization ha c
      (LatticeSlices.tendsto_groupBodySlice (LatticeSlices.generatedGroup S)
        (isCompact_innerBody v) (convex_innerBody v) hβ ha)
  · filter_upwards [eventually_gt_atTop 0] with k hk
    rw [ConeSubset.normalizedCardinality, card_sourceSubset_slices]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
    have hdegree : (((k + b) * a : ℕ) : ℤ) = ((k * a : ℕ) : ℤ) + f.2 := by
      rw [hb]
      simp [Nat.add_mul, Nat.cast_add]
    rw [hdegree]
    exact Nat.cast_le.mpr (hbound (k * a) (Nat.mul_pos hk ha))

/-- The actual linear projection along the normalized degree lift. -/
def centerProjection {n : ℕ} (β : Fin n → ℤ) (a : ℕ) :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.fst ℝ (Fin n → ℝ) ℝ -
    (LinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight ((a : ℝ)⁻¹ • Counting.integerCast β)

/-- The actual degree period makes projection of every group point genuinely horizontal. -/
theorem centerProjection_group_mem_horizontal {n : ℕ}
    (G : AddSubgroup ((Fin n → ℤ) × ℤ)) {β : Fin n → ℤ} {a : ℕ}
    (ha : 0 < a) (hperiod : LatticeSlices.degreeGroup G = AddSubgroup.zmultiples (a : ℤ))
    (hβ : (β, (a : ℤ)) ∈ G) {z : (Fin n → ℤ) × ℤ} (hz : z ∈ G) :
    centerProjection β a (latticeCast n z) ∈ LatticeSlices.horizontalLattice G := by
  have hdegree : z.2 ∈ LatticeSlices.degreeGroup G :=
    (LatticeSlices.mem_degreeGroup_iff G z.2).mpr ⟨z.1, hz⟩
  rw [hperiod] at hdegree
  obtain ⟨k, hk⟩ := Int.mem_zmultiples_iff.mp hdegree
  have hzk : (z.1, k * (a : ℤ)) ∈ G := by
    have hz' : (z.1, z.2) ∈ G := hz
    rw [hk] at hz'
    simpa only [mul_comm] using hz'
  have hhor := (LatticeSlices.mem_group_slice_mul_iff G hβ k).mp hzk
  apply (LatticeSlices.mem_horizontalLattice_iff G _).mpr
  refine ⟨z.1 - k • β, hhor, ?_⟩
  rw [LatticeSlices.integerCast_sub, LatticeSlices.integerCast_zsmul]
  change Counting.integerCast z.1 - (k : ℝ) • Counting.integerCast β =
    Counting.integerCast z.1 - (z.2 : ℝ) • ((a : ℝ)⁻¹ • Counting.integerCast β)
  rw [hk, Int.cast_mul, smul_smul]
  congr 2
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  simp

/-- Actual cone generation and closure force the centered source body into its actual horizontal span. -/
theorem centered_body_subset_horizontal_span {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) {β : Fin n → ℤ} {a : ℕ}
    (ha : 0 < a)
    (hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ))
    (hβ : (β, (a : ℤ)) ∈ LatticeSlices.generatedGroup S) :
    LatticeSlices.centeredBody (body S) β a ⊆
      Submodule.span ℝ (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S) :
        Set (Fin n → ℝ)) := by
  let V := Submodule.span ℝ
    (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S) : Set (Fin n → ℝ))
  let P := centerProjection β a
  have hspan : PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) ≤
      (V.comap P).restrictScalars {r : ℝ // 0 ≤ r} := by
    apply Submodule.span_le.mpr
    rintro y ⟨z, hz, rfl⟩
    exact Submodule.subset_span (centerProjection_group_mem_horizontal
      (LatticeSlices.generatedGroup S) ha hperiod hβ (AddSubgroup.subset_closure hz))
  have hclosed : IsClosed ((V.comap P : Submodule ℝ ((Fin n → ℝ) × ℝ)) :
      Set ((Fin n → ℝ) × ℝ)) :=
    V.closed_of_finiteDimensional.preimage P.continuous_of_finiteDimensional
  have hcone : (closedCone S : Set ((Fin n → ℝ) × ℝ)) ⊆ V.comap P :=
    closure_minimal hspan hclosed
  rintro y ⟨x, hx, rfl⟩
  have h := hcone hx
  change x - (1 : ℝ) • ((a : ℝ)⁻¹ • Counting.integerCast β) ∈ V at h
  apply SetLike.mem_coe.mpr
  change x - (a : ℝ)⁻¹ • Counting.integerCast β ∈ V
  simpa only [one_smul] using h

/-- Zero actual body volume gives a true all-degree source counting limit. -/
theorem tendsto_source_normalizedCardinality_of_volume_zero {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    (hvolume : MeasureTheory.volume.real (body S) = 0) :
    Tendsto (sourceSubset C S hS).normalizedCardinality atTop (𝓝 0) := by
  let A := generatedAdmissibleCone C S hS hne
  have hSA : S ≤ latticePoints A.cone := fun _ hz => mem_closedCone_of_mem S hz
  have h := Counting.tendsto_cone_lattice_slices A
  change Tendsto _ atTop (𝓝 (MeasureTheory.volume.real (body S))) at h
  rw [hvolume] at h
  apply squeeze_zero (fun k => ConeSubset.normalizedCardinality_nonneg _ k) ?_ h
  intro k
  have heq : (sourceSubset C S hS).normalizedCardinality k =
      (sourceSubset A S hSA).normalizedCardinality k := by
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality,
      card_sourceSubset_slices, card_sourceSubset_slices]
  rw [heq]
  exact ConeSubset.normalizedCardinality_mono (sourceSubset A S hSA) (Counting.coneSubset A)
    (fun _ hz => hSA hz : (sourceSubset A S hSA).val ⊆ (Counting.coneSubset A).val) k

/-- With only the zero source point, all positive-degree counts actually vanish. -/
theorem tendsto_source_normalizedCardinality_of_no_nonzero {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hzero : ∀ z ∈ S, z = 0) :
    Tendsto (sourceSubset C S hS).normalizedCardinality atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hs : slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := congrArg Prod.snd (hzero (x, (k : ℤ)) hx)
    change (k : ℤ) = 0 at h
    have hk0 : k = 0 := by exact_mod_cast h
    omega
  rw [ConeSubset.normalizedCardinality, card_sourceSubset_slices, hs]
  simp

/-- The original lower-rank source case has an actual limit through all degrees. -/
theorem tendsto_source_normalizedCardinality_of_lower_rank {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hproper : Submodule.span ℝ
      (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S) : Set (Fin n → ℝ)) ≠ ⊤) :
    Tendsto (sourceSubset C S hS).normalizedCardinality atTop (𝓝 0) := by
  by_cases hnonzero : ∃ z ∈ S, z ≠ 0
  · obtain ⟨a, ha, hperiod, β, hβ⟩ := LatticeSlices.exists_semigroup_degree_period C S hS hnonzero
    have hvol : MeasureTheory.volume (LatticeSlices.centeredBody (body S) β a) = 0 :=
      measure_mono_null (centered_body_subset_horizontal_span S ha hperiod hβ)
        (Measure.addHaar_submodule MeasureTheory.volume _ hproper)
    have hreal : MeasureTheory.volume.real (body S) = 0 := by
      rw [← LatticeSlices.volume_centeredBody (body S) β a, Measure.real, hvol, ENNReal.toReal_zero]
    obtain ⟨z, hz, _⟩ := hnonzero
    exact tendsto_source_normalizedCardinality_of_volume_zero C S hS ⟨z, hz⟩ hreal
  · apply tendsto_source_normalizedCardinality_of_no_nonzero C S hS
    simpa only [not_exists, not_and, not_not] using hnonzero

/-- The actual source points whose degrees are positive. -/
def positiveSource {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Set ((Fin n → ℤ) × ℤ) := {z | z ∈ S ∧ 0 < z.2}

/-- Zero-degree source points are omitted from the actual normalized source set. -/
def normalizedSource {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Set (Fin n → ℝ) := normalizedPoint '' positiveSource S

/-- The genuine pointed cone over a convex height-one body. -/
def coneOver {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) : PointedCone ℝ (E × ℝ) :=
  let Q : ConvexCone ℝ (E × ℝ) := {
    carrier := {z | z = 0 ∨ 0 < z.2 ∧ z.2⁻¹ • z.1 ∈ K}
    smul_mem' := by
      intro c hc x hx
      rcases hx with rfl | ⟨hheight, hnorm⟩
      · exact Or.inl (smul_zero c)
      · refine Or.inr ⟨mul_pos hc hheight, ?_⟩
        change (c * x.2)⁻¹ • (c • x.1) ∈ K
        have heq : (c * x.2)⁻¹ * c = x.2⁻¹ := by
          field_simp
        simpa only [smul_smul, heq] using hnorm
    add_mem' := by
      intro x hx y hy
      change x + y = 0 ∨ 0 < (x + y).2 ∧ (x + y).2⁻¹ • (x + y).1 ∈ K
      rcases hx with rfl | ⟨hxheight, hxnorm⟩
      · simpa only [zero_add] using (show y = 0 ∨ 0 < y.2 ∧ y.2⁻¹ • y.1 ∈ K from hy)
      rcases hy with rfl | ⟨hyheight, hynorm⟩
      · simpa only [add_zero] using Or.inr ⟨hxheight, hxnorm⟩
      have hsum : 0 < x.2 + y.2 := add_pos hxheight hyheight
      refine Or.inr ⟨hsum, ?_⟩
      change (x.2 + y.2)⁻¹ • (x.1 + y.1) ∈ K
      have h := convex_iff_div.mp hK hxnorm hynorm hxheight.le hyheight.le hsum
      have hxcoef : x.2 / (x.2 + y.2) * x.2⁻¹ = (x.2 + y.2)⁻¹ := by
        field_simp
      have hycoef : y.2 / (x.2 + y.2) * y.2⁻¹ = (x.2 + y.2)⁻¹ := by
        field_simp
      simpa only [smul_smul, hxcoef, hycoef, smul_add] using h }
  Q.toPointedCone (Or.inl rfl)

theorem mem_coneOver {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (z : E × ℝ) :
    z ∈ coneOver K hK ↔ z = 0 ∨ 0 < z.2 ∧ z.2⁻¹ • z.1 ∈ K := Iff.rfl

/-- Every actual positive-height cone-hull point normalizes into the actual source convex hull. -/
theorem normalized_mem_convexHull {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
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
    · have hpos := LatticeSlices.positive_degree_of_nonzero C (hS hx) hzero
      refine Or.inr ⟨by change (0 : ℝ) < (x.2 : ℝ); exact_mod_cast hpos, ?_⟩
      exact subset_convexHull ℝ _ ⟨x, ⟨hx, hpos⟩, rfl⟩
  rcases (mem_coneOver H (convex_convexHull ℝ _) z).mp (hle hz) with hzero | hnorm
  · simp [hzero] at hheight
  · exact hnorm.2

/-- The actual generated body is the closure of the genuine positive-degree normalized hull. -/
theorem body_eq_closure_convexHull {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) :
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
    exact normalized_mem_convexHull C S hS hz.1 hz.2
  simpa only [inv_one, one_smul] using hcontinuous.continuousWithinAt.mem_closure hxT hmap

/-- Actual finite positive-source normalized hulls, without choosing an artificial enumeration. -/
def finiteInnerBody {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (t : Finset (positiveSource S)) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun z : positiveSource S => normalizedPoint z.1) ''
    (t : Set (positiveSource S)))

theorem finiteInnerBody_mono {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Monotone (finiteInnerBody S) := by
  intro t u htu
  exact convexHull_mono (image_mono htu)

theorem finiteInnerBody_directed {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    Directed (· ⊆ ·) (finiteInnerBody S) := by
  classical
  intro t u
  exact ⟨t ∪ u, finiteInnerBody_mono S Finset.subset_union_left,
    finiteInnerBody_mono S Finset.subset_union_right⟩

/-- The genuine countable directed finite hull union is the actual normalized source hull. -/
theorem convexHull_normalizedSource_eq_iUnion {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    convexHull ℝ (normalizedSource S) = ⋃ t : Finset (positiveSource S), finiteInnerBody S t := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ ((finiteInnerBody_directed S).convex_iUnion
      (fun t => convex_convexHull ℝ _))
    rintro y ⟨z, hz, rfl⟩
    refine mem_iUnion.mpr ⟨{⟨z, hz⟩}, subset_convexHull ℝ _ ?_⟩
    exact ⟨⟨z, hz⟩, Finset.mem_singleton_self _, rfl⟩
  · apply iUnion_subset
    intro t
    apply convexHull_mono
    rintro y ⟨z, _, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

/-- Every finite source hull is an actual previously checked finite inner body. -/
theorem finiteInnerBody_eq_innerBody {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (t : Finset (positiveSource S)) :
    ∃ (m : ℕ) (v : Fin m → (Fin n → ℤ) × ℤ),
      (∀ i, v i ∈ S) ∧ (∀ i, 0 < (v i).2) ∧ finiteInnerBody S t = innerBody v := by
  classical
  let e := (Fintype.equivFin t).symm
  let v := fun i => (e i).1.1
  refine ⟨Fintype.card t, v, fun i => (e i).1.2.1, fun i => (e i).1.2.2, ?_⟩
  apply congrArg (convexHull ℝ)
  ext y
  constructor
  · rintro ⟨z, hzt, rfl⟩
    obtain ⟨i, hi⟩ := e.surjective ⟨z, hzt⟩
    exact ⟨i, by simp [v, hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(e i).1, (e i).2, rfl⟩

/-- The true body measure is exhausted by actual finite positive-source inner-body measures. -/
theorem volume_body_eq_iSup_inner {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) :
    volume (body S) = ⨆ t : Finset (positiveSource S), volume (finiteInnerBody S t) := by
  rw [body_eq_closure_convexHull C S hS,
    measure_closure_of_null_frontier ((convex_convexHull ℝ (normalizedSource S)).addHaar_frontier volume),
    convexHull_normalizedSource_eq_iUnion S]
  exact (finiteInnerBody_directed S).measure_iUnion

/-- Strict real volume approximation is derived from true finite-measure exhaustion. -/
theorem exists_inner_volume_gt {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (hrbody : r < volume.real (body S)) :
    ∃ (m : ℕ) (v : Fin m → (Fin n → ℤ) × ℤ),
      (∀ i, v i ∈ S) ∧ (∀ i, 0 < (v i).2) ∧ r < volume.real (innerBody v) := by
  have hfinite : volume (body S) ≠ ⊤ := (isCompact_body C S hS hne).measure_lt_top.ne
  have hlt : ENNReal.ofReal r < ⨆ t : Finset (positiveSource S), volume (finiteInnerBody S t) := by
    rw [← volume_body_eq_iSup_inner C S hS]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr hfinite).mpr hrbody
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hlt
  obtain ⟨m, v, hv, hdeg, heq⟩ := finiteInnerBody_eq_innerBody S t
  refine ⟨m, v, hv, hdeg, ?_⟩
  rw [heq] at ht
  exact (ENNReal.ofReal_lt_iff_lt_toReal hr (isCompact_innerBody v).measure_lt_top.ne).mp ht

/-- True finite-inner exhaustion and produced conductors squeeze the actual period counts. -/
theorem tendsto_source_period_of_full_rank {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty)
    [IsZLattice ℝ (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S))]
    {β : Fin n → ℤ} {a : ℕ} (ha : 0 < a)
    (hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ)) (hβ : (β, (a : ℤ)) ∈ LatticeSlices.generatedGroup S) :
    Tendsto (fun k : ℕ => (sourceSubset C S hS).normalizedCardinality (k * a)) atTop
      (𝓝 (volume.real (body S) /
        ZLattice.covolume (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)))) := by
  let A := generatedAdmissibleCone C S hS hne
  let G := LatticeSlices.generatedGroup S
  let T := LatticeSlices.groupConeSubset A G
  have hSA : S ≤ latticePoints A.cone := fun _ hz => mem_closedCone_of_mem S hz
  have heqS (k : ℕ) : (sourceSubset C S hS).normalizedCardinality k =
      (sourceSubset A S hSA).normalizedCardinality k := by
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality,
      card_sourceSubset_slices, card_sourceSubset_slices]
  have hST (k : ℕ) : (sourceSubset C S hS).normalizedCardinality k ≤
      T.normalizedCardinality k := by
    rw [heqS]
    apply ConeSubset.normalizedCardinality_mono
    intro z hz
    exact ⟨hSA hz, AddSubgroup.subset_closure hz⟩
  have hupper := LatticeSlices.tendsto_groupConeSubset A G hβ ha
  have hcovol : 0 < ZLattice.covolume (LatticeSlices.horizontalLattice G) :=
    ZLattice.covolume_pos (LatticeSlices.horizontalLattice G)
  apply tendsto_order.mpr
  constructor
  · intro r hr
    by_cases hrneg : r < 0
    · exact Eventually.of_forall (fun k => hrneg.trans_le
        (ConeSubset.normalizedCardinality_nonneg _ _))
    have hrnonneg : 0 ≤ r := le_of_not_gt hrneg
    have hrbody : r * ZLattice.covolume (LatticeSlices.horizontalLattice G) <
        volume.real (body S) := (lt_div_iff₀ hcovol).mp hr
    obtain ⟨m, v, hv, hdeg, hvvol⟩ := exists_inner_volume_gt C S hS hne
      (mul_nonneg hrnonneg hcovol.le) hrbody
    have hrlower : r < volume.real (innerBody v) /
        ZLattice.covolume (LatticeSlices.horizontalLattice G) :=
      (lt_div_iff₀ hcovol).mpr hvvol
    obtain ⟨b, lower, hlower, hbound⟩ :=
      exists_asymptotic_inner_lower_bound C S hS hne ha hperiod hβ v hv hdeg
    have hshift : ∀ᶠ k in atTop,
        r < (sourceSubset C S hS).normalizedCardinality ((k + b) * a) := by
      filter_upwards [(tendsto_order.mp hlower).1 r hrlower, hbound] with k hk hkb
      exact hk.trans_le hkb
    have hfinal : ∀ᶠ k in Filter.map (fun k : ℕ => k + b) atTop,
        r < (sourceSubset C S hS).normalizedCardinality (k * a) := hshift
    rwa [map_add_atTop_eq_nat] at hfinal
  · intro r hr
    filter_upwards [(tendsto_order.mp hupper).2 r hr] with k hk
    exact (hST (k * a)).trans_lt hk

/-- Off the actual generated period, the source slice and its normalized count are genuinely empty. -/
theorem source_normalizedCardinality_eq_zero_of_not_dvd {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    {a : ℕ} (hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples (a : ℤ)) {k : ℕ} (hk : ¬ a ∣ k) :
    (sourceSubset C S hS).normalizedCardinality k = 0 := by
  have hempty : slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hk (Int.natCast_dvd_natCast.mp (LatticeSlices.degree_dvd_of_mem S hperiod hx))
  rw [ConeSubset.normalizedCardinality, card_sourceSubset_slices, hempty]
  simp

private theorem limsup_eq_of_supported_period (q : ℕ → ℝ)
    (hq : ∀ k, 0 ≤ q k) (hbounded : IsBoundedUnder (· ≤ ·) atTop q)
    {a : ℕ} (ha : 0 < a) (hoff : ∀ k, ¬ a ∣ k → q k = 0)
    {L : ℝ} (hperiod : Tendsto (fun k => q (k * a)) atTop (𝓝 L)) :
    limsup q atTop = L := by
  have hmul : Tendsto (fun k : ℕ => k * a) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k ha) tendsto_id
  have hdiv : Tendsto (fun k : ℕ => k / a) atTop atTop :=
    le_of_eq (map_div_atTop_eq_nat a ha)
  have hrounded := hperiod.comp hdiv
  have hcompare : ∀ᶠ k in atTop, q k ≤ q (k / a * a) := by
    apply Eventually.of_forall
    intro k
    by_cases hk : a ∣ k
    · rw [Nat.div_mul_cancel hk]
    · rw [hoff k hk]
      exact hq _
  apply le_antisymm
  · rw [← hrounded.limsup_eq]
    exact limsup_le_limsup hcompare (isCoboundedUnder_le_of_le atTop hq)
      hrounded.isBoundedUnder_le
  · rw [← hperiod.limsup_eq]
    exact hmul.limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le (Filter.map (fun k : ℕ => k * a) atTop) hq) hbounded

/-- The source's arbitrary-semigroup divisible-degree limit exists and equals its actual limsup volume. -/
theorem exists_divisible_degree_limit {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone) :
    ∃ a : ℕ, 0 < a ∧ ∀ d : ℕ, 0 < d → a ∣ d →
      Tendsto (fun k : ℕ => (sourceSubset C S hS).normalizedCardinality (k * d))
        atTop (𝓝 (ConeSubset.volume (sourceSubset C S hS))) := by
  classical
  let Q := sourceSubset C S hS
  have hzero_case (hzero : Tendsto Q.normalizedCardinality atTop (𝓝 0)) :
      ∃ a : ℕ, 0 < a ∧ ∀ d : ℕ, 0 < d → a ∣ d →
        Tendsto (fun k : ℕ => Q.normalizedCardinality (k * d))
          atTop (𝓝 (ConeSubset.volume Q)) := by
    have hvolume : ConeSubset.volume Q = 0 := hzero.limsup_eq
    refine ⟨1, zero_lt_one, fun d hd _ => ?_⟩
    rw [hvolume]
    exact hzero.comp (tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k hd) tendsto_id)
  by_cases hnonzero : ∃ z ∈ S, z ≠ 0
  · by_cases hproper : Submodule.span ℝ
        (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S) : Set (Fin n → ℝ)) ≠ ⊤
    · exact hzero_case (tendsto_source_normalizedCardinality_of_lower_rank C S hS hproper)
    · let : IsZLattice ℝ (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)) :=
        ⟨not_ne_iff.mp hproper⟩
      obtain ⟨a, ha, hperiod, β, hβ⟩ := LatticeSlices.exists_semigroup_degree_period C S hS hnonzero
      obtain ⟨z, hz, _⟩ := hnonzero
      have hlimit := tendsto_source_period_of_full_rank C S hS ⟨z, hz⟩ ha hperiod hβ
      have hvolume : ConeSubset.volume Q = volume.real (body S) /
          ZLattice.covolume (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)) :=
        limsup_eq_of_supported_period Q.normalizedCardinality
          (ConeSubset.normalizedCardinality_nonneg Q) Q.bounded_normalizedCardinality ha
          (fun k hk => source_normalizedCardinality_eq_zero_of_not_dvd C S hS hperiod hk) hlimit
      refine ⟨a, ha, fun d hd had => ?_⟩
      obtain ⟨b, rfl⟩ := had
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd
      rw [hvolume]
      have h := hlimit.comp (tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k hb) tendsto_id)
      simpa only [Function.comp_def, Nat.mul_assoc, Nat.mul_comm a b] using h
  · exact hzero_case (tendsto_source_normalizedCardinality_of_no_nonzero C S hS
      (by simpa only [not_exists, not_and, not_not] using hnonzero))

/-- Full group generation forces actual nonempty source. -/
theorem nonempty_of_generatedGroup_eq_top {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    (S : Set ((Fin n → ℤ) × ℤ)).Nonempty := by
  classical
  by_contra hnone
  have hempty : (S : Set ((Fin n → ℤ) × ℤ)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
  have hGbot : LatticeSlices.generatedGroup S = ⊥ := by
    rw [LatticeSlices.generatedGroup, hempty, AddSubgroup.closure_empty]
  have hmem : ((0 : Fin n → ℤ), (1 : ℤ)) ∈
      (⊥ : AddSubgroup ((Fin n → ℤ) × ℤ)) := by
    rw [← hGbot, hG]
    trivial
  have h := congrArg Prod.snd (AddSubgroup.mem_bot.mp hmem)
  norm_num at h

/-- Full actual group generation gives the source's ordinary body-volume counting limit. -/
theorem tendsto_source_of_generatedGroup_eq_top {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    Tendsto (sourceSubset C S hS).normalizedCardinality atTop (𝓝 (volume.real (body S))) := by
  classical
  have hne := nonempty_of_generatedGroup_eq_top S hG
  let A := generatedAdmissibleCone C S hS hne
  have hβ : ((0 : Fin n → ℤ), (1 : ℤ)) ∈ LatticeSlices.generatedGroup S := by
    rw [hG]
    trivial
  have hperiod : LatticeSlices.degreeGroup (LatticeSlices.generatedGroup S) =
      AddSubgroup.zmultiples ((1 : ℕ) : ℤ) := by
    rw [hG]
    ext k
    constructor
    · intro _
      exact Int.mem_zmultiples_iff.mpr (one_dvd k)
    · intro _
      exact (LatticeSlices.mem_degreeGroup_iff ⊤ k).mpr ⟨0, by trivial⟩
  let : IsZLattice ℝ (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)) :=
    ⟨by rw [hG]; exact IsZLattice.span_top⟩
  have hsource := tendsto_source_period_of_full_rank C S hS hne zero_lt_one hperiod hβ
  have hsat := LatticeSlices.tendsto_groupConeSubset A (LatticeSlices.generatedGroup S) hβ zero_lt_one
  have heq : LatticeSlices.groupConeSubset A (LatticeSlices.generatedGroup S) =
      Counting.coneSubset A := by
    apply Subtype.ext
    ext z
    simp [LatticeSlices.groupConeSubset, Counting.coneSubset, hG]
  rw [heq] at hsat
  have hsat' : Tendsto (Counting.coneSubset A).normalizedCardinality atTop
      (𝓝 (volume.real (body S) /
        ZLattice.covolume (LatticeSlices.horizontalLattice (LatticeSlices.generatedGroup S)))) := by
    simpa only [Nat.mul_one, A, generatedAdmissibleCone, body] using hsat
  have hvalue := tendsto_nhds_unique hsat' (Counting.tendsto_cone_lattice_slices A)
  rw [hvalue] at hsource
  simpa only [Nat.mul_one, A, generatedAdmissibleCone, body] using hsource

end SGPT.AlmostSemigroup.Okounkov
