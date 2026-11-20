import SGPT.Okounkov.SchemeProjectiveSectionRawBody

/-!
# Actual common-degree section polytopes

Positive repetitions in the SAME original section semigroup retain the whole
normalized point. Common positive multiples therefore give a directed family
of genuine degree polytopes. No uniform bound or lattice-generation hypothesis
is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open scoped Topology

private theorem positive_nsmul_mem {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) {z : (Fin n → ℤ) × ℤ}
    (hz : z ∈ S) (r : ℕ) (hr : 0 < r) : r • z ∈ S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [succ_nsmul, add_comm]
  exact Conductor.add_nsmul_mem S hz hz k

private theorem normalizedSlice_subset_positive_multiple {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (m r : ℕ) (hr : 0 < r) :
    BodyGeometry.normalizedSlice S m ⊆ BodyGeometry.normalizedSlice S (r * m) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨r • u, ?_, ?_⟩
  · have hmem := positive_nsmul_mem S hu r hr
    simpa [nsmul_eq_mul] using hmem
  · have hrr : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    ext i
    simp [Counting.integerCast, nsmul_eq_mul, mul_inv_rev, smul_eq_mul,
      hrr, mul_comm, mul_left_comm]

private theorem positive_source_normalizedPoint_mem_slice {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (z : positiveSource S) :
    normalizedPoint z.val ∈ BodyGeometry.normalizedSlice S z.val.2.toNat := by
  have hdeg : (z.val.2.toNat : ℤ) = z.val.2 := Int.toNat_of_nonneg z.property.2.le
  have hreal : (z.val.2.toNat : ℝ) = (z.val.2 : ℝ) := by exact_mod_cast hdeg
  refine ⟨z.val.1, ?_, ?_⟩
  · change (z.val.1, (z.val.2.toNat : ℤ)) ∈ S
    rw [hdeg]
    exact z.property.1
  · simp only [normalizedPoint, hreal]

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionExhaustionTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionExhaustionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Actual positive source repetitions retain the SAME entire normalized section point. -/
theorem schemeProjectiveSectionNormalizedPoints_subset_multiple {L : X.Modules}
    (a : LineBundleAtlas L) (m r : ℕ) (hr : 0 < r) :
    schemeProjectiveSectionNormalizedPoints f n E Y hY a m ⊆
      schemeProjectiveSectionNormalizedPoints f n E Y hY a (r * m) :=
  normalizedSlice_subset_positive_multiple _ m r hr

/-- Genuine common-degree source products give actual degree-polytope inclusions. -/
theorem schemeProjectiveSectionDegreeBody_subset_multiple {L : X.Modules}
    (a : LineBundleAtlas L) (m r : ℕ) (hr : 0 < r) :
    schemeProjectiveSectionDegreeBody f n E Y hY a m ⊆
      schemeProjectiveSectionDegreeBody f n E Y hY a (r * m) :=
  convexHull_mono (Set.image_mono
    (schemeProjectiveSectionNormalizedPoints_subset_multiple f n E Y hY a m r hr))

/-- Common positive degree multiples make the actual section-polytope family directed. -/
theorem schemeProjectiveSectionDegreeBody_directed {L : X.Modules}
    (a : LineBundleAtlas L) :
    Directed (· ⊆ ·) (fun m : {m : ℕ // 0 < m} =>
      schemeProjectiveSectionDegreeBody f n E Y hY a m.val) := by
  intro m k
  refine ⟨⟨m.val * k.val, Nat.mul_pos m.property k.property⟩, ?_, ?_⟩
  · simpa [Nat.mul_comm] using
      schemeProjectiveSectionDegreeBody_subset_multiple f n E Y hY a m.val k.val k.property
  · exact schemeProjectiveSectionDegreeBody_subset_multiple f n E Y hY a k.val m.val m.property

/-- Actual common degrees absorb the native finite inner hulls, giving the whole hull union. -/
theorem schemeProjectiveSectionNormalizedHull_eq_iUnion {L : X.Modules}
    (a : LineBundleAtlas L) :
    convexHull ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        normalizedSource (schemeProjectiveSectionSemigroup f n E Y hY a)) =
      ⋃ m : {m : ℕ // 0 < m}, schemeProjectiveSectionDegreeBody f n E Y hY a m.val := by
  let S := schemeProjectiveSectionSemigroup f n E Y hY a
  let J := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let U := ⋃ m : {m : ℕ // 0 < m}, schemeProjectiveSectionDegreeBody f n E Y hY a m.val
  have hconv : Convex ℝ U := (schemeProjectiveSectionDegreeBody_directed f n E Y hY a).convex_iUnion
    (fun m => schemeProjectiveSectionDegreeBody_convex f n E Y hY a m.val)
  have hnorm (z : positiveSource S) : J (normalizedPoint z.val) ∈ U := by
    have hm : 0 < z.val.2.toNat := by
      have hp : 0 < z.val.2 := z.property.2
      omega
    apply mem_iUnion.mpr
    refine ⟨⟨z.val.2.toNat, hm⟩, subset_convexHull ℝ _ ?_⟩
    exact ⟨normalizedPoint z.val, positive_source_normalizedPoint_mem_slice S z, rfl⟩
  have hfinite (t : Finset (positiveSource S)) : finiteInnerBody S t ⊆ J ⁻¹' U := by
    apply convexHull_min ?_ (hconv.linear_preimage J.toLinearMap)
    rintro _ ⟨z, _, rfl⟩
    exact hnorm z
  have hleft : J '' convexHull ℝ (normalizedSource S) ⊆ U := by
    rw [convexHull_normalizedSource_eq_iUnion S]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    exact hfinite t ht
  apply Set.Subset.antisymm
  · calc
      _ = J '' convexHull ℝ (normalizedSource S) := (J.toLinearMap.image_convexHull _).symm
      _ ⊆ U := hleft
  · apply iUnion_subset
    intro m
    apply convexHull_mono
    apply Set.image_mono
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(u, (m.val : ℤ)), ⟨hu, by change (0 : ℤ) < (m.val : ℤ); exact_mod_cast m.property⟩, ?_⟩
    simp only [normalizedPoint, Int.cast_natCast]

/-- The actual raw generated section body is exhausted by genuine positive-degree polytopes. -/
theorem schemeProjectiveSectionRawBody_eq_closure_iUnion {L : X.Modules}
    (a : LineBundleAtlas L) :
    schemeProjectiveSectionRawBody f n E Y hY a =
      closure (⋃ m : {m : ℕ // 0 < m}, schemeProjectiveSectionDegreeBody f n E Y hY a m.val) := by
  rw [schemeProjectiveSectionRawBody_eq_closure_convexHull f n E Y hY a,
    schemeProjectiveSectionNormalizedHull_eq_iUnion f n E Y hY a]

end SGPT.Okounkov
