import SGPT.Projective.OkounkovFiniteCore
import SGPT.Projective.OkounkovFiniteNormCone
import SGPT.Projective.OkounkovPositiveBodyExhaustion

/-! SAME original body finite volume from actual source slice growth.
Blueprint: okounkov-body-polynomial-growth.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set Filter MeasureTheory SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov
open scoped Topology

/-- Count SAME actual finite generated subsemigroups; bound each original finite normalized hull. -/
theorem finiteInnerBody_volume_le_of_polynomial_growth {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    (hfinite : ∀ k : ℕ, (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite)
    (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ B * (k : ℝ)^n)
    (t : Finset (positiveSource S)) : volume (finiteInnerBody S t) ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨R₀,hR₀,hG₀⟩ := exists_positive_finite_fullGroup_core S hpositive hG
  let R := R₀ ∪ t.image Subtype.val
  let T := AddSubsemigroup.closure (R : Set ((Fin n → ℤ) × ℤ))
  have hR : (R : Set ((Fin n → ℤ) × ℤ)) ⊆ positiveSource S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hR₀ hz
    · rcases Finset.mem_image.mp hz with ⟨w,_,rfl⟩
      exact w.property
  have hTS : T ≤ S := AddSubsemigroup.closure_le.mpr (fun _ hz => (hR hz).1)
  have hGT : LatticeSlices.generatedGroup T = ⊤ := by
    rw [generatedGroup_addSubsemigroup_closure]
    apply top_le_iff.mp
    rw [←hG₀]
    exact AddSubgroup.closure_mono (by intro z hz; exact Finset.mem_union_left _ hz)
  let C := originalNormCone n (finiteSourceNormBound R)
  have hTC : T ≤ latticePoints C.cone := finiteGenerated_le_normCone R (fun z hz => (hR hz).2)
  have hlimit := tendsto_source_of_generatedGroup_eq_top C T hTC hGT
  have hbound : ∀ᶠ k : ℕ in atTop, (sourceSubset C T hTC).normalizedCardinality k ≤ B := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hfin := hfinite k
    let := hfin.to_subtype
    have hslice : slice (T : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) ⊆
        slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) := fun _ hz => hTS hz
    have hcard := Nat.card_le_card_of_injective (Set.inclusion hslice)
      (Set.inclusion_injective hslice)
    have hcardR : (Nat.card (slice (T : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤
        B*(k:ℝ)^n := by
      have hcast : (Nat.card (slice (T : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤
          (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) := by exact_mod_cast hcard
      exact hcast.trans (hcount k hk)
    have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
    rw [ConeSubset.normalizedCardinality,card_sourceSubset_slices]
    calc (k:ℝ)⁻¹^n * (Nat.card (slice (T : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ)
        ≤ (k:ℝ)⁻¹^n * (B*(k:ℝ)^n) :=
          mul_le_mul_of_nonneg_left hcardR (pow_nonneg (inv_nonneg.mpr hkR.le) n)
      _ = B := by rw [inv_pow]; field_simp
  have hreal : volume.real (body T) ≤ B := le_of_tendsto hlimit hbound
  have hvolfin : volume (body T) ≠ ⊤ :=
    (isCompact_body C T hTC (nonempty_of_generatedGroup_eq_top T hGT)).measure_lt_top.ne
  have hvol : volume (body T) ≤ ENNReal.ofReal B :=
    (ENNReal.toReal_le_toReal hvolfin ENNReal.ofReal_ne_top).mp (by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hB] using hreal)
  have hinner : finiteInnerBody S t ⊆ body T := by
    apply convexHull_min ?_ (convex_body T)
    rintro _ ⟨z,hz,rfl⟩
    have hzR : z.val ∈ R :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    exact normalizedPoint_mem_heightOne _
      (mem_closedCone_of_mem T (AddSubsemigroup.subset_closure hzR)) z.property.2
  exact (measure_mono hinner).trans hvol

/-- The genuine directed finite-hull exhaustion bounds the SAME original body's volume. -/
theorem volume_body_le_of_polynomial_growth {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    (hfinite : ∀ k : ℕ, (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite)
    (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ B*(k:ℝ)^n) :
    volume (body S) ≤ ENNReal.ofReal B := by
  rw [volume_body_eq_iSup_inner_of_positiveHeight S hpositive]
  exact iSup_le (fun t => finiteInnerBody_volume_le_of_polynomial_growth S hpositive hG hfinite B hB hcount t)

/-- Actual original polynomial counts manufacture finite SAME-body volume without a source cone. -/
theorem volume_body_ne_top_of_polynomial_growth {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    (hfinite : ∀ k : ℕ, (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite)
    (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ B*(k:ℝ)^n) :
    volume (body S) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (volume_body_le_of_polynomial_growth S hpositive hG hfinite B hB hcount)

end SGPT.Okounkov.BodyFromGrowth
