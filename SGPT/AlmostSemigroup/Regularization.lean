import SGPT.AlmostSemigroup.Okounkov

/-!
# Actual generated-cone regularization

The source regularization is the actual lattice-point semigroup of its
closed generated cone. Actual inclusion and the checked all-degree counting
limits make its normalized symmetric-difference discrepancy converge to zero.
This proves SGPT `lma:regularizatapp` using the exact source pseudometric.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Regularization

open Filter MeasureTheory
open scoped Topology
open Okounkov

/-- SGPT's actual `Reg(S) = C(S) ∩ ℤ^(n+1)`, retaining its additive structure. -/
def regularizedSemigroup {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) :=
  latticePoints (closedCone S : ConvexCone ℝ ((Fin n → ℝ) × ℝ))

@[simp] theorem mem_regularizedSemigroup {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (z : (Fin n → ℤ) × ℤ) :
    z ∈ regularizedSemigroup S ↔ latticeCast n z ∈ closedCone S := Iff.rfl

/-- Every actual source lattice point belongs to its regularization. -/
theorem le_regularizedSemigroup {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) :
    S ≤ regularizedSemigroup S := fun _ hz => mem_closedCone_of_mem S hz

/-- Actual regularization stays in the original admissible cone. -/
theorem regularizedSemigroup_le_source {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    regularizedSemigroup S ≤ latticePoints C.cone :=
  latticePoints_mono (closedCone_subset_source C S hS hne)

/-- Full generated-group equality is preserved by actual regularization. -/
theorem generatedGroup_regularizedSemigroup_eq_top {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    LatticeSlices.generatedGroup (regularizedSemigroup S) = ⊤ := by
  apply top_le_iff.mp
  rw [← hG]
  exact AddSubgroup.closure_mono (le_regularizedSemigroup S)

/-- The actual regularization as a subset of the original source cone. -/
def regularizedSubset {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) : ConeSubset C :=
  sourceSubset C (regularizedSemigroup S) (regularizedSemigroup_le_source C S hS hne)

/-- Its actual normalized slice counts converge to the original generated body volume. -/
theorem tendsto_regularized_normalizedCardinality {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hne : (S : Set ((Fin n → ℤ) × ℤ)).Nonempty) :
    Tendsto (regularizedSubset C S hS hne).normalizedCardinality atTop
      (𝓝 (volume.real (body S))) := by
  let A := generatedAdmissibleCone C S hS hne
  have heq : (regularizedSubset C S hS hne).normalizedCardinality =
      (Counting.coneSubset A).normalizedCardinality := by
    funext k
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    congr 1
  rw [heq]
  exact Counting.tendsto_cone_lattice_slices A

/-- Actual subset inclusion turns normalized symmetric difference into the cardinality deficit. -/
theorem normalizedDiscrepancy_eq_sub_of_subset {n : ℕ} {C : AdmissibleCone n}
    (S T : ConeSubset C) (hST : S.val ⊆ T.val) (k : ℕ) :
    normalizedDiscrepancy n S.slices T.slices k =
      T.normalizedCardinality k - S.normalizedCardinality k := by
  classical
  have h := discrepancy_formula (S.slices k) (T.slices k)
  rw [Finset.inter_eq_left.mpr (ConeSubset.slices_subset_of_subset S T hST k)] at h
  have hr : (discrepancy (S.slices k) (T.slices k) : ℝ) +
      2 * (S.slices k).card = (S.slices k).card + (T.slices k).card := by
    exact_mod_cast h
  have hd : (discrepancy (S.slices k) (T.slices k) : ℝ) =
      (T.slices k).card - (S.slices k).card := by linarith
  simp only [normalizedDiscrepancy, ConeSubset.normalizedCardinality, hd, mul_sub]

/-- The genuine source discrepancy sequence tends to zero under the source's full-generation premise. -/
theorem tendsto_regularization_discrepancy {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    Tendsto (normalizedDiscrepancy n (sourceSubset C S hS).slices
      (regularizedSubset C S hS (nonempty_of_generatedGroup_eq_top S hG)).slices)
      atTop (𝓝 0) := by
  have hreg := tendsto_regularized_normalizedCardinality C S hS
    (nonempty_of_generatedGroup_eq_top S hG)
  have hsource := tendsto_source_of_generatedGroup_eq_top C S hS hG
  have h := hreg.sub hsource
  simp only [sub_self] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun k =>
    (normalizedDiscrepancy_eq_sub_of_subset _ _ (le_regularizedSemigroup S) k).symm

/-- SGPT `lma:regularizatapp`: the actual source pseudometric identifies `S` and `Reg(S)`. -/
theorem distance_regularization_eq_zero {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    dist (sourceSubset C S hS)
      (regularizedSubset C S hS (nonempty_of_generatedGroup_eq_top S hG)) = 0 :=
  (tendsto_regularization_discrepancy C S hS hG).limsup_eq

end SGPT.AlmostSemigroup.Regularization
