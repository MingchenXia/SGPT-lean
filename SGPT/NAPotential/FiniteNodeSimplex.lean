import SGPT.NAPotential.BerkovichPiecewiseLinear

/-!
Actual finite-node simplex values in the revised SGPT Remark 13.4.1
(commit 69360cfdc1f1d0c0472a4e6fce1f281176ada70b).

This module concerns the exact feasible-weight supremum and proves its cutoff,
monotonicity, and maximum-valued left tail for every number of nodes and every
complex dimension. It does not identify this supremum with spatial upper
semicontinuous regularization of the old pointwise concave envelope, nor prove
the finite-vertex or concavity assertions. The source writes a maximum;
attainment away from the left tail is not claimed here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The source's closed simplex cut by its parameter barycentre halfspace. -/
def feasibleWeights (D : PiecewiseLinearData θ) (s : ℝ) : Set (Fin (D.N + 1) → ℝ) :=
  {w | (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧ (∑ i, w i) = 1 ∧ s ≤ ∑ i, w i * D.τ i}

/-- The literal source weighted sum. Zero coefficients contribute zero even
at a polar point, since `0 * ⊥ = 0` in `EReal`. -/
def weightedValue (D : PiecewiseLinearData θ) (w : Fin (D.N + 1) → ℝ) (x : M) : EReal :=
  ∑ i, (w i : EReal) * D.A i x

/-- The actual simplex supremum. Attainment is a separate theorem. -/
def simplexValue (D : PiecewiseLinearData θ) (s : ℝ) (x : M) : EReal :=
  ⨆ w, ⨆ (_ : w ∈ feasibleWeights D s), weightedValue D w x

/-- Finite source-node maximum, written as a supremum over its finite index type. -/
def nodeMaximum (D : PiecewiseLinearData θ) (x : M) : EReal :=
  ⨆ i, D.A i x

private theorem sum_coe_mul_const {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (a : EReal) :
    (∑ i ∈ s, (w i : EReal) * a) = ((∑ i ∈ s, w i : ℝ) : EReal) * a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hw' : ∀ j ∈ s, 0 ≤ w j := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hw', EReal.coe_add]
    exact (EReal.right_distrib_of_nonneg
      (EReal.coe_nonneg.mpr (hw i (Finset.mem_insert_self i s)))
      (EReal.coe_nonneg.mpr (Finset.sum_nonneg hw'))).symm

/-- Every feasible weighted value is below the actual finite node maximum. -/
theorem weightedValue_le_nodeMaximum (D : PiecewiseLinearData θ) (s : ℝ)
    (w : Fin (D.N + 1) → ℝ) (hw : w ∈ feasibleWeights D s) (x : M) :
    weightedValue D w x ≤ nodeMaximum D x := by
  have hnonneg : ∀ i, 0 ≤ w i := fun i => (hw.1 i).1
  calc
    weightedValue D w x ≤ ∑ i, (w i : EReal) * nodeMaximum D x := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (le_iSup (fun j => D.A j x) i)
        (EReal.coe_nonneg.mpr (hnonneg i))
    _ = nodeMaximum D x := by
      rw [sum_coe_mul_const Finset.univ w (fun i _ => hnonneg i), hw.2.1]
      simp

/-- The simplex value never exceeds the actual finite node maximum. -/
theorem simplexValue_le_nodeMaximum (D : PiecewiseLinearData θ) (s : ℝ) (x : M) :
    simplexValue D s x ≤ nodeMaximum D x := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact weightedValue_le_nodeMaximum D s w hw x

/-- A genuine standard-basis weight of the source simplex. -/
def vertexWeights {N : ℕ} (i : Fin (N + 1)) : Fin (N + 1) → ℝ :=
  fun j => if j = i then 1 else 0

/-- Each admissible node gives an actual feasible source weight. -/
theorem vertexWeights_mem (D : PiecewiseLinearData θ) (i : Fin (D.N + 1))
    {s : ℝ} (hs : s ≤ D.τ i) : vertexWeights i ∈ feasibleWeights D s := by
  classical
  constructor
  · intro j
    simp only [vertexWeights]
    split_ifs <;> norm_num
  constructor
  · simp [vertexWeights]
  · simpa [vertexWeights] using hs

/-- Evaluating the weighted source expression at a vertex returns its node,
including a negative-infinite node value. -/
theorem weightedValue_vertex (D : PiecewiseLinearData θ) (i : Fin (D.N + 1)) (x : M) :
    weightedValue D (vertexWeights i) x = D.A i x := by
  classical
  unfold weightedValue
  rw [Finset.sum_eq_single i]
  · simp [vertexWeights]
  · intro j _ hji
    simp [vertexWeights, hji]
  · simp

/-- A node to the right of the parameter lies below the actual simplex value. -/
theorem node_le_simplexValue (D : PiecewiseLinearData θ) (i : Fin (D.N + 1))
    {s : ℝ} (hs : s ≤ D.τ i) (x : M) : D.A i x ≤ simplexValue D s x := by
  exact le_iSup_of_le (vertexWeights i)
    (le_iSup_of_le (vertexWeights_mem D i hs) (by rw [weightedValue_vertex]))

/-- Revised source tail formula, all node counts and all dimensions. -/
theorem simplexValue_eq_nodeMaximum_of_le_last (D : PiecewiseLinearData θ)
    {s : ℝ} (hs : s ≤ D.τ (Fin.last D.N)) (x : M) :
    simplexValue D s x = nodeMaximum D x := by
  apply le_antisymm (simplexValue_le_nodeMaximum D s x)
  apply iSup_le
  intro i
  exact node_le_simplexValue D i (hs.trans (D.tau_last_le i)) x

/-- The feasible simplex is empty beyond the original first parameter. -/
theorem not_feasibleWeights_of_lt_first (D : PiecewiseLinearData θ) {s : ℝ}
    (hs : D.τ 0 < s) (w : Fin (D.N + 1) → ℝ) : w ∉ feasibleWeights D s := by
  intro hw
  have htime : (∑ i, w i * D.τ i) ≤ D.τ 0 := by
    calc
      (∑ i, w i * D.τ i) ≤ ∑ i, w i * D.τ 0 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (D.tau_le_tau_zero i) (hw.1 i).1
      _ = D.τ 0 := by rw [← Finset.sum_mul, hw.2.1, one_mul]
  exact (not_le.mpr hs) (hw.2.2.trans htime)

/-- Revised source cutoff. No surrogate value is inserted when the simplex is empty. -/
theorem simplexValue_eq_bot_of_lt_first (D : PiecewiseLinearData θ) {s : ℝ}
    (hs : D.τ 0 < s) (x : M) : simplexValue D s x = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact ((not_feasibleWeights_of_lt_first D hs w) hw).elim

/-- Increasing the parameter shrinks its exact feasible-weight set. -/
theorem simplexValue_antitone (D : PiecewiseLinearData θ) (x : M) :
    Antitone (fun s => simplexValue D s x) := by
  intro s t hst
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact le_iSup_of_le w (le_iSup_of_le
    (show w ∈ feasibleWeights D s from ⟨hw.1, hw.2.1, hst.trans hw.2.2⟩) le_rfl)

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
