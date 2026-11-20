import SGPT.NAPotential.HullFiniteConcaveMajorant
import SGPT.NAPotential.PointwiseEnvelope
import SGPT.NAPotential.FiniteNodeSimplex

/-! Direct original-D consumer of finite real-height Jensen and the original
constant tail. Every actual raw LCE, nodal value, index and feasible weight is retained. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- At an original point off all nodal poles, the literal original weighted
EReal expression is its actual real-height sum. No no-top hypothesis is supplied. -/
theorem weightedValue_eq_real_of_nodes_ne_bot (D : PiecewiseLinearData θ)
    (x : M) (hfinite : ∀ i, D.A i x ≠ ⊥) (w : Fin (D.N + 1) → ℝ) :
    weightedValue D w x = ((∑ i, w i * (D.A i x).toReal : ℝ) : EReal) := by
  have hnode : ∀ i, ((D.A i x).toReal : EReal) = D.A i x :=
    fun i => EReal.coe_toReal ((D.isThetaPSH i).1 x) (hfinite i)
  unfold weightedValue
  calc
    (∑ i, (w i : EReal) * D.A i x) =
        ∑ i, (w i : EReal) * ((D.A i x).toReal : EReal) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hnode i]
    _ = ∑ i, ((w i * (D.A i x).toReal : ℝ) : EReal) := by
      simp only [EReal.coe_mul]
    _ = ((∑ i, w i * (D.A i x).toReal : ℝ) : EReal) :=
      (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun i => w i * (D.A i x).toReal) Finset.univ).symm

/-- The actual feasible original nodal expression lies below the unchanged
literal raw pointwise concave envelope away from the original nodal poles.
All dimensions and node counts, including 0, are retained. -/
theorem weightedValue_le_pointwiseUpperConcaveEnvelope_of_nodes_ne_bot
    (D : PiecewiseLinearData θ) (s : ℝ) (w : Fin (D.N + 1) → ℝ)
    (hw : w ∈ feasibleWeights D s) (x : M) (hfinite : ∀ i, D.A i x ≠ ⊥) :
    weightedValue D w x ≤ D.pointwiseUpperConcaveEnvelope s x := by
  have hnode : ∀ i, ((D.A i x).toReal : EReal) = D.A i x :=
    fun i => EReal.coe_toReal ((D.isThetaPSH i).1 x) (hfinite i)
  rw [weightedValue_eq_real_of_nodes_ne_bot D x hfinite w]
  apply HullAnalytic.finite_realHeight_le_of_leftTail D.τ
    (fun i => (D.A i x).toReal) w (fun r => D.pointwiseUpperConcaveEnvelope r x)
    (D.pointwiseUpperConcaveEnvelope_concave x) ?_
    (D.τ (Fin.last D.N)) (D.A (Fin.last D.N) x).toReal ?_
    (fun i => (hw.1 i).1) hw.2.1 s hw.2.2
  · intro i
    rw [hnode i, ← D.curve_tau i]
    exact D.le_pointwiseUpperConcaveEnvelope (D.τ i) x
  · intro L hL
    rw [hnode (Fin.last D.N)]
    have h := D.le_pointwiseUpperConcaveEnvelope L x
    rw [D.curve_of_le_last hL] at h
    exact h

/-- The exact canonical simplex supremum lies below the unchanged original
raw envelope off the actual finite union of nodal poles. -/
theorem simplexValue_le_pointwiseUpperConcaveEnvelope_of_nodes_ne_bot
    (D : PiecewiseLinearData θ) (s : ℝ) (x : M) (hfinite : ∀ i, D.A i x ≠ ⊥) :
    simplexValue D s x ≤ D.pointwiseUpperConcaveEnvelope s x := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact weightedValue_le_pointwiseUpperConcaveEnvelope_of_nodes_ne_bot D s w hw x hfinite
end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
