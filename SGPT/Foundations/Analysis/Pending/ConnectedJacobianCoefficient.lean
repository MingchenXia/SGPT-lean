import SGPT.Foundations.Analysis.Pending.GlobalJacobianCoefficient
import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ConnectedJacobianCoefficient

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder ActualFlatNormalOrder
  GlobalRelativeJacobianIdeal GlobalJacobianCoefficient IdealPowerNormalOrder

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y}

/-- The actual global divisor and actual connected carrier manufacture one finite
coefficient with its ENTIRE original-stalk, flat-Jacobian and near-divisibility dictionary. -/
theorem exists_actual_relativeJacobian_coefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) :
    ∃ a : ℕ,
      (∀ y ∈ E, ∀ Φ : DivisorFlattening (m := m) E y,
        originalStalkNormalOrder Φ (actualRelativeJacobianDivisor hπ).ideal = (a : ℕ∞) ∧
          flatJacobianOrder hπ.1 Φ = (a : ℕ∞)) ∧
      (∀ y ∈ E, ∀ k : ℕ,
        DivisorExponent.IsDivNear (m + 1) (actualRelativeJacobianDivisor hπ).ideal E k y ↔ k ≤ a) := by
  let D := actualRelativeJacobianDivisor hπ
  have hDcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hDnonzero : ∀ z, DivisorExponent.IsNonzeroAt D.ideal z :=
    fun z => HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible z
  obtain ⟨a, ha⟩ := exists_originalStalkNormalOrder_on_connected_hypersurface hE D.ideal hDcoh hDnonzero
  refine ⟨a, ?_, ?_⟩
  · intro y hy Φ
    exact ⟨ha y hy Φ,
      (originalStalkNormalOrder_actualRelativeJacobianDivisor_eq_flat hπ Φ).symm.trans (ha y hy Φ)⟩
  · intro y hy k
    obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
    have hbound := natCast_le_originalStalkNormalOrder_iff_isDivNear Φ D.ideal hDcoh k
    rw [ha y hy Φ] at hbound
    exact hbound.symm.trans ENat.natCast_le_natCast

/-- The finite coefficient is unique by an actual point and genuine flattening
internally obtained from the original nonempty smooth carrier. -/
theorem existsUnique_actual_flatJacobianOrder
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) :
    ∃! a : ℕ, ∀ y ∈ E, ∀ Φ : DivisorFlattening (m := m) E y,
      flatJacobianOrder hπ.1 Φ = (a : ℕ∞) := by
  obtain ⟨a, ha, _hpower⟩ := exists_actual_relativeJacobian_coefficient hπ hE
  refine ⟨a, (fun y hy Φ => (ha y hy Φ).2), ?_⟩
  intro b hb
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  exact ENat.natCast_inj.mp ((hb y hy Φ).symm.trans (ha y hy Φ).2)

/-- The unique coefficient PRODUCED from the original modification and actual
connected hypersurface; model-change invariance is not assumed or asserted here. -/
def actualRelativeJacobianCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) : ℕ :=
  Classical.choose (existsUnique_actual_flatJacobianOrder hπ hE)

/-- Every actual original point and every same-carrier flattening reads the produced coefficient. -/
theorem flatJacobianOrder_eq_actualRelativeJacobianCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (y : Y) (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    flatJacobianOrder hπ.1 Φ = (actualRelativeJacobianCoefficient hπ hE : ℕ∞) :=
  (Classical.choose_spec (existsUnique_actual_flatJacobianOrder hπ hE)).1 y hy Φ

/-- The SAME actual effective divisor's entire original stalk, not selected generators,
has precisely this produced finite coefficient. -/
theorem originalStalkNormalOrder_eq_actualRelativeJacobianCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (y : Y) (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    originalStalkNormalOrder Φ (actualRelativeJacobianDivisor hπ).ideal =
      (actualRelativeJacobianCoefficient hπ hE : ℕ∞) :=
  (originalStalkNormalOrder_actualRelativeJacobianDivisor_eq_flat hπ Φ).trans
    (flatJacobianOrder_eq_actualRelativeJacobianCoefficient hπ hE y hy Φ)

/-- Every actual original near-divisibility power is characterized by the produced coefficient. -/
theorem isDivNear_iff_le_actualRelativeJacobianCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) (y : Y) (hy : y ∈ E) (k : ℕ) :
    DivisorExponent.IsDivNear (m + 1) (actualRelativeJacobianDivisor hπ).ideal E k y ↔
      k ≤ actualRelativeJacobianCoefficient hπ hE := by
  have hDcoh := DivisorMetric.isCoherent_of_isInvertible (actualRelativeJacobianDivisor hπ).isInvertible
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have hbound := natCast_le_originalStalkNormalOrder_iff_isDivNear Φ
    (actualRelativeJacobianDivisor hπ).ideal hDcoh k
  rw [originalStalkNormalOrder_eq_actualRelativeJacobianCoefficient hπ hE y hy Φ] at hbound
  exact hbound.symm.trans ENat.natCast_le_natCast

end SGPT.Foundations.Analysis.Pending.ConnectedJacobianCoefficient
