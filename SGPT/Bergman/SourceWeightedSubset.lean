import SGPT.PSH.Pluripolar
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.WeightedSubset

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe u

/-- WHOLE original def:weightedss: the SAME closed nonPP subset with its
actual REAL continuous weight. No compact-subtype or boundedness field. -/
structure WeightedSubset (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  carrier : Set M
  isClosed_carrier : IsClosed carrier
  nonPluripolar_carrier : (ofFixedModel n M).NonPluripolar carrier
  weight : C(carrier, ℝ)

namespace WeightedSubset

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The SAME original subtype weight, with only the literal scalar inclusion.
No values outside K or partial/envelope operators are introduced. -/
def erealWeight (W : WeightedSubset n M) : W.carrier → EReal :=
  fun x => (W.weight x : EReal)

/-- Original closedness plus actual ambient compactness INTERNALLY supplies
CompactSpace K and a finite real absolute bound for the genuine weight. -/
theorem exists_real_abs_bound [CompactSpace M] (W : WeightedSubset n M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : W.carrier, |W.weight x| ≤ R := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  refine ⟨‖W.weight‖, norm_nonneg _, ?_⟩
  intro x
  simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm W.weight x

/-- Actual finite REAL lower/upper witnesses for the SAME original partial
obstacle, manufactured from continuous weighted-subset data, not assumed. -/
theorem partialEnvelope_weight_bounds [CompactSpace M] (W : WeightedSubset n M) :
    ∃ a b : ℝ, (∀ x : W.carrier, (a : EReal) ≤ W.erealWeight x) ∧
      ∀ x : W.carrier, W.erealWeight x ≤ (b : EReal) := by
  obtain ⟨R, _hR0, hR⟩ := W.exists_real_abs_bound
  exact ⟨-R, R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).1,
    fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩

end WeightedSubset
end SGPT.Bergman.WeightedSubset
