import SGPT.Bergman.SourceEnvelopeContactSets
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open scoped Topology ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The EXACT original full open contact gap is the countable union of
the actual positive gaps 1/(j+1), including every envelope pole. -/
theorem sourceEnvelopeGap_zero_eq_iUnion
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (v : C(X, ℝ)) :
    sourceEnvelopeGap theta phi v 0 =
      ⋃ j : ℕ, sourceEnvelopeGap theta phi v (1 / ((j : ℝ) + 1)) := by
  ext x
  constructor
  · intro hx
    change partialEnvelope theta phi univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x <
      ((v x - 0 : ℝ) : EReal) at hx
    rw [sub_zero] at hx
    obtain ⟨q, hq, hqv⟩ := EReal.exists_rat_btwn_of_lt hx
    have hroom : 0 < v x - (q : ℝ) := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hqv)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hroom
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change partialEnvelope theta phi univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x <
      ((v x - 1 / ((j : ℝ) + 1) : ℝ) : EReal)
    exact hq.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    change partialEnvelope theta phi univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x <
      ((v x - 1 / ((j : ℝ) + 1) : ℝ) : EReal) at hj
    change partialEnvelope theta phi univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x <
      ((v x - 0 : ℝ) : EReal)
    rw [sub_zero]
    exact hj.trans (EReal.coe_lt_coe_iff.mpr (sub_lt_self _ (by positivity)))

variable [MeasurableSpace X]

/-- Genuine countable passage from all positive source gaps to the SAME
original full open contact set. No continuity-set or boundary-null input. -/
theorem measure_sourceEnvelopeGap_zero_of_positive
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (v : C(X, ℝ)) (mu : Measure X)
    (h : ∀ delta : ℝ, 0 < delta → mu (sourceEnvelopeGap theta phi v delta) = 0) :
    mu (sourceEnvelopeGap theta phi v 0) = 0 := by
  rw [sourceEnvelopeGap_zero_eq_iUnion]
  exact measure_iUnion_null (fun j => h (1 / ((j : ℝ) + 1)) (by positivity))

end SGPT.Bergman.ContactConcentration
