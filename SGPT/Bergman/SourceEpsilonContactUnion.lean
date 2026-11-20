import SGPT.Bergman.SourceAnalyticPartialEnvelopeBackgroundLimit
import SGPT.Bergman.SourceEnvelopeContactSets
import SGPT.Bergman.SourceGeneralBergmanTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Bergman.BackgroundEnvelopeLimit

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.ContactConcentration
open SGPT.Bergman.GeneralBMTransport
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- An actual positive countable cofinal approach to the original zero background. -/
def sourceEpsilonSequence (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem sourceEpsilonSequence_pos (j : ℕ) : 0 < sourceEpsilonSequence j := by
  dsimp only [sourceEpsilonSequence]
  positivity

theorem sourceEpsilonSequence_antitone : Antitone sourceEpsilonSequence := by
  intro a b hab
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hab 1

theorem sourceEpsilonSequence_tendsto : Tendsto sourceEpsilonSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The literal source888-893 contact-open union follows from the newly
produced actual background infimum, with the original phi unchanged. -/
theorem sourceEnvelopeGap_zero_eq_iUnion_epsilon
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi)
    (han : (ofFixedModel n X).HasRationalAnalyticType phi) (v : C(X, ℝ)) :
    sourceEnvelopeGap (nativeClosedFormToAtlas theta) phi v 0 =
      ⋃ j : ℕ, sourceEnvelopeGap
        (nativeClosedFormToAtlas (theta + sourceEpsilonSequence j • omega.form)) phi v 0 := by
  have heq := (analytic_partialEnvelope_background_decreasing omega theta hcurrent han
    (wholeWeightedSubset (n := n) v) (fun j => (sourceEpsilonSequence_pos j).le)
    sourceEpsilonSequence_antitone sourceEpsilonSequence_tendsto).2.1
  ext x
  have hp : (⨅ j : ℕ, partialEnvelope
      (nativeClosedFormToAtlas (theta + sourceEpsilonSequence j • omega.form)) phi univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal)) x) =
      partialEnvelope (nativeClosedFormToAtlas theta) phi univ
        (fun y : ↥(univ : Set X) => (v y.val : EReal)) x := congrFun heq x
  simp only [mem_iUnion, sourceEnvelopeGap, mem_ofPred_eq, sub_zero]
  rw [← hp]
  exact iInf_lt_iff

end SGPT.Bergman.BackgroundEnvelopeLimit
