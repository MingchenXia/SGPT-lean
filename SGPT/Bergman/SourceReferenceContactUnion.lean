import SGPT.Bergman.SourceCurrentReferenceEnvelopes
import SGPT.Bergman.SourceGeneralBergmanTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.Bergman.GeneralBMTransport
open scoped Topology ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Literal original reference-limit contact union927-934. The infimum
identity is PRODUCED from the actual current/d_S/whole-envelope chain,
not supplied as a reader. Original phi, physical background, all poles
and the exact original full-X envelope/obstacle are unchanged. -/
theorem sourceEnvelopeGap_zero_eq_iUnion_scaled
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi) (v : C(X, ℝ))
    (alpha : ℕ → ℝ) (hmono : Monotone alpha) (hpos : ∀ k, 0 < alpha k)
    (hlt : ∀ k, alpha k < 1) (hlim : Tendsto alpha atTop (𝓝 1)) :
    sourceEnvelopeGap (nativeClosedFormToAtlas theta) phi v 0 =
      ⋃ k : ℕ, sourceEnvelopeGap (nativeClosedFormToAtlas theta)
        (fun x => ((alpha k : ℝ) : EReal) * phi x) v 0 := by
  have heq := partialEnvelope_eq_iInf_scaled_references_of_current omega theta hcurrent
    (wholeWeightedSubset (n := n) v) alpha hmono hpos hlt hlim
  change partialEnvelope (nativeClosedFormToAtlas theta) phi univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal)) =
    ⨅ k : ℕ, partialEnvelope (nativeClosedFormToAtlas theta)
      (fun y => ((alpha k : ℝ) : EReal) * phi y) univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal)) at heq
  ext x
  have hp : partialEnvelope (nativeClosedFormToAtlas theta) phi univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal)) x =
      ⨅ k : ℕ, partialEnvelope (nativeClosedFormToAtlas theta)
        (fun y => ((alpha k : ℝ) : EReal) * phi y) univ
        (fun y : ↥(univ : Set X) => (v y.val : EReal)) x := by
    simpa only [iInf_apply] using congrFun heq x
  simp only [mem_iUnion, sourceEnvelopeGap, mem_ofPred_eq, sub_zero]
  rw [hp]
  exact iInf_lt_iff

end SGPT.Bergman.ReferenceEnvelopeConvergence
