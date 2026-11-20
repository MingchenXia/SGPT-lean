import SGPT.Bergman.SourceEnvelopeContactSets
import SGPT.PSH.MultiplierIdealInfSkoda

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual original reference-envelope invariance under the INTERNALLY
used compact normalization phi-A and positive scaling. All extended poles
and both entire admissible sets are retained; no envelope equality or
singularity-equivalence certificate is supplied. -/
theorem sourcePartialEnvelope_scaled_sub_const
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (K : Set X) (v : K → EReal) (A a : ℝ) (ha : 0 < a) :
    partialEnvelope theta (fun x => (a : EReal) * (phi x - (A : EReal))) K v =
      partialEnvelope theta (fun x => (a : EReal) * phi x) K v := by
  have hformula (x : X) : (a : EReal) * (phi x - (A : EReal)) =
      (a : EReal) * phi x + ((-(a * A) : ℝ) : EReal) := by
    rw [sub_eq_add_neg, ← EReal.coe_neg,
      SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe ha, mul_neg]
  apply le_antisymm
  · apply partialEnvelope_mono_singularity
    exact ⟨-(a * A), fun x _ => (hformula x).le⟩
  · apply partialEnvelope_mono_singularity
    refine ⟨a * A, fun x _ => ?_⟩
    change (a : EReal) * phi x ≤
      (a : EReal) * (phi x - (A : EReal)) + ((a * A : ℝ) : EReal)
    rw [hformula x, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- The unscaled original reference is unchanged by the same real
normalization, including empty candidate sets and infinite envelopes. -/
theorem sourcePartialEnvelope_sub_const
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (K : Set X) (v : K → EReal) (A : ℝ) :
    partialEnvelope theta (fun x => phi x - (A : EReal)) K v =
      partialEnvelope theta phi K v := by
  simpa only [EReal.coe_one, one_mul] using
    sourcePartialEnvelope_scaled_sub_const theta phi K v A 1 zero_lt_one

end SGPT.Bergman.ReferenceEnvelopeConvergence
