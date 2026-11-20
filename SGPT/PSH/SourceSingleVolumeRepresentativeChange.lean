import SGPT.PSH.SourcePositiveMixedIVolume

/-! Exact source prop:voldeponlyoncurr, including the manufactured compensated
PSH domain. This is a source readback of the checked independent-slot producer;
no new analytic producer or whole-book completion is claimed. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The literal smooth gauge manufactures phi-g as an original eta-PSH
potential and preserves the original single I-volume, including n=0. -/
theorem sourceIVolume_smooth_representative_invariance (ω : KahlerBackground n M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g) {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    ∃ hφ' : (ofFixedModel n M).IsThetaPSH η (fun x => φ x - (g x : EReal)),
      sourceIVolume θ φ hφ = sourceIVolume η (fun x => φ x - (g x : EReal)) hφ' := by
  refine ⟨sourceThetaPSH_sub_smooth hchange hφ, ?_⟩
  have h := sourceEnvelopeMixedIVolume_changeRepresentative ω
    (fun _ : Fin n => θ) (fun _ => η) (fun _ => φ) (fun _ => g)
    (fun _ => hchange) (fun _ => hφ)
  simpa only [sourceEnvelopeMixedIVolume_diagonal] using h.symm

end SGPT.PSH.VariableComplexAtlas
