import SGPT.Envelopes.SourcePerturbedModelLimits
import SGPT.Bergman.SourcePartialEnvelopeBounds

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.BackgroundEnvelopeLimit

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual source theta-PSH candidates remain admissible when the SAME
background is enlarged by a nonnegative multiple of the actual Kahler form. -/
theorem sourceThetaPSH_perturb_mono (omega : KahlerBackground n X)
    {theta : ClosedRealOneOneForm n X} {s t : ℝ} (hst : s ≤ t)
    {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (theta + s • omega.form)) u) :
    (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (theta + t • omega.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  have hun := (isThetaPSH_iff_nativeThetaPotential _ _).mp hu
  simp only [sourceNativeAtlasForm_roundTrip] at hun ⊢
  exact SGPT.Envelopes.PerturbedModelLimit.isThetaPshPotential_perturb_mono omega hst hun

/-- Inclusion of the entire original competitor family, including genuinely
empty families. The obstacle/reference/potential are unchanged. -/
theorem partialEnvelope_perturb_mono (omega : KahlerBackground n X)
    {theta : ClosedRealOneOneForm n X} {s t : ℝ} (hst : s ≤ t)
    (phi : X → EReal) (K : Set X) (f : K → EReal) :
    partialEnvelope (nativeClosedFormToAtlas (theta + s • omega.form)) phi K f ≤
      partialEnvelope (nativeClosedFormToAtlas (theta + t • omega.form)) phi K f := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro v
  exact le_iSup
    (fun w : partialCompetitors
      (nativeClosedFormToAtlas (theta + t • omega.form)) phi K f => w.val x)
    ⟨v.val, sourceThetaPSH_perturb_mono omega hst v.property.1,
      v.property.2.1, v.property.2.2⟩

/-- An actual Kahler-current representative remains the SAME actual
Kahler current in every nonnegative enlarged background. -/
theorem sourceKahlerCurrent_perturb_nonneg (omega : KahlerBackground n X)
    {theta : ClosedRealOneOneForm n X} {phi : X → EReal}
    (hcurrent : AnalyticGluingData.IsKahlerCurrentPotential theta phi)
    {eps : ℝ} (heps : 0 ≤ eps) :
    AnalyticGluingData.IsKahlerCurrentPotential (theta + eps • omega.form) phi := by
  obtain ⟨kappa, hstrict⟩ := hcurrent
  refine ⟨kappa, ?_⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hstrict
    (KahlerDomination.isSemipositive_smul omega.isSemipositive heps)
  rwa [show theta - kappa.form + eps • omega.form =
    theta + eps • omega.form - kappa.form by module] at h

end SGPT.Bergman.BackgroundEnvelopeLimit
