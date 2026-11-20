import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Okounkov.TranscendentalL2Corollaries
import SGPT.Okounkov.TranscendentalLiftingResolution
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial

/-! Actual bounded-residual divisor translation used by whole source lma:slicepob.
Resolution data and identity geometry are manufactured from the actual input
potential decomposition; no body identity is a caller premise. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody

/-- The actual identity map lifts every original supplied flag. -/
theorem identityFlagLifting {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    IsFlagLifting F F id := by
  refine ⟨isAnalyticModification_identity, fun i => ⟨fun _ h => h, ?_⟩⟩
  let := F.componentCharts i
  let := F.componentComplex i
  change IsAnalyticModification (n := n - (i : ℕ)) (id : F.flag i → F.flag i)
  exact isAnalyticModification_identity

/-- The genuine correction matrix for the identity flag lifting is the identity. -/
theorem correctionMatrixReal_identity {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    correctionMatrixReal (identityFlagLifting F) = 1 := by
  let h := identityFlagLifting F
  let g := correctionMatrixReal h
  have hid : g = g * g := correctionMatrixReal_comp h h h
  have hinv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_det_correctionMatrixReal h)
  have heq := congrArg (fun A => A * g⁻¹) hid
  simpa only [Matrix.mul_assoc, hinv, Matrix.mul_one] using heq.symm

/-- Exact source body translation for a genuine original analytic Kähler
current D+b with bounded psh residual; no resolution or body equality is supplied. -/
theorem generalPartialBody_eq_divisor_translate_of_bounded
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφA : φ ∈ globalAnalyticCurrents θ) (hφK : IsKahlerCurrentPotential θ φ)
    (D : MeteredEffectiveQDivisor (m + 1) F.carrier) (b : F.carrier → EReal)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (hbounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    (heq : ∀ y, φ y = D.weight y + b y) :
    generalPartialBody F θ φ =
      flagValuation F D.weight +ᵥ tradOkounkovBody F (θ - D.curvature) := by
  let hid := identityFlagLifting F
  have hgeo : (ClosedRealOneOneForm.pullback hid.1.1 θ).val.GeometricallyEq θ.val :=
    SmoothRealForm.pullback_id_geometricallyEq θ.val
  have hgeoR : (ClosedRealOneOneForm.pullback hid.1.1 θ - D.curvature).val.GeometricallyEq
      (θ - D.curvature).val := by
    intro e z hz
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg]
    rw [hgeo e hz]
  have hR : IsResolutionData θ φ hid D b :=
    ⟨(hgeoR.thetaPshPotential_iff b).mpr hb, hbounded, heq⟩
  have htrad : tradOkounkovBody F (ClosedRealOneOneForm.pullback hid.1.1 θ - D.curvature) =
      tradOkounkovBody F (θ - D.curvature) :=
    tradOkounkovBody_eq_of_class_eq (RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeoR)
  calc
    generalPartialBody F θ φ = partialOkounkovBody F θ φ :=
      (generalPartialBody_eq_analyticPartialBody hφA hφK).trans
        (TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody hφA hφK)
    _ = analyticPartialBodyOf θ hid D :=
      (TranscendentalPartial.analyticPartialBodyOf_eq_partialOkounkovBody
        TranscendentalL2.pushforwardAnalyticStatement hR hφK
        (globalAnalyticCurrents_subset_analyticCurrents θ hφA)).symm
    _ = flagValuation F D.weight +ᵥ tradOkounkovBody F (θ - D.curvature) := by
      rw [analyticPartialBodyOf_eq_image]
      simp only [correctionMatrixReal_identity F, inv_one, Matrix.vecMul_one, htrad]
      exact Set.image_id _
end SGPT.Okounkov.SourceSlice
