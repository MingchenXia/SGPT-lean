import SGPT.Okounkov.PotentialFlagCorrection
import SGPT.Okounkov.FlagCorrectionMatrix
import SGPT.Okounkov.ThetaCurrentPullbackCompatibility

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set
open scoped NNReal ENNReal Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open SourceTraceRepresentativeDefinition

/-- An arbitrary original current internally produces its unique whole
modification pullback. Its genuine finite valuation is the original geometric
correction, with the literal SAME integer matrix on the right. -/
theorem exists_originalCurrentFlagValuation_pullback_correctionMatrix {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)),
      ∃ (hcR : R.IsClosed (canonicalBasis (m + 1)))
        (h11R : R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR : IsFullPositive R),
        (∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
          (hu : IsThetaPshPotential θ.val u), T = thetaPotentialCurrent θ.val u hu →
          R = thetaPotentialModificationCurrent hπ θ u hu) ∧
        currentFlagValuation W R hcR h11R hR =
          flagLiftingCorrectionNNReal (m + 1) F W π hπ
            (currentFlagValuation F T hc h11 hT) ∧
        (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) ᵥ*
          (fun i j => (flagLiftingCorrectionMatrix (m + 1) F W π hπ i j : ℝ)) =
            fun j => (currentFlagValuation W R hcR h11R hR j : ℝ) := by
  obtain ⟨R, ⟨hcR, h11R, hR, hall⟩, huniq⟩ :=
    exists_unique_original_current_modification_pullback hπ T hc h11 hT
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hc h11 hT
  let hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hu
  have hRread := hall θ u hu hread
  have hRval := currentFlagValuation_eq_potentialFlagValuation W R hcR h11R hR
    (θ := ClosedRealOneOneForm.pullback hπ.1.1 θ) hup hRread
  have hTval := currentFlagValuation_eq_potentialFlagValuation F T hc h11 hT hu hread
  have hNN : currentFlagValuation W R hcR h11R hR =
      flagLiftingCorrectionNNReal (m + 1) F W π hπ
        (currentFlagValuation F T hc h11 hT) := by
    rw [hRval, hTval]
    exact potentialFlagValuation_modification_eq_correctionNNReal (m + 1) F W π hπ θ u hu
  refine ⟨R, ⟨hcR, h11R, hR, hall, hNN, ?_⟩, ?_⟩
  · rw [hNN]
    exact flagLiftingCorrectionMatrix_vecMul_nnreal (m + 1) F W π hπ
      (currentFlagValuation F T hc h11 hT)
  · rintro S ⟨hcS, h11S, hS, hallS, _hNNS, _hMatrixS⟩
    exact huniq S ⟨hcS, h11S, hS, hallS⟩

end SGPT.Okounkov
