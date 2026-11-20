import SGPT.Okounkov.CurrentFlagCorrection
import SGPT.Okounkov.FlagCorrectionReal
import SGPT.Okounkov.FlagLiftingCancellation

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped NNReal ENNReal Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open AnalyticModificationLocalDiscrepancy

/-- The actual original current vector, corrected by the SAME genuine
signed real inverse on this smooth model. No sign truncation is introduced. -/
def correctedModelCurrentFlagValuation {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ :=
  (flagLiftingCorrectionReal (m + 1) F W π hπ).symm
    (fun i => (currentFlagValuation W T hc h11 hT i : ℝ))

/-- The original two lifting premises internally manufacture the intermediate
lifting and the unique whole current pullback. Its signed corrected vector
is unchanged; no representation or current/vector equality is a premise. -/
theorem exists_unique_correctedModelCurrentFlagValuation_pullback {m : ℕ}
    {F W V : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hq : IsFlagLifting F V (π ∘ p))
    (hpmod : IsAnalyticModification (n := m + 1) p)
    (T : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! S : GlobalCurrent (m + 1) V.carrier (degreeTwo (Nat.succ_pos m)),
      ∃ (hcS : S.IsClosed (canonicalBasis (m + 1)))
        (h11S : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hS : IsFullPositive S),
        (∀ (θ : ClosedRealOneOneForm (m + 1) W.carrier) (v : W.carrier → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          S = thetaPotentialModificationCurrent (hπ.of_comp hq hpmod) θ v hv) ∧
        correctedModelCurrentFlagValuation hq S hcS h11S hS =
          correctedModelCurrentFlagValuation hπ T hc h11 hT := by
  let hp := hπ.of_comp hq hpmod
  obtain ⟨S, ⟨hcS, h11S, hS, hall, _hNN, hMatrix⟩, _huniq⟩ :=
    exists_originalCurrentFlagValuation_pullback_correctionMatrix hp T hc h11 hT
  change flagLiftingCorrectionReal (m + 1) W V p hp
    (fun i => (currentFlagValuation W T hc h11 hT i : ℝ)) =
      (fun j => (currentFlagValuation V S hcS h11S hS j : ℝ)) at hMatrix
  refine ⟨S, ⟨hcS, h11S, hS, hall, ?_⟩, ?_⟩
  · unfold correctedModelCurrentFlagValuation
    rw [← hMatrix]
    exact flagLiftingCorrectionReal_comp_symm_apply (m + 1) F W V π p hπ hp _
  · rintro R ⟨hcR, h11R, hR, hallR, _hvector⟩
    obtain ⟨P, _hP, huniqP⟩ :=
      exists_unique_original_current_modification_pullback hp T hc h11 hT
    exact (huniqP R ⟨hcR, h11R, hR, hallR⟩).trans
      (huniqP S ⟨hcS, h11S, hS, hall⟩).symm

/-- Arbitrary original base currents internally produce their unique whole
pullback; the actual corrected vector recovers the original real valuation. -/
theorem exists_unique_originalCurrent_correctedModel_recovery {m : ℕ}
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
        (∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : F.carrier → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          R = thetaPotentialModificationCurrent hπ θ v hv) ∧
        correctedModelCurrentFlagValuation hπ R hcR h11R hR =
          (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  obtain ⟨R, ⟨hcR, h11R, hR, hall, _hNN, hMatrix⟩, _huniq⟩ :=
    exists_originalCurrentFlagValuation_pullback_correctionMatrix hπ T hc h11 hT
  change flagLiftingCorrectionReal (m + 1) F W π hπ
    (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) =
      (fun j => (currentFlagValuation W R hcR h11R hR j : ℝ)) at hMatrix
  refine ⟨R, ⟨hcR, h11R, hR, hall, ?_⟩, ?_⟩
  · unfold correctedModelCurrentFlagValuation
    rw [← hMatrix]
    exact (flagLiftingCorrectionReal (m + 1) F W π hπ).symm_apply_apply _
  · rintro S ⟨hcS, h11S, hS, hallS, _hvector⟩
    obtain ⟨P, _hP, huniqP⟩ :=
      exists_unique_original_current_modification_pullback hπ T hc h11 hT
    exact (huniqP S ⟨hcS, h11S, hS, hallS⟩).trans
      (huniqP R ⟨hcR, h11R, hR, hall⟩).symm

end SGPT.Okounkov
