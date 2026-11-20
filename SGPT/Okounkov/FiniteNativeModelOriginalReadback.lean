import SGPT.Okounkov.FiniteNativeModelCurrentValuation
import SGPT.Okounkov.SmoothModelOriginalReadback

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

/-- The native function for the empty initial sequence recovers the actual
original current flag valuation. Its adapted model is produced internally. -/
theorem finiteNativeModelCurrentFlagValuation_original_eq {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)}
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    finiteNativeModelCurrentFlagValuation
      (IsBlowupSequence.refl (X := F.carrier)) T hc h11 hT =
      (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  obtain ⟨W, h, hs, _hsTotal, hLift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F F.carrier id
      IsBlowupSequence.refl
  have hChoice := finiteNativeModelCurrentFlagValuation_eq_choice
    (IsBlowupSequence.refl (X := F.carrier)) hs hLift T hc h11 hT
  exact hChoice.trans (smoothModelCurrentFlagChoice_original_eq hLift T hc h11 hT)

/-- An actual finite initial map internally produces the original whole
pullback current, with every representation readback and its literal native
function equal to the original flag value. No adapted model is a premise. -/
theorem exists_finiteNativeModelCurrentFlagValuation_original_pullback {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z]
    {pi : Z → F.carrier} (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (Tpi : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m))),
      ∃ (hcpi : Tpi.IsClosed (canonicalBasis (m + 1)))
        (h11pi : Tpi.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hTpi : IsFullPositive Tpi),
        (∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : F.carrier → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          Tpi = analyticModificationThetaCurrent
            (isAnalyticModification_of_finiteBlowupSequence hpi) θ v hv) ∧
        finiteNativeModelCurrentFlagValuation hpi Tpi hcpi h11pi hTpi =
          (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  obtain ⟨Tpi, hcpi, h11pi, hTpi, hread, hvalue⟩ :=
    exists_finiteNativeModelCurrentFlagValuation_birational
      (IsBlowupSequence.refl (X := F.carrier)) hpi T hc h11 hT
  exact ⟨Tpi, hcpi, h11pi, hTpi, hread,
    hvalue.trans (finiteNativeModelCurrentFlagValuation_original_eq T hc h11 hT)⟩

end SGPT.Okounkov
