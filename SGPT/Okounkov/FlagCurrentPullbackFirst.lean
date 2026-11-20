import SGPT.Okounkov.FlagLiftingStrictTransform
import SGPT.Okounkov.CurrentFlagValuation
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open NaturalThetaPshClosedCurrent SourceTraceRepresentativeDefinition

/-- The actual whole current of the genuine pulled theta representation.
It does not assume or assert whole-current representation independence. -/
def thetaPotentialModificationCurrent {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)) :=
  thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1.1 θ).val (u ∘ π)
    (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ.1 θ hu)

/-- Actual modification and source theta data manufacture all whole-current
closedness, type and full-positive test pairings upstairs. -/
theorem thetaPotentialModificationCurrent_closed_type_positive {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    (thetaPotentialModificationCurrent hπ θ u hu).IsClosed (canonicalBasis (m + 1)) ∧
    (thetaPotentialModificationCurrent hπ θ u hu).IsTypeOneOne
      (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    IsFullPositive (thetaPotentialModificationCurrent hπ θ u hu) :=
  thetaPotentialCurrent_closed_type_positive _ _ _

/-- Genuine strict-transform source-reader covariance proves the actual
first coefficient of the manufactured whole pulled current. -/
theorem thetaPotentialModificationCurrent_first {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
    let hs := thetaPotentialCurrent_closed_type_positive θ.val u hu
    currentFlagValuation W (thetaPotentialModificationCurrent hπ θ u hu)
      hp.1 hp.2.1 hp.2.2 0 =
    currentFlagValuation F (thetaPotentialCurrent θ.val u hu)
      hs.1 hs.2.1 hs.2.2 0 := by
  let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
  let hs := thetaPotentialCurrent_closed_type_positive θ.val u hu
  let hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 θ hu
  have hW := congrFun (currentFlagValuation_eq_potentialFlagValuation W
    (thetaPotentialModificationCurrent hπ θ u hu) hp.1 hp.2.1 hp.2.2
    (θ := ClosedRealOneOneForm.pullback hπ.1.1 θ) hup rfl) 0
  have hF := congrFun (currentFlagValuation_eq_potentialFlagValuation F
    (thetaPotentialCurrent θ.val u hu) hs.1 hs.2.1 hs.2.2 hu rfl) 0
  have heq : (potentialFlagValuation W hup 0 : ℝ≥0∞) =
      (potentialFlagValuation F hu 0 : ℝ≥0∞) := by
    rw [potentialFlagValuation_first W hup, potentialFlagValuation_first F hu]
    exact hπ.sourceGeneric_first_comp_eq hu.quasiPshPotential
  have heqNN : potentialFlagValuation W hup 0 = potentialFlagValuation F hu 0 := by
    exact_mod_cast heq
  exact hW.trans (heqNN.trans hF.symm)

/-- Every arbitrary original whole closed/full-positive current internally
supplies a genuine global representation and actual upstairs current with
its exact original first coefficient. No representation is a caller premise. -/
theorem exists_original_current_modification_first {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
      (hu : IsThetaPshPotential θ.val u), T = thetaPotentialCurrent θ.val u hu ∧
      let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
      currentFlagValuation W (thetaPotentialModificationCurrent hπ θ u hu)
        hp.1 hp.2.1 hp.2.2 0 = currentFlagValuation F T hc h11 hT 0 := by
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hc h11 hT
  refine ⟨θ, u, hu, hread, ?_⟩
  let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
  let hs := thetaPotentialCurrent_closed_type_positive θ.val u hu
  have hfirst : currentFlagValuation W (thetaPotentialModificationCurrent hπ θ u hu)
      hp.1 hp.2.1 hp.2.2 0 =
      currentFlagValuation F (thetaPotentialCurrent θ.val u hu) hs.1 hs.2.1 hs.2.2 0 :=
    thetaPotentialModificationCurrent_first hπ θ u hu
  have hsource := congrFun
    (currentFlagValuation_eq_potentialFlagValuation F T hc h11 hT hu hread) 0
  have htheta := congrFun (currentFlagValuation_eq_potentialFlagValuation F
    (thetaPotentialCurrent θ.val u hu) hs.1 hs.2.1 hs.2.2 hu rfl) 0
  exact hfirst.trans (htheta.trans hsource.symm)

end SGPT.Okounkov
