import SGPT.Okounkov.FlagCurrentPullbackFirst

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open NaturalThetaPshClosedCurrent SourceTraceRepresentativeDefinition

/-- The whole original vector base in complex dimension one follows from
actual first-source covariance and genuine singleton-index extensionality. -/
theorem thetaPotentialModificationCurrent_one_valuation_eq
    {F W : OriginalFlagGeometry.{u} 1} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (θ : ClosedRealOneOneForm 1 F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
    let hs := thetaPotentialCurrent_closed_type_positive θ.val u hu
    currentFlagValuation W (thetaPotentialModificationCurrent hπ θ u hu)
      hp.1 hp.2.1 hp.2.2 =
    currentFlagValuation F (thetaPotentialCurrent θ.val u hu)
      hs.1 hs.2.1 hs.2.2 := by
  apply funext
  intro i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  exact thetaPotentialModificationCurrent_first hπ θ u hu

/-- The arbitrary original current internally produces its representation
and actual whole pulled current, with the entire singleton vector preserved. -/
theorem exists_original_current_modification_one_valuation_eq
    {F W : OriginalFlagGeometry.{u} 1} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent 1 F.carrier (degreeTwo (Nat.succ_pos 0)))
    (hc : T.IsClosed (canonicalBasis 1))
    (h11 : T.IsTypeOneOne (canonicalBasis 1) (Nat.succ_pos 0))
    (hT : IsFullPositive T) :
    ∃ (θ : ClosedRealOneOneForm 1 F.carrier) (u : F.carrier → EReal)
      (hu : IsThetaPshPotential θ.val u), T = thetaPotentialCurrent θ.val u hu ∧
      let hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
      currentFlagValuation W (thetaPotentialModificationCurrent hπ θ u hu)
        hp.1 hp.2.1 hp.2.2 = currentFlagValuation F T hc h11 hT := by
  obtain ⟨θ, u, hu, hread, hfirst⟩ :=
    exists_original_current_modification_first hπ T hc h11 hT
  refine ⟨θ, u, hu, hread, ?_⟩
  apply funext
  intro i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  exact hfirst

end SGPT.Okounkov
