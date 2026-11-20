import SGPT.Okounkov.OF12FlaggedResolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov.ValCurr SGPT.Okounkov.OCSpaceFormNative
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open scoped Matrix

noncomputable section

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}

attribute [local instance] resolutionPointTopology resolutionPointCharts resolutionPointManifold

/-- Pull back a current along the full flagged projection in one step. -/
def Presentation.flaggedPullbackCurrent
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) (hXu : (UnibAn.analytification f).IsUnibranch)
    (θ : SpaceForm (UnibAn.analytification f) 2)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    GlobalCurrent (m + 1) Q.P.F.carrier (degreeTwo (Nat.succ_pos m)) :=
  thetaPotentialCurrent (nativePullback Q.flaggedProjection θ)
    (nativePotential Q.flaggedProjection ψ)
    (isThetaPshPotential_nativePullback Q.flaggedProjection θ hψ hXu
      Q.flaggedProjection_isResolution.2)

/-- The composite pullback and the two successive pullbacks define the same whole current. -/
theorem Presentation.flaggedPullbackCurrent_eq
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) (hXu : (UnibAn.analytification f).IsUnibranch)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    Q.flaggedPullbackCurrent hXu θ ψ hψ =
      analyticModificationThetaCurrent Q.P.isModification (Q.R.pullbackForm θ hθ)
        (Q.R.pullbackPotential ψ) (Q.R.isThetaPshPotential_pullback hXu θ hθ ψ hψ) := by
  unfold Presentation.flaggedPullbackCurrent analyticModificationThetaCurrent
  apply thetaPotentialCurrent_eq_of_geometricallyEq
  exact nativePullback_comp_geometricallyEq Q.R.π θ Q.P.isBlowupSequence.contMDiff

/-- Read the value from the current pulled back along the full flagged projection. -/
theorem Presentation.value_eq_flaggedPullback
    {ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m ν) (hXu : (UnibAn.analytification f).IsUnibranch)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    let hdata := thetaPotentialCurrent_closed_type_positive
      (nativePullback Q.flaggedProjection θ) (nativePotential Q.flaggedProjection ψ)
      (isThetaPshPotential_nativePullback Q.flaggedProjection θ hψ hXu
        Q.flaggedProjection_isResolution.2)
    Q.value hXu θ hθ ψ hψ =
      (fun i => (currentFlagValuation Q.P.F (Q.flaggedPullbackCurrent hXu θ ψ hψ)
        hdata.1 hdata.2.1 hdata.2.2 i : ℝ)) ᵥ* (Int.castRingHom ℝ).mapMatrix Q.P.G := by
  dsimp only
  unfold Presentation.value OF2.modificationPresentationValue
  congr 1
  funext i
  exact congrArg (fun v => (v i : ℝ))
    (OF2.currentFlagValuation_congr_current' Q.P.F
      (Q.flaggedPullbackCurrent_eq hXu θ hθ ψ hψ).symm _ _ _ _ _ _)

/-- Every surjective valuation in the projective positive-dimensional setting uses
the presentation branch of the current-value definition. -/
theorem valuationCurrentValue_eq_on_normalProjective
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ))
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ Q : Presentation f m ν, ∀ (θ : SpaceForm (UnibAn.analytification f) 2)
        (hθ : PD.IsLocallyClosedOneOne θ) (ψ : (UnibAn.analytification f).obj.left → EReal)
        (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ),
      valuationCurrentValue f m hX ν θ hθ ψ hψ =
        Q.value (isUnibranch_analytification_of_normal f hX) θ hθ ψ hψ := by
  obtain ⟨Q, _, _⟩ := exists_flaggedResolution_of_normalProjective E hX hdim ν hν
  exact ⟨Q, fun θ hθ ψ hψ => valuationCurrentValue_eq hX hν Q θ hθ ψ hψ⟩

/-- In dimension zero every current-value vector is the empty vector. -/
theorem currentValue_fin_zero_eq (v : Fin 0 → ℝ) : v = 0 :=
  Subsingleton.elim _ _

end

end SGPT.Okounkov.OF12
