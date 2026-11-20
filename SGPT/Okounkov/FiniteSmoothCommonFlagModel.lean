import SGPT.Okounkov.FlagLiftingExistence
import SGPT.Okounkov.FlagLiftingCancellation

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Actual finite-sequence induction manufactures a common native space,
finite left refinement, genuine right analytic modification, and whole square.
The prescribed one-step producer was separately recursively axiom-audited. -/
theorem exists_domination_of_finiteBlowupSequence
    {n : ℕ} {Z Y0 Y1 : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z]
    [TopologicalSpace Y0] [ChartedSpace (ComplexModel n) Y0] [IsComplexManifold n Y0]
    [TopologicalSpace Y1] [ChartedSpace (ComplexModel n) Y1] [IsComplexManifold n Y1]
    {c : Y0 → Z} (hc : IsAnalyticModification (n := n) c)
    {b : Y1 → Z} (hb : IsBlowupSequence n Z Y1 b) :
    ∃ (U : Type u) (_ : TopologicalSpace U) (_ : ChartedSpace (ComplexModel n) U)
      (_ : IsComplexManifold n U) (s : U → Y0) (t : U → Y1),
      IsBlowupSequence n Y0 U s ∧ IsAnalyticModification (n := n) t ∧ c ∘ s = b ∘ t := by
  induction hb with
  | refl =>
      exact ⟨Y0, inferInstance, inferInstance, inferInstance, id, c,
        IsBlowupSequence.refl, hc, rfl⟩
  | step b C a hb ha ih =>
      obtain ⟨U0, topU0, chartsU0, complexU0, s0, t0, hs0, ht0, hcomm0⟩ := ih
      let := topU0
      let := chartsU0
      let := complexU0
      let := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hb).1
      obtain ⟨U, topU, chartsU, complexU, r, t, _D, _E, hr, _hrMod, ht,
        hsquare, _hIdeal, _hSNC, _hSupport⟩ :=
        PrescribedBlowupDomination.exists_domination_of_isBlowupAlong ha ht0
      let := topU
      let := chartsU
      let := complexU
      refine ⟨U, topU, chartsU, complexU, s0 ∘ r, t,
        isBlowupSequence_comp_nativeFlag hs0 hr.isBlowupSequence, ht, ?_⟩
      calc
        c ∘ (s0 ∘ r) = (c ∘ s0) ∘ r := rfl
        _ = (b ∘ t0) ∘ r := congrArg (fun f => f ∘ r) hcomm0
        _ = b ∘ (a ∘ t) := congrArg (fun f => b ∘ f) hsquare.symm
        _ = (b ∘ a) ∘ t := rfl

/-- The common whole original flag is PRODUCED on the same common source,
using full native flag existence. The two given choices supply no common
square or common flag certificate. All intermediate liftings are derived. -/
theorem exists_commonFlagRefinement_of_finiteSmoothModels
    {n : ℕ} (F W0 W1 : OriginalFlagGeometry.{u} n) {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z]
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := n) pi)
    {h0 : W0.carrier → Z} {h1 : W1.carrier → Z}
    (hs0 : IsBlowupSequence n Z W0.carrier h0)
    (hs1 : IsBlowupSequence n Z W1.carrier h1)
    (hLift0 : IsFlagLifting F W0 (pi ∘ h0))
    (hLift1 : IsFlagLifting F W1 (pi ∘ h1)) :
    ∃ (V : OriginalFlagGeometry.{u} n) (q0 : V.carrier → W0.carrier)
      (q1 : V.carrier → W1.carrier),
      IsBlowupSequence n W0.carrier V.carrier q0 ∧
      IsAnalyticModification (n := n) q1 ∧ h0 ∘ q0 = h1 ∘ q1 ∧
      IsFlagLifting F V ((pi ∘ h0) ∘ q0) ∧
      IsFlagLifting F V ((pi ∘ h1) ∘ q1) ∧
      IsFlagLifting W0 V q0 ∧ IsFlagLifting W1 V q1 := by
  have hh0 := isAnalyticModification_of_finiteBlowupSequence hs0
  obtain ⟨U, topU, chartsU, complexU, s, t, hs, ht, hcomm⟩ :=
    exists_domination_of_finiteBlowupSequence hh0 hs1
  let := topU
  let := chartsU
  let := complexU
  obtain ⟨compactU, ⟨omegaU⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨W0.omega⟩ s hs
  let := compactU
  have hgamma : IsAnalyticModification (n := n) (pi ∘ h0 ∘ s) :=
    AnalyticModificationComposition.isAnalyticModification_comp hpi
      (AnalyticModificationComposition.isAnalyticModification_comp hh0
        (isAnalyticModification_of_finiteBlowupSequence hs))
  obtain ⟨V, r, hr, hLift⟩ := exists_flagLifting_dominating_nativeModel n F U omegaU
    (pi ∘ h0 ∘ s) hgamma
  let q0 := s ∘ r
  let q1 := t ∘ r
  have hq0 : IsBlowupSequence n W0.carrier V.carrier q0 := isBlowupSequence_comp_nativeFlag hs hr
  have hq1 : IsAnalyticModification (n := n) q1 :=
    AnalyticModificationComposition.isAnalyticModification_comp ht
      (isAnalyticModification_of_finiteBlowupSequence hr)
  have hwhole : h0 ∘ q0 = h1 ∘ q1 := by
    funext v
    exact congrFun hcomm (r v)
  have hLiftV0 : IsFlagLifting F V ((pi ∘ h0) ∘ q0) := hLift
  have hLiftV1 : IsFlagLifting F V ((pi ∘ h1) ∘ q1) := by
    have heq : (pi ∘ h0) ∘ q0 = (pi ∘ h1) ∘ q1 := by
      funext v
      exact congrArg pi (congrFun hwhole v)
    exact heq ▸ hLiftV0
  exact ⟨V, q0, q1, hq0, hq1, hwhole, hLiftV0, hLiftV1,
    hLift0.of_comp hLiftV0 (isAnalyticModification_of_finiteBlowupSequence hq0),
    hLift1.of_comp hLiftV1 hq1⟩

end SGPT.Okounkov
