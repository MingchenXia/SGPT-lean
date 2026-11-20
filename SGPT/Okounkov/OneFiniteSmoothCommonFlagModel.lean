import SGPT.Okounkov.FiniteSmoothCommonFlagModel
import SGPT.Okounkov.SmoothModelValuationChoice

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

/-- One actual finite choice suffices to manufacture a common original flag
with every native smooth holomorphic adapted choice. The other modification
record, square, common source and full common flag are produced internally. -/
theorem exists_commonFlagRefinement_of_one_finiteModel
    {n : ℕ} (F W0 W1 : OriginalFlagGeometry.{u} n) {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z]
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := n) pi)
    {h0 : W0.carrier → Z} {h1 : W1.carrier → Z}
    (hs0 : IsBlowupSequence n Z W0.carrier h0)
    (hh1 : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h1)
    (hLift0 : IsFlagLifting F W0 (pi ∘ h0))
    (hLift1 : IsFlagLifting F W1 (pi ∘ h1)) :
    ∃ (V : OriginalFlagGeometry.{u} n) (q0 : V.carrier → W0.carrier)
      (q1 : V.carrier → W1.carrier),
      IsAnalyticModification (n := n) q0 ∧ IsBlowupSequence n W1.carrier V.carrier q1 ∧
      h0 ∘ q0 = h1 ∘ q1 ∧ IsFlagLifting F V ((pi ∘ h0) ∘ q0) ∧
      IsFlagLifting F V ((pi ∘ h1) ∘ q1) ∧
      IsFlagLifting W0 V q0 ∧ IsFlagLifting W1 V q1 := by
  have hh1mod := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hpi hLift1.1 hh1 rfl
  obtain ⟨U, topU, chartsU, complexU, s, t, hs, ht, hcomm⟩ :=
    exists_domination_of_finiteBlowupSequence hh1mod hs0
  let := topU
  let := chartsU
  let := complexU
  obtain ⟨compactU, ⟨omegaU⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨W1.omega⟩ s hs
  let := compactU
  have hgamma : IsAnalyticModification (n := n) (pi ∘ h1 ∘ s) :=
    AnalyticModificationComposition.isAnalyticModification_comp hpi
      (AnalyticModificationComposition.isAnalyticModification_comp hh1mod
        (isAnalyticModification_of_finiteBlowupSequence hs))
  obtain ⟨V, r, hr, hLift⟩ := exists_flagLifting_dominating_nativeModel n F U omegaU
    (pi ∘ h1 ∘ s) hgamma
  let q0 := t ∘ r
  let q1 := s ∘ r
  have hq0 : IsAnalyticModification (n := n) q0 :=
    AnalyticModificationComposition.isAnalyticModification_comp ht
      (isAnalyticModification_of_finiteBlowupSequence hr)
  have hq1 : IsBlowupSequence n W1.carrier V.carrier q1 := isBlowupSequence_comp_nativeFlag hs hr
  have hwhole : h0 ∘ q0 = h1 ∘ q1 := by
    funext v
    exact (congrFun hcomm (r v)).symm
  have hLiftV1 : IsFlagLifting F V ((pi ∘ h1) ∘ q1) := hLift
  have hLiftV0 : IsFlagLifting F V ((pi ∘ h0) ∘ q0) := by
    have heq : (pi ∘ h1) ∘ q1 = (pi ∘ h0) ∘ q0 := by
      funext v
      exact congrArg pi (congrFun hwhole v).symm
    exact heq ▸ hLiftV1
  exact ⟨V, q0, q1, hq0, hq1, hwhole, hLiftV0, hLiftV1,
    hLift0.of_comp hLiftV0 hq0,
    hLift1.of_comp hLiftV1 (isAnalyticModification_of_finiteBlowupSequence hq1)⟩

/-- An actual finite choice compares with every native holomorphic adapted
choice using internally produced common geometry and unique whole currents.
Finiteness of the second chosen model map is neither assumed nor concluded. -/
theorem smoothModelCurrentFlagChoice_eq_of_one_finiteModel
    {m : ℕ} {F W0 W1 : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    {h0 : W0.carrier → Z} {h1 : W1.carrier → Z}
    (hs0 : IsBlowupSequence (m + 1) Z W0.carrier h0)
    (hh1 : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h1)
    (hLift0 : IsFlagLifting F W0 (pi ∘ h0))
    (hLift1 : IsFlagLifting F W1 (pi ∘ h1))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    smoothModelCurrentFlagChoice hpi hs0.contMDiff hLift0 T hc h11 hT =
      smoothModelCurrentFlagChoice hpi hh1 hLift1 T hc h11 hT := by
  obtain ⟨V, q0, q1, hq0, hq1, hcomm, hCommon, _hCommon1, _hInter0, _hInter1⟩ :=
    exists_commonFlagRefinement_of_one_finiteModel F W0 W1 hpi hs0 hh1 hLift0 hLift1
  exact smoothModelCurrentFlagChoice_eq_common hpi hs0.contMDiff hh1
    hq0.1 hq1.contMDiff hLift0 hLift1 hCommon hcomm T hc h11 hT

end SGPT.Okounkov
