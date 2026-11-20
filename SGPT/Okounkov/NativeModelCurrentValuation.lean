import SGPT.Okounkov.OneFiniteSmoothCommonFlagModel
import SGPT.Okounkov.SmoothModelBirationalChoice

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- The original signed function for an arbitrary actual native analytic
initial map with an actual Kähler background. Properness supplies compactness,
and full native existence supplies the finite adapted model internally. -/
def nativeModelCurrentFlagValuation (omegaZ : KahlerBackground (m + 1) Z)
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ :=
  letI : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
  let result := exists_flagLifting_dominating_nativeModel (m + 1) F Z omegaZ pi hpi
  let W := Classical.choose result
  let h := Classical.choose (Classical.choose_spec result)
  let hs := Classical.choose_spec (Classical.choose_spec result)
  smoothModelCurrentFlagChoice (W := W) (h := h) hpi hs.1.contMDiff hs.2 T hc h11 hT

/-- Every native holomorphic adapted smooth choice computes the internally
defined signed function. Neither the initial nor the other choice map is
assumed finite, and no common square/current/value certificate is supplied. -/
theorem nativeModelCurrentFlagValuation_eq_choice
    (omegaZ : KahlerBackground (m + 1) Z) {W : OriginalFlagGeometry.{u} (m + 1)}
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    {h : W.carrier → Z}
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hLift : IsFlagLifting F W (pi ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    letI : CompactSpace Z :=
      AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
    nativeModelCurrentFlagValuation omegaZ hpi T hc h11 hT =
      smoothModelCurrentFlagChoice hpi hh hLift T hc h11 hT := by
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
  let result := exists_flagLifting_dominating_nativeModel (m + 1) F Z omegaZ pi hpi
  have hs0 := Classical.choose_spec (Classical.choose_spec result)
  exact smoothModelCurrentFlagChoice_eq_of_one_finiteModel hpi hs0.1 hh
    hs0.2 hLift T hc h11 hT

/-- A Kähler background is used only to produce an adapted model: any two
actual backgrounds on the same native model give the identical signed value. -/
theorem nativeModelCurrentFlagValuation_background_eq
    (omega0 omega1 : KahlerBackground (m + 1) Z)
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    nativeModelCurrentFlagValuation omega0 hpi T hc h11 hT =
      nativeModelCurrentFlagValuation omega1 hpi T hc h11 hT := by
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
  obtain ⟨W, h, hs, hLift⟩ :=
    exists_flagLifting_dominating_nativeModel (m + 1) F Z omega0 pi hpi
  exact (nativeModelCurrentFlagValuation_eq_choice omega0 hpi hs.contMDiff hLift T hc h11 hT).trans
    (nativeModelCurrentFlagValuation_eq_choice omega1 hpi hs.contMDiff hLift T hc h11 hT).symm

/-- The definition produces its actual finite adapted model and actual unique
whole current with every original representation readback and signed value.
No finite-sequence conclusion for the arbitrary initial composite is made. -/
theorem nativeModelCurrentFlagValuation_spec
    (omegaZ : KahlerBackground (m + 1) Z)
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (W : OriginalFlagGeometry.{u} (m + 1)) (h : W.carrier → Z)
      (_hs : IsBlowupSequence (m + 1) Z W.carrier h)
      (hLift : IsFlagLifting F W (pi ∘ h))
      (hf : IsAnalyticModification (n := m + 1) h)
      (R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m))),
      ∃ (hcR : R.IsClosed (canonicalBasis (m + 1)))
        (h11R : R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR : IsFullPositive R),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          R = analyticModificationThetaCurrent hf θ v hv) ∧
        nativeModelCurrentFlagValuation omegaZ hpi T hc h11 hT =
          correctedModelCurrentFlagValuation hLift R hcR h11R hR := by
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
  let result := exists_flagLifting_dominating_nativeModel (m + 1) F Z omegaZ pi hpi
  let W := Classical.choose result
  let h := Classical.choose (Classical.choose_spec result)
  have hs := Classical.choose_spec (Classical.choose_spec result)
  obtain ⟨hf, R, hcR, h11R, hR, hread, hvalue⟩ :=
    smoothModelCurrentFlagChoice_spec hpi hs.1.contMDiff hs.2 T hc h11 hT
  exact ⟨W, h, hs.1, hs.2, hf, R, hcR, h11R, hR, hread, hvalue⟩

/-- An arbitrary actual analytic further map of native smooth Kähler models
produces its whole current and preserves the independently defined function.
The same original composite flag is produced internally; p need not be finite. -/
theorem exists_nativeModelCurrentFlagValuation_birational
    (omegaZ : KahlerBackground (m + 1) Z)
    {Z' : Type u} [TopologicalSpace Z']
    [ChartedSpace (ComplexModel (m + 1)) Z'] [IsComplexManifold (m + 1) Z']
    (omegaZ' : KahlerBackground (m + 1) Z')
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    {p : Z' → Z} (hp : IsAnalyticModification (n := m + 1) p)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (T' : GlobalCurrent (m + 1) Z' (degreeTwo (Nat.succ_pos m))),
      ∃ (hc' : T'.IsClosed (canonicalBasis (m + 1)))
        (h11' : T'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hT' : IsFullPositive T'),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          T' = analyticModificationThetaCurrent hp θ v hv) ∧
        nativeModelCurrentFlagValuation omegaZ'
          (AnalyticModificationComposition.isAnalyticModification_comp hpi hp)
          T' hc' h11' hT' = nativeModelCurrentFlagValuation omegaZ hpi T hc h11 hT := by
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hpi
  let : CompactSpace Z' :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hp
  have hTotal := AnalyticModificationComposition.isAnalyticModification_comp hpi hp
  obtain ⟨W, h, hs, hLift⟩ :=
    exists_flagLifting_dominating_nativeModel (m + 1) F Z' omegaZ' (pi ∘ p) hTotal
  obtain ⟨T', hc', h11', hT', hread, hvalue⟩ :=
    exists_smoothModelCurrentFlagChoice_birational hpi hp hs.contMDiff hLift T hc h11 hT
  refine ⟨T', hc', h11', hT', hread, ?_⟩
  have hUp := nativeModelCurrentFlagValuation_eq_choice omegaZ' hTotal hs.contMDiff
    hLift T' hc' h11' hT'
  have hDown := nativeModelCurrentFlagValuation_eq_choice omegaZ hpi
    (hp.1.comp hs.contMDiff) hLift T hc h11 hT
  exact hUp.trans (hvalue.trans hDown.symm)

end SGPT.Okounkov
