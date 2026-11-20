import SGPT.Okounkov.NativeModelCurrentValuation
import SGPT.Okounkov.FiniteNativeModelOriginalReadback

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

/-- The two independently defined native functions agree on actual finite
initial maps, for any actual source Kähler background, by computing on the
same internally produced finite adapted flag and whole current. -/
theorem finiteNativeModelCurrentFlagValuation_eq_native {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] (omegaZ : KahlerBackground (m + 1) Z)
    {pi : Z → F.carrier} (hpi : IsBlowupSequence (m + 1) F.carrier Z pi)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    finiteNativeModelCurrentFlagValuation hpi T hc h11 hT =
      nativeModelCurrentFlagValuation omegaZ
        (isAnalyticModification_of_finiteBlowupSequence hpi) T hc h11 hT := by
  obtain ⟨W, h, hs, _hsTotal, hLift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F Z pi hpi
  have hFinite := finiteNativeModelCurrentFlagValuation_eq_choice hpi hs hLift T hc h11 hT
  have hNative := nativeModelCurrentFlagValuation_eq_choice omegaZ
    (isAnalyticModification_of_finiteBlowupSequence hpi) hs.contMDiff hLift T hc h11 hT
  exact hFinite.trans hNative.symm

/-- The actual analytic native identity function is the original current
flag value in the reals; its finite/native bridge retains the signed correction. -/
theorem nativeModelCurrentFlagValuation_original_eq {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)}
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    nativeModelCurrentFlagValuation F.omega
      (isAnalyticModification_identity (n := m + 1) (X := F.carrier)) T hc h11 hT =
      (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  have hBridge := finiteNativeModelCurrentFlagValuation_eq_native F.omega
    (IsBlowupSequence.refl (X := F.carrier)) T hc h11 hT
  exact hBridge.symm.trans (finiteNativeModelCurrentFlagValuation_original_eq T hc h11 hT)

/-- Every actual analytic native original map with its actual Kähler geometry
internally produces the whole original pullback with all readbacks and native
function equal to the original flag value. No finite initial map is assumed. -/
theorem exists_nativeModelCurrentFlagValuation_original_pullback {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] (omegaZ : KahlerBackground (m + 1) Z)
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
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
          Tpi = analyticModificationThetaCurrent hpi θ v hv) ∧
        nativeModelCurrentFlagValuation omegaZ hpi Tpi hcpi h11pi hTpi =
          (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  obtain ⟨Tpi, hcpi, h11pi, hTpi, hread, hvalue⟩ :=
    exists_nativeModelCurrentFlagValuation_birational F.omega omegaZ
      (isAnalyticModification_identity (n := m + 1) (X := F.carrier)) hpi T hc h11 hT
  exact ⟨Tpi, hcpi, h11pi, hTpi, hread,
    hvalue.trans (nativeModelCurrentFlagValuation_original_eq T hc h11 hT)⟩

end SGPT.Okounkov
