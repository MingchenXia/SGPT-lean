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

/-- The original defined signed current values of two genuine finite native
smooth choices agree. The common space, square, and entire common original
flag are manufactured internally; no common-geometry or value certificate
is a premise. Whole-current uniqueness and original correction are retained. -/
theorem smoothModelCurrentFlagChoice_eq_of_finiteModels
    {m : ℕ} {F W0 W1 : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    {pi : Z → F.carrier} (hpi : IsAnalyticModification (n := m + 1) pi)
    {h0 : W0.carrier → Z} {h1 : W1.carrier → Z}
    (hs0 : IsBlowupSequence (m + 1) Z W0.carrier h0)
    (hs1 : IsBlowupSequence (m + 1) Z W1.carrier h1)
    (hLift0 : IsFlagLifting F W0 (pi ∘ h0))
    (hLift1 : IsFlagLifting F W1 (pi ∘ h1))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    smoothModelCurrentFlagChoice hpi hs0.contMDiff hLift0 T hc h11 hT =
      smoothModelCurrentFlagChoice hpi hs1.contMDiff hLift1 T hc h11 hT := by
  obtain ⟨V, q0, q1, hq0, hq1, hcomm, hCommon, _hCommon1, _hInter0, _hInter1⟩ :=
    exists_commonFlagRefinement_of_finiteSmoothModels F W0 W1 hpi hs0 hs1 hLift0 hLift1
  exact smoothModelCurrentFlagChoice_eq_common hpi hs0.contMDiff hs1.contMDiff
    hq0.contMDiff hq1.1 hLift0 hLift1 hCommon hcomm T hc h11 hT

end SGPT.Okounkov
