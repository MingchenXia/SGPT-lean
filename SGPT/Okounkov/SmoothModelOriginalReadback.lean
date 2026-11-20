import SGPT.Okounkov.SmoothModelBirationalChoice

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

/-- The original current model is recovered by whole-current uniqueness,
before the SAME signed correction inverse is applied to its flag vector. -/
theorem smoothModelCurrentFlagChoice_original_eq {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {h : W.carrier → F.carrier}
    (hh : IsFlagLifting F W h)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    smoothModelCurrentFlagChoice
      (isAnalyticModification_identity (n := m + 1) (X := F.carrier))
      hh.1.1 hh T hc h11 hT =
      (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  obtain ⟨hs, S, hcS, h11S, hS, hreadS, hvalue⟩ :=
    smoothModelCurrentFlagChoice_spec
      (isAnalyticModification_identity (n := m + 1) (X := F.carrier))
      hh.1.1 hh T hc h11 hT
  obtain ⟨R, ⟨hcR, h11R, hR, hreadR, hvector⟩, _huniqR⟩ :=
    exists_unique_originalCurrent_correctedModel_recovery hh T hc h11 hT
  obtain ⟨P, _hP, huniq⟩ :=
    exists_unique_compact_current_analyticModification_pullback hs T hc h11 hT
  have he : S = R := (huniq S ⟨hcS, h11S, hS, hreadS⟩).trans
    (huniq R ⟨hcR, h11R, hR, fun θ v hv hread => by
      simpa only [analyticModificationThetaCurrent, thetaPotentialModificationCurrent]
        using hreadR θ v hv hread⟩).symm
  subst S
  exact hvalue.trans hvector

/-- Existing birational readback internally produces the original pullback
current and its EVERY-presentation specification; the first theorem reads its value. -/
theorem exists_smoothModelCurrentFlagChoice_original_pullback {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z]
    {π : Z → F.carrier} {h : W.carrier → Z}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hπh : IsFlagLifting F W (π ∘ h))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    letI : CompactSpace Z :=
      AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hπ
    ∃ (Tπ : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m))),
      ∃ (hcπ : Tπ.IsClosed (canonicalBasis (m + 1)))
        (h11π : Tπ.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hTπ : IsFullPositive Tπ),
        (∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : F.carrier → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          Tπ = analyticModificationThetaCurrent hπ θ v hv) ∧
        smoothModelCurrentFlagChoice hπ hh hπh Tπ hcπ h11π hTπ =
          (fun i => (currentFlagValuation F T hc h11 hT i : ℝ)) := by
  let : CompactSpace Z :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hπ
  obtain ⟨Tπ, hcπ, h11π, hTπ, hall, hvalue⟩ :=
    exists_smoothModelCurrentFlagChoice_birational
      (isAnalyticModification_identity (n := m + 1) (X := F.carrier))
      hπ hh hπh T hc h11 hT
  refine ⟨Tπ, hcπ, h11π, hTπ, hall, ?_⟩
  exact hvalue.trans (smoothModelCurrentFlagChoice_original_eq hπh T hc h11 hT)

end SGPT.Okounkov
