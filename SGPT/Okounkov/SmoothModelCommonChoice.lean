import SGPT.Okounkov.AnalyticModificationCurrent
import SGPT.Okounkov.SmoothModelCurrentValuation

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

/-- A given literal common square and original composite liftings manufacture
every intermediate modification and flag lifting, including dimension zero. -/
theorem commonFlagModel_intermediate_liftings {n : ℕ}
    {F W₀ W₁ V : OriginalFlagGeometry.{u} n} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]
    {π : Z → F.carrier} {h₀ : W₀.carrier → Z} {h₁ : W₁.carrier → Z}
    {q₀ : V.carrier → W₀.carrier} {q₁ : V.carrier → W₁.carrier}
    (hπ : IsAnalyticModification (n := n) π)
    (hh₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h₀)
    (hh₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h₁)
    (hq₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q₀)
    (hq₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q₁)
    (hπ₀ : IsFlagLifting F W₀ (π ∘ h₀))
    (hπ₁ : IsFlagLifting F W₁ (π ∘ h₁))
    (hρ : IsFlagLifting F V ((π ∘ h₀) ∘ q₀))
    (hcomm : h₀ ∘ q₀ = h₁ ∘ q₁) :
    IsAnalyticModification (n := n) h₀ ∧
    IsAnalyticModification (n := n) h₁ ∧
    IsFlagLifting F V ((π ∘ h₁) ∘ q₁) ∧
    IsFlagLifting W₀ V q₀ ∧ IsFlagLifting W₁ V q₁ := by
  have hf₀ := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ hπ₀.1 hh₀ rfl
  have hf₁ := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ hπ₁.1 hh₁ rfl
  have he : (π ∘ h₀) ∘ q₀ = (π ∘ h₁) ∘ q₁ := by
    funext z
    exact congrArg π (congrFun hcomm z)
  have hρ₁ : IsFlagLifting F V ((π ∘ h₁) ∘ q₁) := he ▸ hρ
  have hg₀ := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ₀.1 hρ.1 hq₀ rfl
  have hg₁ := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ₁.1 hρ₁.1 hq₁ rfl
  exact ⟨hf₀, hf₁, hρ₁, hπ₀.of_comp hρ hg₀, hπ₁.of_comp hρ₁ hg₁⟩

/-- An arbitrary original current on a compact smooth model internally
produces both pullbacks, one SAME common whole current, and equal signed
corrected vectors. The common geometric square is given, not its existence. -/
theorem exists_compact_current_commonFlagModel_choice {m : ℕ}
    {F W₀ W₁ V : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
    [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    {π : Z → F.carrier} {h₀ : W₀.carrier → Z} {h₁ : W₁.carrier → Z}
    {q₀ : V.carrier → W₀.carrier} {q₁ : V.carrier → W₁.carrier}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hh₀ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h₀)
    (hh₁ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h₁)
    (hq₀ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ q₀)
    (hq₁ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ q₁)
    (hπ₀ : IsFlagLifting F W₀ (π ∘ h₀))
    (hπ₁ : IsFlagLifting F W₁ (π ∘ h₁))
    (hρ : IsFlagLifting F V ((π ∘ h₀) ∘ q₀))
    (hcomm : h₀ ∘ q₀ = h₁ ∘ q₁)
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (hf₀ : IsAnalyticModification (n := m + 1) h₀)
      (hf₁ : IsAnalyticModification (n := m + 1) h₁)
      (hg₀ : IsFlagLifting W₀ V q₀) (hg₁ : IsFlagLifting W₁ V q₁)
      (R₀ : GlobalCurrent (m + 1) W₀.carrier (degreeTwo (Nat.succ_pos m)))
      (R₁ : GlobalCurrent (m + 1) W₁.carrier (degreeTwo (Nat.succ_pos m)))
      (Q : GlobalCurrent (m + 1) V.carrier (degreeTwo (Nat.succ_pos m))),
      ∃ (hc₀ : R₀.IsClosed (canonicalBasis (m + 1)))
        (h11₀ : R₀.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR₀ : IsFullPositive R₀)
        (hc₁ : R₁.IsClosed (canonicalBasis (m + 1)))
        (h11₁ : R₁.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR₁ : IsFullPositive R₁)
        (_hcQ : Q.IsClosed (canonicalBasis (m + 1)))
        (_h11Q : Q.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (_hQ : IsFullPositive Q),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          R₀ = analyticModificationThetaCurrent hf₀ θ v hv ∧
          R₁ = analyticModificationThetaCurrent hf₁ θ v hv) ∧
        (∀ (σ : ClosedRealOneOneForm (m + 1) W₀.carrier) (w : W₀.carrier → EReal)
          (hw : IsThetaPshPotential σ.val w), R₀ = thetaPotentialCurrent σ.val w hw →
          Q = thetaPotentialModificationCurrent hg₀ σ w hw) ∧
        (∀ (σ : ClosedRealOneOneForm (m + 1) W₁.carrier) (w : W₁.carrier → EReal)
          (hw : IsThetaPshPotential σ.val w), R₁ = thetaPotentialCurrent σ.val w hw →
          Q = thetaPotentialModificationCurrent hg₁ σ w hw) ∧
        correctedModelCurrentFlagValuation hπ₀ R₀ hc₀ h11₀ hR₀ =
          correctedModelCurrentFlagValuation hπ₁ R₁ hc₁ h11₁ hR₁ := by
  obtain ⟨hf₀, hf₁, hρ₁, hg₀, hg₁⟩ := commonFlagModel_intermediate_liftings
    hπ hh₀ hh₁ hq₀ hq₁ hπ₀ hπ₁ hρ hcomm
  obtain ⟨R₀, R₁, Q, hR₀, hR₁, hQ, hallT, hall₀, hall₁⟩ :=
    exists_compact_current_commonModification_pullbacks hf₀ hf₁ hg₀.1 hg₁.1 hcomm
      T hc h11 hT
  have hallQ₀ : ∀ (σ : ClosedRealOneOneForm (m + 1) W₀.carrier)
      (w : W₀.carrier → EReal) (hw : IsThetaPshPotential σ.val w),
      R₀ = thetaPotentialCurrent σ.val w hw →
      Q = thetaPotentialModificationCurrent hg₀ σ w hw := hall₀
  have hallQ₁ : ∀ (σ : ClosedRealOneOneForm (m + 1) W₁.carrier)
      (w : W₁.carrier → EReal) (hw : IsThetaPshPotential σ.val w),
      R₁ = thetaPotentialCurrent σ.val w hw →
      Q = thetaPotentialModificationCurrent hg₁ σ w hw := hall₁
  have hv₀ : correctedModelCurrentFlagValuation hρ Q hQ.1 hQ.2.1 hQ.2.2 =
      correctedModelCurrentFlagValuation hπ₀ R₀ hR₀.1 hR₀.2.1 hR₀.2.2 := by
    obtain ⟨S, ⟨hcS, h11S, hS, hallS, hvector⟩, _huniqS⟩ :=
      exists_unique_correctedModelCurrentFlagValuation_pullback hπ₀ hρ hg₀.1
        R₀ hR₀.1 hR₀.2.1 hR₀.2.2
    obtain ⟨P, _hP, huniqP⟩ := exists_unique_original_current_modification_pullback
      hg₀ R₀ hR₀.1 hR₀.2.1 hR₀.2.2
    have he : Q = S := (huniqP Q ⟨hQ.1, hQ.2.1, hQ.2.2, hallQ₀⟩).trans
      (huniqP S ⟨hcS, h11S, hS, hallS⟩).symm
    subst S
    exact hvector
  have hv₁ : correctedModelCurrentFlagValuation hρ₁ Q hQ.1 hQ.2.1 hQ.2.2 =
      correctedModelCurrentFlagValuation hπ₁ R₁ hR₁.1 hR₁.2.1 hR₁.2.2 := by
    obtain ⟨S, ⟨hcS, h11S, hS, hallS, hvector⟩, _huniqS⟩ :=
      exists_unique_correctedModelCurrentFlagValuation_pullback hπ₁ hρ₁ hg₁.1
        R₁ hR₁.1 hR₁.2.1 hR₁.2.2
    obtain ⟨P, _hP, huniqP⟩ := exists_unique_original_current_modification_pullback
      hg₁ R₁ hR₁.1 hR₁.2.1 hR₁.2.2
    have he : Q = S := (huniqP Q ⟨hQ.1, hQ.2.1, hQ.2.2, hallQ₁⟩).trans
      (huniqP S ⟨hcS, h11S, hS, hallS⟩).symm
    subst S
    exact hvector
  have he : (⟨(π ∘ h₀) ∘ q₀, hρ⟩ : {f // IsFlagLifting F V f}) =
      ⟨(π ∘ h₁) ∘ q₁, hρ₁⟩ := by
    apply Subtype.ext
    funext z
    exact congrArg π (congrFun hcomm z)
  have hvalue := congrArg (fun f : {f // IsFlagLifting F V f} =>
    correctedModelCurrentFlagValuation f.property Q hQ.1 hQ.2.1 hQ.2.2) he
  refine ⟨hf₀, hf₁, hg₀, hg₁, R₀, R₁, Q, hR₀.1, hR₀.2.1, hR₀.2.2,
    hR₁.1, hR₁.2.1, hR₁.2.2, hQ.1, hQ.2.1, hQ.2.2, ?_, hallQ₀, hallQ₁,
    hv₀.symm.trans (hvalue.trans hv₁)⟩
  intro θ v hv hread
  exact ⟨(hallT θ v hv hread).1, (hallT θ v hv hread).2.1⟩

end SGPT.Okounkov
