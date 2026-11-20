import SGPT.Okounkov.SmoothModelCommonChoice

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

variable {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {Z : Type u}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z] [CompactSpace Z]

/-- Literal smooth-model choice in the original signed definition: choose the
actual unique whole pullback and apply the SAME actual real correction inverse. -/
def smoothModelCurrentFlagChoice {π : Z → F.carrier} {h : W.carrier → Z}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hπh : IsFlagLifting F W (π ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ :=
  let hf := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ hπh.1 hh rfl
  let result := exists_unique_compact_current_analyticModification_pullback hf T hc h11 hT
  let R := Classical.choose result
  let hR := (Classical.choose_spec result).1
  correctedModelCurrentFlagValuation hπh R hR.1 hR.2.1 hR.2.2.1

/-- The definition's genuine unique-current producer supplies its whole current,
all original properties, EVERY representation readback and literal signed value. -/
theorem smoothModelCurrentFlagChoice_spec {π : Z → F.carrier} {h : W.carrier → Z}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hπh : IsFlagLifting F W (π ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (hf : IsAnalyticModification (n := m + 1) h)
      (R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m))),
      ∃ (hcR : R.IsClosed (canonicalBasis (m + 1)))
        (h11R : R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hR : IsFullPositive R),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          R = analyticModificationThetaCurrent hf θ v hv) ∧
        smoothModelCurrentFlagChoice hπ hh hπh T hc h11 hT =
          correctedModelCurrentFlagValuation hπh R hcR h11R hR := by
  let hf := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπ hπh.1 hh rfl
  let result := exists_unique_compact_current_analyticModification_pullback hf T hc h11 hT
  let R := Classical.choose result
  have hR := (Classical.choose_spec result).1
  exact ⟨hf, R, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2, rfl⟩

/-- The actual defined signed functions agree through a given common smooth
square. Whole-current uniqueness identifies the independently selected currents. -/
theorem smoothModelCurrentFlagChoice_eq_common
    {W₀ W₁ V : OriginalFlagGeometry.{u} (m + 1)}
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
    smoothModelCurrentFlagChoice hπ hh₀ hπ₀ T hc h11 hT =
      smoothModelCurrentFlagChoice hπ hh₁ hπ₁ T hc h11 hT := by
  obtain ⟨hs₀, S₀, hcS₀, h11S₀, hS₀, hreadS₀, hvalue₀⟩ :=
    smoothModelCurrentFlagChoice_spec hπ hh₀ hπ₀ T hc h11 hT
  obtain ⟨hs₁, S₁, hcS₁, h11S₁, hS₁, hreadS₁, hvalue₁⟩ :=
    smoothModelCurrentFlagChoice_spec hπ hh₁ hπ₁ T hc h11 hT
  obtain ⟨_hf₀, _hf₁, _hg₀, _hg₁, R₀, R₁, _Q,
      hc₀, h11₀, hR₀, hc₁, h11₁, hR₁, _hcQ, _h11Q, _hQ,
      hallT, _hallQ₀, _hallQ₁, hvector⟩ :=
    exists_compact_current_commonFlagModel_choice hπ hh₀ hh₁ hq₀ hq₁
      hπ₀ hπ₁ hρ hcomm T hc h11 hT
  obtain ⟨P₀, _hP₀, huniq₀⟩ :=
    exists_unique_compact_current_analyticModification_pullback hs₀ T hc h11 hT
  obtain ⟨P₁, _hP₁, huniq₁⟩ :=
    exists_unique_compact_current_analyticModification_pullback hs₁ T hc h11 hT
  have he₀ : R₀ = S₀ := (huniq₀ R₀ ⟨hc₀, h11₀, hR₀, fun θ v hv hread =>
    (hallT θ v hv hread).1⟩).trans
      (huniq₀ S₀ ⟨hcS₀, h11S₀, hS₀, hreadS₀⟩).symm
  have he₁ : R₁ = S₁ := (huniq₁ R₁ ⟨hc₁, h11₁, hR₁, fun θ v hv hread =>
    (hallT θ v hv hread).2⟩).trans
      (huniq₁ S₁ ⟨hcS₁, h11S₁, hS₁, hreadS₁⟩).symm
  subst R₀
  subst R₁
  exact hvalue₀.trans (hvector.trans hvalue₁.symm)

end SGPT.Okounkov
