import SGPT.Okounkov.SmoothModelValuationChoice

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy GlobalCurrents CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent

variable {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {Z Z' : Type u}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z] [CompactSpace Z]
  [TopologicalSpace Z'] [ChartedSpace (ComplexModel (m + 1)) Z']
  [IsComplexManifold (m + 1) Z']

/-- Properness supplies compactness upstairs; the public factor theorem and
the identical genuine common-current branches produce every literal readback. -/
theorem exists_compact_current_smoothModel_birational_readbacks
    {π : Z → F.carrier} {p : Z' → Z} {h : W.carrier → Z'}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hp : IsAnalyticModification (n := m + 1) p)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hπph : IsFlagLifting F W ((π ∘ p) ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (hhmod : IsAnalyticModification (n := m + 1) h)
      (hph : IsAnalyticModification (n := m + 1) (p ∘ h))
      (T' : GlobalCurrent (m + 1) Z' (degreeTwo (Nat.succ_pos m)))
      (Q : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m))),
      (T'.IsClosed (canonicalBasis (m + 1)) ∧
        T'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive T') ∧
      (Q.IsClosed (canonicalBasis (m + 1)) ∧
        Q.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive Q) ∧
      (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
        (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
        T' = analyticModificationThetaCurrent hp θ v hv ∧
        Q = analyticModificationThetaCurrent hph θ v hv) ∧
      ∀ (σ : ClosedRealOneOneForm (m + 1) Z') (w : Z' → EReal)
        (hw : IsThetaPshPotential σ.val w), T' = thetaPotentialCurrent σ.val w hw →
        Q = analyticModificationThetaCurrent hhmod σ w hw := by
  let : CompactSpace Z' :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hp
  have hπp := AnalyticModificationComposition.isAnalyticModification_comp hπ hp
  have hhmod := PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hπp hπph.1 hh rfl
  have hph := AnalyticModificationComposition.isAnalyticModification_comp hp hhmod
  obtain ⟨T', _T'', Q, hT', _hT'', hQ, hallT, hallQ, _hallQ'⟩ :=
    exists_compact_current_commonModification_pullbacks hp hp hhmod hhmod rfl T hc h11 hT
  exact ⟨hhmod, hph, T', Q, hT', hQ, fun θ v hv hread =>
    ⟨(hallT θ v hv hread).1, (hallT θ v hv hread).2.2⟩, hallQ⟩

/-- The actual intermediate current is manufactured internally; whole-current
uniqueness identifies the independently chosen values of the literal function. -/
theorem exists_smoothModelCurrentFlagChoice_birational
    {π : Z → F.carrier} {p : Z' → Z} {h : W.carrier → Z'}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hp : IsAnalyticModification (n := m + 1) p)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ h)
    (hπph : IsFlagLifting F W ((π ∘ p) ∘ h))
    (T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    letI : CompactSpace Z' :=
      AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hp
    ∃ (T' : GlobalCurrent (m + 1) Z' (degreeTwo (Nat.succ_pos m))),
      ∃ (hc' : T'.IsClosed (canonicalBasis (m + 1)))
        (h11' : T'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hT' : IsFullPositive T'),
        (∀ (θ : ClosedRealOneOneForm (m + 1) Z) (v : Z → EReal)
          (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
          T' = analyticModificationThetaCurrent hp θ v hv) ∧
        smoothModelCurrentFlagChoice
          (AnalyticModificationComposition.isAnalyticModification_comp hπ hp)
          hh hπph T' hc' h11' hT' =
        smoothModelCurrentFlagChoice hπ (hp.1.comp hh) hπph T hc h11 hT := by
  let : CompactSpace Z' :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hp
  obtain ⟨hhmod, hph, T', Q, hT', hQ, hallT, hallQ⟩ :=
    exists_compact_current_smoothModel_birational_readbacks hπ hp hh hπph T hc h11 hT
  obtain ⟨hs₀, S₀, hcS₀, h11S₀, hS₀, hreadS₀, hvalue₀⟩ :=
    smoothModelCurrentFlagChoice_spec hπ (hp.1.comp hh) hπph T hc h11 hT
  obtain ⟨hs₁, S₁, hcS₁, h11S₁, hS₁, hreadS₁, hvalue₁⟩ :=
    smoothModelCurrentFlagChoice_spec
      (AnalyticModificationComposition.isAnalyticModification_comp hπ hp)
      hh hπph T' hT'.1 hT'.2.1 hT'.2.2
  obtain ⟨P₀, _hP₀, huniq₀⟩ :=
    exists_unique_compact_current_analyticModification_pullback hph T hc h11 hT
  obtain ⟨P₁, _hP₁, huniq₁⟩ :=
    exists_unique_compact_current_analyticModification_pullback hhmod T' hT'.1 hT'.2.1 hT'.2.2
  have he₀ : S₀ = Q := (huniq₀ S₀ ⟨hcS₀, h11S₀, hS₀, hreadS₀⟩).trans
    (huniq₀ Q ⟨hQ.1, hQ.2.1, hQ.2.2, fun θ v hv hread =>
      (hallT θ v hv hread).2⟩).symm
  have he₁ : S₁ = Q := (huniq₁ S₁ ⟨hcS₁, h11S₁, hS₁, hreadS₁⟩).trans
    (huniq₁ Q ⟨hQ.1, hQ.2.1, hQ.2.2, hallQ⟩).symm
  subst S₀
  subst S₁
  exact ⟨T', hT'.1, hT'.2.1, hT'.2.2,
    fun θ v hv hread => (hallT θ v hv hread).1,
    hvalue₁.trans hvalue₀.symm⟩

end SGPT.Okounkov
