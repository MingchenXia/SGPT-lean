import SGPT.GAGA.ChowBlEmbed
import SGPT.Okounkov.OkoLelongMin
import SGPT.NAPotential.DivDict2Blowup
import SGPT.Foundations.Analysis.Pending.ResolvedNefPart

/-!
# Partial Okounkov bodies on blow-up towers determine the `𝓘`-order

Source `chapter_Okounkov.tex`, `cor:Deltacontimplyvarphi`: *let `φ, ψ ∈ PSH(X, θ)_{>0}`; if
`Δ_{W•}(π^*θ, π^*φ) ⊆ Δ_{W•}(π^*θ, π^*ψ)` for all modifications `π : Y → X` and all admissible
flags `W•` on `Y`, then `φ ⪯_𝓘 ψ`.*  Lane CHOW-BLOWUP, blueprint `claude-chow-blowup.tex`, node
`claude-chow-blowup:delta-cont`.

Formal statement (`sourceIOrder_of_generalPartialBody_subset`), transcendental form: `X` is a
compact connected Kähler manifold of dimension `m + 1` with a holomorphic embedding into some
`ℙᴺ` (a projective manifold), `θ` a closed real `(1,1)`-form, `φ, ψ` `θ`-psh.  The bodies are the
partial Okounkov bodies `Δ_{W•}(π^*θ + dd^c π^*φ)` of `def:generalPOB`
(`SGPT.Okounkov.PartialBody.generalPartialBody`), which `cor:transalgPOB` (verified) identifies
with the algebraic bodies on projective `Y`.  The hypothesis is required only for the modifications
that are finite sequences of blow-ups with smooth centres and only for smooth flags (a weaker
hypothesis than the book's, so a stronger statement); no positivity of the masses is needed.

Proof (the book's): every prime divisor `E` on a blow-up tower `Y` is the first member of a smooth
flag on `Y`, because `Y` is projective (`SGPT.GAGA.ChowBl.exists_isSmoothFlag_one_eq_of_isBlowupSequence`,
lane CHOW-BLOWUP: Chow's theorem and the projectivity of blow-ups); by `thm:nuOk` the inclusion gives
`ν(π^*ψ, E) ≤ ν(π^*φ, E)` (`SGPT.Okounkov.OkoLelong.sourceGenericLelongNumber_le_of_generalPartialBody_subset`);
the `𝓘`-order is detected by prime divisors on blow-up towers (`prop:Iequivchar2`,
`SGPT.NAPotential.DivDict2.sourceIOrder_of_blowupPresentationComparison`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ChowBl

universe u

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Projective
open scoped ENNReal

variable {m N : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- A `θ`-psh potential (for a native closed form `θ`) is quasi-psh in the atlas sense. -/
theorem isQPSH_of_isThetaPshPotential {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) : (ofFixedModel (m + 1) X).IsQPSH u := by
  refine ⟨nativeClosedFormToAtlas θ, (isThetaPSH_iff_nativeThetaPotential _ u).mpr ?_⟩
  have : atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
    rcases θ with ⟨θ, hθ⟩
    cases θ
    rfl
  rw [this]
  exact hu

/-- The reader of a presentation is the generic Lelong number along its hypersurface. -/
theorem presentationReader_eq_sourceGenericLelongNumber (u : X → EReal)
    (p : PrimePresentation (m + 1) X) {A : Set p.model} (hA : A = p.divisor) :
    presentationReader u p = sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : A → p.model) (fun y => u (p.projection y)) := by
  subst hA
  simp only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    sourceGenericLelongNumber, Function.comp_def]
  rw [iInf_subtype']

/-- **`cor:Deltacontimplyvarphi`, transcendental form, for projective `X`.**  If the partial
Okounkov bodies satisfy `Δ_{W•}(π^*θ, π^*φ) ⊆ Δ_{W•}(π^*θ, π^*ψ)` for every finite sequence of
blow-ups with smooth centres `π : Y → X` and every smooth flag `W•` on `Y` (with any Kähler
background, on which the bodies do not depend), then `φ ⪯_𝓘 ψ`. -/
theorem sourceIOrder_of_generalPartialBody_subset [CompactSpace X] [ConnectedSpace X]
    {Ψ : X → ComplexProjectiveSpace N} (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := m + 1) Ψ)
    (hK : Nonempty (KahlerBackground (m + 1) X)) (θ : ClosedRealOneOneForm (m + 1) X)
    {φ ψ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (hsub : ∀ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → X)
      (_ : IsBlowupSequence (m + 1) X W.carrier π) (hmod : IsAnalyticModification (n := m + 1) π),
      PartialBody.generalPartialBody W (ClosedRealOneOneForm.pullback hmod.1 θ)
          (fun y => φ (π y)) ⊆
        PartialBody.generalPartialBody W (ClosedRealOneOneForm.pullback hmod.1 θ)
          (fun y => ψ (π y))) :
    sourceIOrder (ofFixedModel (m + 1) X) φ ψ := by
  refine SGPT.NAPotential.DivDict2.sourceIOrder_of_blowupPresentationComparison
    (isQPSH_of_isThetaPshPotential hφ) (isQPSH_of_isThetaPshPotential hψ) fun p hp => ?_
  have hseq : IsBlowupSequence (m + 1) X p.model p.projection := hp
  obtain ⟨hc, hKY⟩ := ResolvedNefPart.compactSpace_and_kahler_of_isBlowupSequence hK hseq
  have := hc
  have : ConnectedSpace p.model :=
    BlowupConnected.connectedSpace_of_isBlowupSequence p.projection hseq
  have hdim : p.divisorDimension = m := by have := p.codimension_one; omega
  have hW : IsClosedConnectedSubmanifold (m + 1) p.divisor (m + 1 - 1) := by
    have h := p.smooth
    rw [hdim] at h
    simpa using h
  obtain ⟨Yfl, hYfl, hY1⟩ :=
    SGPT.GAGA.ChowBl.exists_isSmoothFlag_one_eq_of_isBlowupSequence hΨ hseq (by omega) hW
  let F : OriginalFlagGeometry.{u} (m + 1) := OriginalFlagGeometry.ofOriginal hKY.some Yfl hYfl
  have key := OkoLelong.sourceGenericLelongNumber_le_of_generalPartialBody_subset F
    (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      p.modification θ hφ)
    (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      p.modification θ hψ)
    (hsub F p.projection hseq p.modification)
  have hflag : F.flag (1 : Fin (m + 2)) = p.divisor := by
    rw [← hY1]
    show Yfl 1 = Yfl ⟨1, _⟩
    congr 1
  rw [presentationReader_eq_sourceGenericLelongNumber ψ p hflag,
    presentationReader_eq_sourceGenericLelongNumber φ p hflag]
  exact key

end SGPT.Okounkov.ChowBl
