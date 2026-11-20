import SGPT.Okounkov.OCLiftableFlag
import SGPT.Unibranch.HironakaG10Complete
import SGPT.Unibranch.HironakaG10GenBlowupBridge
import SGPT.Unibranch.HironakaG10EpBimeromorphicCancel

/-!
# `thm:liftableflag`, unconditionally

Source `thm:liftableflag` (`chapter_Okounkov.tex`, line 386): *let `π : Z → X` be a proper
bimeromorphic morphism from a reduced complex space `Z`. Then there is a modification `W → X`
dominating `Z → X` such that `Y•` admits a lifting to `W`.* Here `X` is the compact connected
Kähler manifold of dimension `n` with its smooth flag `Y•` (`SGPT.Okounkov.OriginalFlagGeometry`),
"modification" is a finite composition of blowups with smooth centres (`def:modif`), and a lifting
(`def:lifting`) is a smooth flag `W•` on the Kähler manifold `W` with `σ(W_i) ⊆ Y_i` and
`W_i → Y_i` bimeromorphic for every `i` (`SGPT.Okounkov.IsFlagLifting`).

Lane OC proved the theorem from Hironaka's Chow lemma for compact complex manifolds
(`OCLiftableFlag.exists_flagLifting_dominating_reducedModel_of_chow`, hypothesis
`HironakaChowLemmaManifold.{0}`). Goal G10 proved that lemma
(`HironakaG10Complete.hironakaChowLemmaManifold : HironakaChowLemmaManifold.{0}`, the same universe),
so the theorem holds without hypothesis:

* `exists_flagLifting_dominating` — `thm:liftableflag`;
* `exists_flagLifting_dominating_modification` — the same, recording in addition that the native
  morphism `W → X` is a modification in the sense of the complex-space formalization of `def:modif`
  (`SmoothCentreModification.IsModification`) and that the dominating morphism `g : W → Z` is
  itself proper bimeromorphic.

Blueprint: `blueprint/src/ch.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.CHLiftableFlag

open Set CategoryTheory
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification

/-- **`thm:liftableflag`.** Let `X` (`F.carrier`) be the compact connected Kähler manifold with its
smooth flag `Y•` (`F.flag`) and `π : Z ⟶ X` a proper bimeromorphic morphism from a reduced complex
space `Z`. Then there are a finite composition of blowups with smooth centres `σ : W → X`
(`IsBlowupSequence`, a modification of `X`, `def:modif`), a morphism of complex spaces
`g : W ⟶ Z` with `g ≫ π = σ` (`W` dominates `Z → X`), and the flag `Y•` admits a lifting `W•`
(`W.flag`) to the compact connected Kähler manifold `W` with respect to `σ` (`def:lifting`). -/
theorem exists_flagLifting_dominating {n : ℕ} (F : OriginalFlagGeometry.{0} n)
    (Z : SourceReducedComplexSpace) (π : Z ⟶ wholeModel (n := n) F.carrier)
    (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (σ : W.carrier → F.carrier)
      (hσ : IsBlowupSequence n F.carrier W.carrier σ)
      (g : wholeModel (n := n) W.carrier ⟶ Z),
      g ≫ π = nativeMorphism hσ.contMDiff ∧ IsFlagLifting F W σ :=
  OCLiftableFlag.exists_flagLifting_dominating_reducedModel_of_chow
    HironakaG10Complete.hironakaChowLemmaManifold F Z π hπ

/-- **`thm:liftableflag`, with the modification read in the category of complex spaces.** In the
conclusion of `exists_flagLifting_dominating`, the morphism of complex spaces `W ⟶ X` induced by
`σ` is a finite composition of smooth-centre blowups (`IsModification`, the complex-space form of
`def:modif`), and the dominating morphism `g : W ⟶ Z` is proper bimeromorphic. -/
theorem exists_flagLifting_dominating_modification {n : ℕ} (F : OriginalFlagGeometry.{0} n)
    (Z : SourceReducedComplexSpace) (π : Z ⟶ wholeModel (n := n) F.carrier)
    (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (σ : W.carrier → F.carrier)
      (hσ : IsBlowupSequence n F.carrier W.carrier σ)
      (g : wholeModel (n := n) W.carrier ⟶ Z),
      IsModification (nativeMorphism (n := n) (m := n) hσ.contMDiff) ∧
        g ≫ π = nativeMorphism hσ.contMDiff ∧ IsProperBimeromorphic g ∧ IsFlagLifting F W σ := by
  obtain ⟨W, σ, hσ, g, hg, hLift⟩ := exists_flagLifting_dominating F Z π hπ
  refine ⟨W, σ, hσ, g, HironakaG10GenBlowupBridge.isModification_nativeMorphism hσ, hg, ?_, hLift⟩
  exact HironakaG10EpBimeromorphicCancel.isProperBimeromorphic_of_comp g hπ
    (nativeMorphism_isProperBimeromorphic
      (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hσ)) hg

end SGPT.Okounkov.CHLiftableFlag
