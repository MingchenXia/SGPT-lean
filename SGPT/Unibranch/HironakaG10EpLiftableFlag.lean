import SGPT.Unibranch.HironakaG10EpChowBridge
import SGPT.Unibranch.HironakaG10EpBimeromorphicCancel
import SGPT.Okounkov.FlagLiftingExistence

/-!
# The book's `thm:liftableflag` for reduced sources, and the initial Chow model of `def:modelvalcurr`

Run 0081 lane G10EP (SGPT consumer contract G10-05-01.sgpt).  Blueprint:
`hironaka-g10ep-chow-bridge.tex`.

Book (chapter Okounkov, `thm:liftableflag`): let `X` be a connected compact Kähler manifold with a
smooth flag `Y•` and `π : Z → X` a proper bimeromorphic morphism from a REDUCED complex space `Z`;
then there is a modification `W → X` dominating `Z → X` such that `Y•` lifts to `W`.  The book's
first step is "by Hironaka's Chow lemma we may assume that `π` is a modification"; the existing
SGPT formalization (`SGPT.Okounkov.exists_flagLifting_dominating_finiteNativeModification`) proves
the theorem after that step, for a finite blowup sequence of manifolds.  This file supplies the
first step from the general Chow lemma `HironakaChowLemmaGeneral` (goal G10), in the native
category of reduced complex spaces:

* `exists_flagLifting_of_isDominatedByModification` — from any domination of `π` by a finite
  smooth-centre modification (unconditional);
* `exists_flagLifting_dominating` — `thm:liftableflag` for reduced `Z`, from
  `HironakaChowLemmaGeneral`;
* `exists_flagLifting_dominating_of_flattening` — the same from Hironaka's flattening theorem
  alone (the base `X` is smooth, so no resolution is needed);
* `exists_flagModel_of_isProperBimeromorphic` — the model `h : Ẑ → Z` chosen in the book's
  `def:modelvalcurr`: a proper bimeromorphic morphism from a compact connected Kähler manifold
  `Ẑ` (a blowup of `X`, with its Kähler form) to which `Y•` lifts with respect to `π ∘ h`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10EpLiftableFlag

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending HironakaChowLemma
  SourceReducedComplexSpace OriginalNativeModification HironakaG10ChowFlatteningReduction
  HironakaG10GenStatement HironakaG10GenChow HironakaG10EpChowBridge
  HironakaG10EpBimeromorphicCancel SGPT.Okounkov

noncomputable section

variable {n : ℕ}

/-- **Flag lifting after a Chow domination** (unconditional).  If `π : Z ⟶ X` (`X` the original
compact connected Kähler manifold with its smooth flag, `Z` any reduced complex space) is
dominated by a finite composition of smooth-centre blowups, then there are a finite blowup
sequence `p : W → X` of manifolds, a lifting of the flag to `W` with respect to `p`, and a morphism
`G : W ⟶ Z` with `G ≫ π = p`. -/
theorem exists_flagLifting_of_isDominatedByModification (F : OriginalFlagGeometry.{0} n)
    {Z : SourceReducedComplexSpace} {π : Z ⟶ wholeModel (n := n) F.carrier}
    (hπ : IsDominatedByModification π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (p : W.carrier → F.carrier)
      (hp : IsBlowupSequence n F.carrier W.carrier p),
      IsFlagLifting F W p ∧
        ∃ G : wholeModel (n := n) W.carrier ⟶ Z, G ≫ π = nativeMorphism hp.contMDiff := by
  obtain ⟨V, tV, cV, mV, ρ, hρ, G, hG⟩ :=
    exists_blowupSequence_domination_of_isDominatedByModification hπ
  let := tV
  let := cV
  let := mV
  obtain ⟨W, q, hq, hρq, hlift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F V ρ hρ
  refine ⟨W, ρ ∘ q, hρq, hlift, nativeMorphism hq.contMDiff ≫ G, ?_⟩
  rw [Category.assoc, hG]
  exact morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)

/-- The whole model of a compact manifold is compact. -/
theorem compactSpace_wholeModel (F : OriginalFlagGeometry.{0} n) :
    CompactSpace (wholeModel (n := n) F.carrier).obj.left :=
  (Homeomorph.Set.univ F.carrier).symm.compactSpace

/-- **`thm:liftableflag` for a reduced source, from the general Chow lemma.**  For every proper
bimeromorphic morphism `π : Z ⟶ X` from a reduced complex space to the original compact connected
Kähler manifold `X` with its smooth flag, there is a finite blowup sequence `p : W → X`
dominating `π` (`G ≫ π = p`) such that the flag lifts to `W`. -/
theorem exists_flagLifting_dominating (H : HironakaChowLemmaGeneral)
    (F : OriginalFlagGeometry.{0} n) {Z : SourceReducedComplexSpace}
    (π : Z ⟶ wholeModel (n := n) F.carrier) (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (p : W.carrier → F.carrier)
      (hp : IsBlowupSequence n F.carrier W.carrier p),
      IsFlagLifting F W p ∧
        ∃ G : wholeModel (n := n) W.carrier ⟶ Z, G ≫ π = nativeMorphism hp.contMDiff :=
  exists_flagLifting_of_isDominatedByModification F (H _ _ π (compactSpace_wholeModel F) hπ)

/-- **`thm:liftableflag` for a reduced source, from Hironaka's flattening theorem alone** (the
base is smooth, so G11 is not needed). -/
theorem exists_flagLifting_dominating_of_flattening (H₀ : HironakaFlattening)
    (F : OriginalFlagGeometry.{0} n) {Z : SourceReducedComplexSpace}
    (π : Z ⟶ wholeModel (n := n) F.carrier) (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (p : W.carrier → F.carrier)
      (hp : IsBlowupSequence n F.carrier W.carrier p),
      IsFlagLifting F W p ∧
        ∃ G : wholeModel (n := n) W.carrier ⟶ Z, G ≫ π = nativeMorphism hp.contMDiff :=
  exists_flagLifting_of_isDominatedByModification F
    (isDominatedByModification_of_isSmooth H₀ π (compactSpace_wholeModel F)
      (isSmooth_wholeModel (n := n) (M := F.carrier)) hπ)

/-- **The initial Chow model of `def:modelvalcurr`**, from the general Chow lemma.  For every
proper bimeromorphic `π : Z ⟶ X` from a reduced complex space there is a proper bimeromorphic
`h : Ẑ ⟶ Z` from (the whole model of) a compact connected Kähler manifold `Ẑ = W.carrier`, a
finite blowup sequence of `X`, such that the flag lifts to `Ẑ` with respect to `π ∘ h`. -/
theorem exists_flagModel_of_isProperBimeromorphic (H : HironakaChowLemmaGeneral)
    (F : OriginalFlagGeometry.{0} n) {Z : SourceReducedComplexSpace}
    (π : Z ⟶ wholeModel (n := n) F.carrier) (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (h : wholeModel (n := n) W.carrier ⟶ Z),
      IsProperBimeromorphic h ∧
        ∃ (p : W.carrier → F.carrier) (hp : IsBlowupSequence n F.carrier W.carrier p),
          IsFlagLifting F W p ∧ h ≫ π = nativeMorphism hp.contMDiff := by
  obtain ⟨W, p, hp, hlift, G, hG⟩ := exists_flagLifting_dominating H F π hπ
  refine ⟨W, G, isProperBimeromorphic_of_comp G hπ ?_ hG, p, hp, hlift, hG⟩
  exact nativeMorphism_isProperBimeromorphic
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hp)

end

end SGPT.Unibranch.HironakaG10EpLiftableFlag
