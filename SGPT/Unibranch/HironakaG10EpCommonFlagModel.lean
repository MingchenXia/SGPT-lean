import SGPT.Unibranch.HironakaG10EpLiftableFlag
import SGPT.Unibranch.OriginalCommonResolutionGeneral

/-!
# Common adapted flag models over a reduced space (`lma:modelvalcurrbir`), from the general Chow lemma

Run 0081 lane G10EP (SGPT consumer contract, item G10-05-01.sgpt.c).  Blueprint:
`hironaka-g10ep-chow-bridge.tex`.

Book (chapter Okounkov, proof of `lma:modelvalcurrbir`): for two models `h_i : Ẑ_i → Z` of the
normal compact Kähler space `Z` over the original Kähler manifold `X` (with its smooth flag `Y•`),
"choose a common modification over `Z`, `q_i : U → Ẑ_i`, such that `Y•` admits a lifting to `U`".
This file constructs such a `U` from the general Chow lemma, for an arbitrary reduced complex space
`Z` and arbitrary smooth models `Y_i → Z` (`exists_common_flagModel`).  The construction refines a
Chow model of `π` twice: a common smooth model over `Z` (unconditional, G11) followed by Chow over
the MANIFOLD base of the current flag model, and the flag lifting of
`SGPT.Okounkov.exists_flagLifting_dominating_finiteNativeModification`.  Proper bimeromorphicity of
every map to `Z` and to the `Y_i` comes from the cancellation lemma
`HironakaG10EpBimeromorphicCancel.isProperBimeromorphic_of_comp`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10EpCommonFlagModel

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending HironakaChowLemma
  SourceReducedComplexSpace OriginalNativeModification
  HironakaG10GenStatement HironakaG10EpChowBridge HironakaG10EpBimeromorphicCancel
  HironakaG10EpLiftableFlag SGPT.Okounkov

noncomputable section

variable {n : ℕ}

/-- A blowup sequence of the original flag manifold gives a proper bimeromorphic native map. -/
theorem isProperBimeromorphic_nativeMorphism_of_isBlowupSequence (F : OriginalFlagGeometry.{0} n)
    {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W]
    {p : W → F.carrier} (hp : IsBlowupSequence n F.carrier W p) :
    IsProperBimeromorphic (nativeMorphism hp.contMDiff) :=
  nativeMorphism_isProperBimeromorphic
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hp)

/-- The source of a proper morphism to the original flag manifold is compact. -/
theorem compactSpace_of_isProperBimeromorphic (F : OriginalFlagGeometry.{0} n)
    {Z : SourceReducedComplexSpace} {π : Z ⟶ wholeModel (n := n) F.carrier}
    (hπ : IsProperBimeromorphic π) : CompactSpace Z.obj.left := by
  have := compactSpace_wholeModel F
  have hc : IsCompact (univ : Set Z.obj.left) := by
    simpa only [preimage_univ] using hπ.1.isCompact_preimage
      (isCompact_univ : IsCompact (univ : Set (wholeModel (n := n) F.carrier).obj.left))
  exact isCompact_univ_iff.mp hc

/-- **One refinement step.**  Let `W → X` be a blowup sequence with a lifted flag and a morphism
`G : W ⟶ Z` over `X`, and `h : Y ⟶ Z` a proper bimeromorphic morphism from a smooth space.  Then a
further blowup sequence `r : V → W`, still with a lifted flag, carries a morphism `K : V ⟶ Y` with
`K ≫ h = r ≫ G`. -/
theorem exists_refinement (H : HironakaChowLemmaGeneral) (F : OriginalFlagGeometry.{0} n)
    {Z Y : SourceReducedComplexSpace} (π : Z ⟶ wholeModel (n := n) F.carrier)
    (hπ : IsProperBimeromorphic π) (W : OriginalFlagGeometry.{0} n) {p : W.carrier → F.carrier}
    (hp : IsBlowupSequence n F.carrier W.carrier p) (G : wholeModel (n := n) W.carrier ⟶ Z)
    (hG : G ≫ π = nativeMorphism hp.contMDiff) (hY : Y.IsSmooth) (h : Y ⟶ Z)
    (hh : IsProperBimeromorphic h) :
    ∃ (V : OriginalFlagGeometry.{0} n) (r : V.carrier → W.carrier)
      (hr : IsBlowupSequence n W.carrier V.carrier r),
      IsBlowupSequence n F.carrier V.carrier (p ∘ r) ∧ IsFlagLifting F V (p ∘ r) ∧
        ∃ K : wholeModel (n := n) V.carrier ⟶ Y, K ≫ h = nativeMorphism hr.contMDiff ≫ G := by
  have := compactSpace_of_isProperBimeromorphic F hπ
  have hGpb : IsProperBimeromorphic G :=
    isProperBimeromorphic_of_comp G hπ
      (isProperBimeromorphic_nativeMorphism_of_isBlowupSequence F hp) hG
  obtain ⟨Z', -, -, A, B, hA, -, hAB⟩ :=
    OriginalCommonResolutionGeneral.exists_common_model_of_isProperBimeromorphic
      (isSmooth_wholeModel (n := n) (M := W.carrier)) hY G h hGpb hh
  obtain ⟨V₀, t₀, c₀, m₀, ρ, hρ, L, hL⟩ := exists_blowupSequence_domination H A hA
  let := t₀
  let := c₀
  let := m₀
  obtain ⟨V, q, hq, hpρq, hlift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F V₀ (p ∘ ρ)
      (HironakaChowLemma.isBlowupSequence_comp hp hρ)
  have hρq : IsBlowupSequence n W.carrier V.carrier (ρ ∘ q) :=
    HironakaChowLemma.isBlowupSequence_comp hρ hq
  refine ⟨V, ρ ∘ q, hρq, hpρq, hlift, nativeMorphism hq.contMDiff ≫ L ≫ B, ?_⟩
  have hcomp : nativeMorphism hq.contMDiff ≫ nativeMorphism hρ.contMDiff =
      nativeMorphism hρq.contMDiff :=
    morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  calc (nativeMorphism hq.contMDiff ≫ L ≫ B) ≫ h
      = nativeMorphism hq.contMDiff ≫ L ≫ (B ≫ h) := by simp only [Category.assoc]
    _ = nativeMorphism hq.contMDiff ≫ (L ≫ A) ≫ G := by rw [← hAB]; simp only [Category.assoc]
    _ = (nativeMorphism hq.contMDiff ≫ nativeMorphism hρ.contMDiff) ≫ G := by
        rw [hL, Category.assoc]
    _ = nativeMorphism hρq.contMDiff ≫ G := by rw [hcomp]

/-- **Common adapted flag model over a reduced space** (`lma:modelvalcurrbir`, from the general Chow
lemma).  Let `π : Z ⟶ X` be proper bimeromorphic from a reduced complex space to the original
compact connected Kähler manifold with its smooth flag, and `h_i : Y_i ⟶ Z` (`i = 0, 1`) proper
bimeromorphic morphisms from smooth spaces.  Then there are a finite blowup sequence `p : V → X`
with a lifted flag and proper bimeromorphic `K_i : V ⟶ Y_i` with `K₀ ≫ h₀ = K₁ ≫ h₁` over `X`. -/
theorem exists_common_flagModel (H : HironakaChowLemmaGeneral) (F : OriginalFlagGeometry.{0} n)
    {Z Y₀ Y₁ : SourceReducedComplexSpace} (π : Z ⟶ wholeModel (n := n) F.carrier)
    (hπ : IsProperBimeromorphic π) (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth)
    (h₀ : Y₀ ⟶ Z) (h₁ : Y₁ ⟶ Z) (hh₀ : IsProperBimeromorphic h₀)
    (hh₁ : IsProperBimeromorphic h₁) :
    ∃ (V : OriginalFlagGeometry.{0} n) (p : V.carrier → F.carrier)
      (hp : IsBlowupSequence n F.carrier V.carrier p),
      IsFlagLifting F V p ∧
        ∃ (K₀ : wholeModel (n := n) V.carrier ⟶ Y₀) (K₁ : wholeModel (n := n) V.carrier ⟶ Y₁),
          IsProperBimeromorphic K₀ ∧ IsProperBimeromorphic K₁ ∧ K₀ ≫ h₀ = K₁ ≫ h₁ ∧
            (K₀ ≫ h₀) ≫ π = nativeMorphism hp.contMDiff := by
  obtain ⟨W, p, hp, -, G, hG⟩ := exists_flagLifting_dominating H F π hπ
  obtain ⟨V₁, r₁, hr₁, hpr₁, -, K₀', hK₀'⟩ := exists_refinement H F π hπ W hp G hG hY₀ h₀ hh₀
  let G₁ := nativeMorphism hr₁.contMDiff ≫ G
  have hG₁ : G₁ ≫ π = nativeMorphism hpr₁.contMDiff := by
    change (nativeMorphism hr₁.contMDiff ≫ G) ≫ π = _
    rw [Category.assoc, hG]
    exact morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  obtain ⟨V, r₂, hr₂, hpr₂, hlift, K₁, hK₁⟩ := exists_refinement H F π hπ V₁ hpr₁ G₁ hG₁ hY₁ h₁ hh₁
  let G₂ := nativeMorphism hr₂.contMDiff ≫ G₁
  have hG₂ : G₂ ≫ π = nativeMorphism hpr₂.contMDiff := by
    change (nativeMorphism hr₂.contMDiff ≫ G₁) ≫ π = _
    rw [Category.assoc, hG₁]
    exact morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  have hG₂pb : IsProperBimeromorphic G₂ :=
    isProperBimeromorphic_of_comp G₂ hπ
      (isProperBimeromorphic_nativeMorphism_of_isBlowupSequence F hpr₂) hG₂
  let K₀ := nativeMorphism hr₂.contMDiff ≫ K₀'
  have hK₀ : K₀ ≫ h₀ = G₂ := by
    change (nativeMorphism hr₂.contMDiff ≫ K₀') ≫ h₀ = nativeMorphism hr₂.contMDiff ≫ G₁
    rw [Category.assoc, hK₀']
  refine ⟨V, (p ∘ r₁) ∘ r₂, hpr₂, hlift, K₀, K₁,
    isProperBimeromorphic_of_comp K₀ hh₀ hG₂pb hK₀,
    isProperBimeromorphic_of_comp K₁ hh₁ hG₂pb hK₁, hK₀.trans hK₁.symm, ?_⟩
  rw [hK₀, hG₂]

/-- **Clause (b) of `lma:modelvalcurrbir`: models of a further proper bimeromorphic `p : Z' ⟶ Z`.**
If `h₁ : Y₁ ⟶ Z'` is a model over `Z'` whose composite `h₁ ≫ p ≫ π` to `X` is proper bimeromorphic (as for
a flag model of `π ∘ p`), then `h₁ ≫ p` is proper bimeromorphic and `h₀`, `h₁ ≫ p` have a common adapted
flag model over `Z`. -/
theorem exists_common_flagModel_of_comp (H : HironakaChowLemmaGeneral)
    (F : OriginalFlagGeometry.{0} n) {Z Z' Y₀ Y₁ : SourceReducedComplexSpace}
    (π : Z ⟶ wholeModel (n := n) F.carrier) (hπ : IsProperBimeromorphic π) (p : Z' ⟶ Z)
    (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth) (h₀ : Y₀ ⟶ Z) (hh₀ : IsProperBimeromorphic h₀)
    (h₁ : Y₁ ⟶ Z') (hh₁ : IsProperBimeromorphic (h₁ ≫ p ≫ π)) :
    ∃ (V : OriginalFlagGeometry.{0} n) (q : V.carrier → F.carrier)
      (hq : IsBlowupSequence n F.carrier V.carrier q),
      IsFlagLifting F V q ∧
        ∃ (K₀ : wholeModel (n := n) V.carrier ⟶ Y₀) (K₁ : wholeModel (n := n) V.carrier ⟶ Y₁),
          IsProperBimeromorphic K₀ ∧ IsProperBimeromorphic K₁ ∧ K₀ ≫ h₀ = K₁ ≫ h₁ ≫ p ∧
            (K₀ ≫ h₀) ≫ π = nativeMorphism hq.contMDiff := by
  have hp : IsProperBimeromorphic (h₁ ≫ p) :=
    isProperBimeromorphic_of_comp (h₁ ≫ p) hπ hh₁ (Category.assoc _ _ _)
  exact exists_common_flagModel H F π hπ hY₀ hY₁ h₀ (h₁ ≫ p) hh₀ hp

end

end SGPT.Unibranch.HironakaG10EpCommonFlagModel
