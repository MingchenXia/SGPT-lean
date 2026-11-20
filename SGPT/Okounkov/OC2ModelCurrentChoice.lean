import SGPT.Okounkov.OCModelCurrentValuation
import SGPT.Unibranch.KS3KahlerBlowupStep
import SGPT.Unibranch.KS3KahlerResolution
import SGPT.Unibranch.KS3KahlerManifold
import SGPT.Unibranch.KSDimension
import SGPT.PSH.PrimeNov16OriginalFibreDictionary
import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-!
# existence of a choice in `def:modelvalcurr`, without the Chow lemma

Source `def:modelvalcurr` (`chapter_Okounkov.tex`): let `π : Z → X` be a proper bimeromorphic
morphism from a normal compact Kähler space and `S` a closed positive `(1,1)`-current on `Z`.
*Choose* a proper bimeromorphic `h : Ẑ → Z` from a compact Kähler manifold such that `Y•` admits a
lifting `(W•, g)` to `Ẑ` with respect to `π ∘ h`, `g = cor(Y•, π ∘ h)`, and put
`ν_{Y•}(S) := ν_{W•}(h^*S) g⁻¹`.

Lane OC formalized the value for a given choice (`OCModelCurrentValuation.modelCurrentFlagValuation`)
and its independence of the choice (`modelCurrentFlagValuation_eq_of_choices`), but obtained a
choice only from Hironaka's Chow lemma (`exists_choice_of_chow`). This file proves the existence
of a choice **unconditionally**, so that the definition is total:

* the compact resolution `p : Y → Z` of `G11` (`HironakaG11PresUnconditional.exists_endpoint`:
  smooth-centre blowups, an isomorphism over the regular locus of `Z`);
* `Y` is a compact Kähler space (lane KS3: `isKahlerSpace_of_isModification` with the proved
  blowup step `KS3KahlerBlowupStep.kahlerBlowupStep`);
* `p ≫ π` is proper bimeromorphic (`OCLiftableFlag.isProperBimeromorphic_comp_of_isIsoOver_regular`)
  and `Y` is connected (`connectedSpace_of_isProperBimeromorphic_wholeModel`: a smooth space with a
  proper bimeromorphic morphism onto a connected manifold is connected), hence `Y ≅ (M, 𝒪_M)` for a
  compact Kähler manifold `M` of dimension `dim X` (`exists_connected_native_manifold_model`,
  `KSDimension.dim_eq_of_isProperBimeromorphic`, `KS3KahlerManifold.kahlerBackgroundOfIso`);
* the flag lifting along the native analytic modification `M → X`
  (`exists_flagLifting_dominating_nativeModel`, the flag-by-flag induction of the proof of
  `thm:liftableflag`, for an arbitrary compact Kähler manifold source; strict transforms of the
  flag members and their Kähler embedded resolutions inside `M`).

Main results.

* `exists_choice`: for every reduced compact Kähler space `Z` (compactness follows from the
  properness of `π`) and proper bimeromorphic `π : Z ⟶ X`, there is a choice `h` in the sense of
  `def:modelvalcurr`. No Chow lemma, no normality is needed for this.
* `modelCurrentValuation`: the total valuation `ν_{Y•}(S)` of `def:modelvalcurr` for `Z` unibranch
  (normal implies unibranch, `isUnibranch_of_normal_stalks`) compact Kähler and
  `S = θ + ddᶜφ`;
* `modelCurrentValuation_eq`: it equals `ν_{W•}(h^*S) g⁻¹` for **every** choice `h`.

Blueprint: `blueprint/src/OC2.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OC2ModelCurrentChoice

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.BlowupTowers
  AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.OriginalProperBimeromorphicNative
open SGPT.Okounkov.OCModelCurrentValuation

/-! ### Connectedness of a smooth model over a connected manifold -/

/-- The identity of a reduced complex space is proper bimeromorphic. -/
theorem isProperBimeromorphic_id (Y : SourceReducedComplexSpace) :
    IsProperBimeromorphic (𝟙 Y) := by
  refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
  exact IsIsoOver.id_of_isOpen Y (by simp)

/-- **A smooth complex space with a proper bimeromorphic morphism onto a connected complex
manifold is connected.** The component of `Y` lying over the unique component of `(M, 𝒪_M)` is
the whole preimage of `M` (`component_preimage_eq_of_actual_native_lift`). -/
theorem connectedSpace_of_isProperBimeromorphic_wholeModel {Y : SourceReducedComplexSpace}
    (hY : Y.IsSmooth) {n : ℕ} (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [ConnectedSpace M] (G : Y ⟶ wholeModel (n := n) M)
    (hG : IsProperBimeromorphic G) : ConnectedSpace Y.obj.left := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  let c : ConnectedComponents (wholeModel (n := n) M).obj.left :=
    ConnectedComponents.mk (⟨x0, mem_univ x0⟩ : (univ : Set M))
  let I := OCLiftableFlag.wholeModelComponentIso (n := n) M c
  obtain ⟨cY, N, J, G', hG', hsq⟩ :=
    PSH.PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hY
      isSmooth_wholeModel G hG c (CMfd.of (n := n) M) I
  have hmod := isAnalyticModification_of_isProperBimeromorphic G' hG'
  have hfull : nativeMorphism hmod.1 = G' := nativeMorphism_nativePointMap G'
  have hpre := PSH.PrimeNov16OriginalFibreDictionary.component_preimage_eq_of_actual_native_lift
    hY isSmooth_wholeModel G hG cY c N (CMfd.of (n := n) M) J I (nativePointMap G') hmod
    (by rw [hfull]; exact hsq)
  rw [OCLiftableFlag.componentSet_wholeModel_eq_univ, preimage_univ] at hpre
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe cY
  rw [OriginalSmoothComponents.componentSet_eq_connectedComponent] at hpre
  exact connectedSpace_iff_connectedComponent.mpr ⟨y, hpre.symm⟩

/-! ### Existence of a choice -/

variable {m : ℕ} (F : OriginalFlagGeometry.{0} (m + 1)) {Z : SourceReducedComplexSpace}

/-- **A compact Kähler manifold model over `X`.** For a compact Kähler space `Z` and a proper
bimeromorphic `π : Z ⟶ X` onto the compact connected Kähler manifold `X = F.carrier`, there are a
compact Kähler manifold `M` of the same dimension and a proper bimeromorphic morphism
`g : (M, 𝒪_M) ⟶ Z` such that `π ∘ g` is proper bimeromorphic: the `G11` resolution of `Z`
(smooth-centre blowups), Kähler by lane KS3, connected because it maps bimeromorphically onto `X`. -/
theorem exists_kahler_manifold_model (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) (hK : Z.IsKahlerSpace) :
    ∃ (M : CMfd.{0} (m + 1)) (_ : CompactSpace M) (_ : KahlerBackground (m + 1) M)
      (g : wholeModel (n := m + 1) M ⟶ Z),
      IsProperBimeromorphic g ∧ IsProperBimeromorphic (g ≫ π) := by
  -- `Z` is compact, since `π` is proper and `X` is compact.
  have hXc : CompactSpace (wholeModel (n := m + 1) F.carrier).obj.left :=
    isCompact_iff_compactSpace.mp (isCompact_univ : IsCompact (univ : Set F.carrier))
  have hZc : CompactSpace Z.obj.left :=
    ⟨by simpa only [preimage_univ] using hπ.1.isCompact_preimage (@isCompact_univ _ _ hXc)⟩
  -- The compact G11 resolution of `Z`.
  obtain ⟨Y, p, _hsing, hmod, hYs, hres, _hsurj, hpp, hpiso, _hdense, hpthin, hcompact⟩ :=
    HironakaG11PresUnconditional.exists_endpoint Z hZc
  have hYc : CompactSpace Y.obj.left := hcompact hZc
  -- `Y` is Kähler.
  have hYK : Y.IsKahlerSpace :=
    KS3KahlerResolution.isKahlerSpace_of_isModification KS3KahlerBlowupStep.kahlerBlowupStep
      hmod hZc hK
  -- `p ≫ π` is proper bimeromorphic and `Y` is connected.
  have hG : IsProperBimeromorphic (p ≫ π) :=
    OCLiftableFlag.isProperBimeromorphic_comp_of_isIsoOver_regular isSmooth_wholeModel hpp hpiso
      hpthin hπ
  have hYconn : ConnectedSpace Y.obj.left :=
    connectedSpace_of_isProperBimeromorphic_wholeModel hYs F.carrier (p ≫ π) hG
  -- The manifold model of `Y`.
  obtain ⟨n, M, ⟨E⟩⟩ :=
    HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model hYs
  have hEG : IsProperBimeromorphic (E.hom ≫ p ≫ π) := hG.precomp_iso E
  have hdim : m + 1 = n :=
    KSUnibranchIEnvelope.dim_eq_of_isProperBimeromorphic
      (𝟙 (wholeModel (n := m + 1) F.carrier)) (E.hom ≫ p ≫ π)
      (isProperBimeromorphic_id _) hEG
  subst hdim
  have : CompactSpace (wholeModel (n := m + 1) M).obj.left :=
    (isoHomeomorph E).symm.compactSpace
  have hMc : CompactSpace M := KS3KahlerResolution.compactSpace_of_wholeModel (n := m + 1)
  obtain ⟨κ, hκ⟩ := hYK
  refine ⟨M, hMc, KS3KahlerManifold.kahlerBackgroundOfIso hκ E.hom, E.hom ≫ p,
    hres.2.precomp_iso E, ?_⟩
  simpa only [Category.assoc] using hEG

/-- **Source `def:modelvalcurr`: existence of a choice of `h`, unconditionally.** Let `Z` be a
reduced compact Kähler space (`IsKahlerSpace`; compactness is automatic) and
`π : Z ⟶ X` proper bimeromorphic, `X = F.carrier` the compact Kähler manifold carrying the smooth
flag `Y•`. There are a compact connected Kähler manifold `Ẑ` with a smooth flag `W•`
(`W : OriginalFlagGeometry`) and a proper bimeromorphic `h : Ẑ ⟶ Z` such that `W•` is a lifting
of `Y•` along `π ∘ h` (`IsFlagLifting`). No Chow lemma is used: `Ẑ` is a finite sequence of
smooth-centre blowups of the Kähler `G11` resolution of `Z`, obtained by the flag induction of
`thm:liftableflag` (`exists_flagLifting_dominating_nativeModel`). -/
theorem exists_choice (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) (hK : Z.IsKahlerSpace) :
    ∃ (W : OriginalFlagGeometry.{0} (m + 1)) (h : wholeModel (n := m + 1) W.carrier ⟶ Z),
      IsProperBimeromorphic h ∧ IsFlagLifting F W (nativePointMap (h ≫ π)) := by
  obtain ⟨M, hMc, omegaM, g, _hg, hgπ⟩ := exists_kahler_manifold_model F π hπ hK
  have hGmod : IsAnalyticModification (n := m + 1) (nativePointMap (g ≫ π)) :=
    isAnalyticModification_of_isProperBimeromorphic (g ≫ π) hgπ
  obtain ⟨W, q, hq, hLift⟩ :=
    exists_flagLifting_dominating_nativeModel (m + 1) F M omegaM (nativePointMap (g ≫ π)) hGmod
  let h : wholeModel (n := m + 1) W.carrier ⟶ Z := nativeMorphism hq.contMDiff ≫ g
  have hmap : nativePointMap (h ≫ π) = nativePointMap (g ≫ π) ∘ q := by
    funext w
    rfl
  have hLift' : IsFlagLifting F W (nativePointMap (h ≫ π)) := by
    rw [hmap]
    exact hLift
  exact ⟨W, h, isProperBimeromorphic_of_isAnalyticModification_comp hπ h hLift'.1, hLift'⟩

/-! ### The total valuation -/

/-- **Source `def:modelvalcurr`.** The valuation `ν_{Y•}(S) := ν_{W•}(h^*S) g⁻¹ ∈ ℝⁿ` of the
closed positive `(1,1)`-current `S = θ + ddᶜφ` on the unibranch (e.g. normal) compact Kähler
space `Z`, with respect to the proper bimeromorphic model `π : Z ⟶ X`, computed on a choice `h`
given by `exists_choice`. By `modelCurrentValuation_eq` the value is the same for every choice. -/
def modelCurrentValuation (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) (hK : Z.IsKahlerSpace) (hZ : Z.IsUnibranch)
    (θ : SpaceForm Z 2) (φ : Z.obj.left → EReal) (hφ : Z.IsThetaPSH θ φ) : Fin (m + 1) → ℝ :=
  modelCurrentFlagValuation F π
    (Classical.choose (Classical.choose_spec (exists_choice F π hπ hK)))
    (Classical.choose_spec (Classical.choose_spec (exists_choice F π hπ hK))).1
    (Classical.choose_spec (Classical.choose_spec (exists_choice F π hπ hK))).2 hZ θ φ hφ

/-- **Source `def:modelvalcurr`, well-definedness.** For every choice `h : Ẑ ⟶ Z` (a compact
Kähler flagged manifold, `h` proper bimeromorphic, `Y•` lifting along `π ∘ h`) and every closed
real `(1,1)`-form `θ`, `ν_{Y•}(S) = ν_{W•}(h^*S) cor(Y•, π ∘ h)⁻¹`. -/
theorem modelCurrentValuation_eq (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) (hK : Z.IsKahlerSpace) (hZ : Z.IsUnibranch)
    {W : OriginalFlagGeometry.{0} (m + 1)} (h : wholeModel (n := m + 1) W.carrier ⟶ Z)
    (hh : IsProperBimeromorphic h) (hLift : IsFlagLifting F W (nativePointMap (h ≫ π)))
    (θ : SpaceForm Z 2) (hθc : θ.IsClosed) (hθ11 : θ.IsOneOne) (φ : Z.obj.left → EReal)
    (hφ : Z.IsThetaPSH θ φ) :
    modelCurrentValuation F π hπ hK hZ θ φ hφ =
      modelCurrentFlagValuation F π h hh hLift hZ θ φ hφ :=
  modelCurrentFlagValuation_eq_of_choices F π _ h _ hh _ hLift hZ θ hθc hθ11 φ hφ

/-- **Source `def:modelvalcurr`, specification.** The valuation is computed by an actual choice
of `h`: there are a compact connected Kähler flagged manifold `W`, a proper bimeromorphic
`h : W ⟶ Z` and a lifting of `Y•` along `π ∘ h` with
`ν_{Y•}(S) = ν_{W•}(h^*S) cor(Y•, π ∘ h)⁻¹`. -/
theorem exists_choice_modelCurrentValuation_eq (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) (hK : Z.IsKahlerSpace) (hZ : Z.IsUnibranch)
    (θ : SpaceForm Z 2) (φ : Z.obj.left → EReal) (hφ : Z.IsThetaPSH θ φ) :
    ∃ (W : OriginalFlagGeometry.{0} (m + 1)) (h : wholeModel (n := m + 1) W.carrier ⟶ Z)
      (hh : IsProperBimeromorphic h) (hLift : IsFlagLifting F W (nativePointMap (h ≫ π))),
      modelCurrentValuation F π hπ hK hZ θ φ hφ =
        modelCurrentFlagValuation F π h hh hLift hZ θ φ hφ :=
  ⟨_, _, _, _, rfl⟩

end SGPT.Okounkov.OC2ModelCurrentChoice
