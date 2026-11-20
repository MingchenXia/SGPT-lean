import SGPT.Okounkov.FlagLiftingExistence
import SGPT.Unibranch.HironakaG11PresUnconditional
import SGPT.Unibranch.EmbeddedCommonResolutionGeneral
import SGPT.Unibranch.HironakaG11ModificationCalculus
import SGPT.Unibranch.OriginalProperBimeromorphicNative
import SGPT.Unibranch.RIsoAModification
import SGPT.Unibranch.HironakaG10GenStatement
import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# reduced initial models in `thm:liftableflag`

Source `thm:liftableflag` (`chapter_Okounkov.tex`): let `π : Z → X` be a proper bimeromorphic
morphism from a reduced complex space `Z` to the compact Kähler manifold `X` carrying the smooth
flag `Y•`. Then there is a modification `W → X` (a finite composition of blowups with smooth
centres, `def:modif`) dominating `Z → X` such that `Y•` admits a lifting to `W`.

The book's proof begins "By Hironaka's Chow lemma `thm:HironakaChow`, we may assume that `π` is a
modification" and then runs the finite flag induction, which is
`SGPT.Okounkov.exists_flagLifting_dominating_finiteNativeModification`.

This file makes the dependence on the Chow lemma exact, for an arbitrary reduced (hence, by
properness, compact) complex space `Z` (`SGPT.Unibranch.SourceReducedComplexSpace`) and an
arbitrary proper bimeromorphic morphism `π : Z ⟶ X` of complex spaces:

* `exists_flagLifting_dominating_reducedModel_of_chow`: the whole theorem, for every reduced `Z`,
  follows from Hironaka's Chow lemma for compact complex manifolds
  (`SGPT.Foundations.Analysis.Pending.HironakaChowLemma.HironakaChowLemmaManifold`, a named
  proposition, not an axiom). The reduction resolves `Z` by the compact G11 resolution
  (`thm:res`), composes with `π` (`isProperBimeromorphic_comp_of_isIsoOver_regular`), reads the
  composite as a native analytic modification of compact manifolds, dominates it by a blowup
  sequence (Chow) and finishes with the finite flag induction.
* `isDominatedByModification_of_flagLifting`: conversely the conclusion of `thm:liftableflag`
  for `π` contains Chow domination of `π` by a modification in the sense of `def:modif`
  (`SGPT.Unibranch.HironakaG10GenStatement.IsDominatedByModification`). Hence the statement of
  `thm:liftableflag` itself (not only its proof) needs `thm:HironakaChow` for the target `X`;
  domination by a mere resolution would not give a modification of `X`.

Blueprint: `blueprint/src/oc.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OCLiftableFlag

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.HironakaChowLemma
  SGPT.Foundations.Analysis.Pending.BlowupTowers
  SGPT.Foundations.Analysis.Pending.HironakaIntrinsicComplexAnalyticRegularLocus
  SGPT.Foundations.Analysis.Pending.HironakaEmbeddedNativeMorphism
  AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.OriginalProperBimeromorphicNative
open SGPT.PSH

/-! ### Composition with an isomorphism over the regular locus -/

/-- Composition of a resolution-type morphism `p : Y ⟶ Z` (proper, an isomorphism over the
intrinsic regular locus of `Z`, with thin inverse image of the singular locus) with a proper
bimeromorphic `π : Z ⟶ X` onto a smooth space is proper bimeromorphic: `π` is an isomorphism
over the complement of its thin analytic set `T`, so `π⁻¹(Tᶜ)` consists of regular points of
`Z`, over which `p` is an isomorphism. -/
theorem isProperBimeromorphic_comp_of_isIsoOver_regular {X Y Z : SourceReducedComplexSpace}
    (hX : X.IsSmooth) {p : Y ⟶ Z} {π : Z ⟶ X}
    (hpProper : IsProperMap p.hom.left.base)
    (hpIso : IsIsoOver p (intrinsicRegularLocus Z.obj))
    (hpThin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus Z.obj) = ∅)
    (hπ : IsProperBimeromorphic π) : IsProperBimeromorphic (p ≫ π) := by
  obtain ⟨hπp, T, hTa, hTt, hπT, hπiso⟩ := hπ
  refine ⟨hπp.comp hpProper, T, hTa, hTt, ?_, ?_⟩
  · have hiso' : IsIsoOver p (intrinsicSingularLocus Z.obj)ᶜ := by
      rw [intrinsicSingularLocus, compl_compl]
      exact hpIso
    change interior (p.hom.left.base ⁻¹' (π.hom.left.base ⁻¹' T)) = ∅
    exact IsIsoOver.interior_preimage_eq_empty hiso' hpThin hπT
  · refine IsIsoOver.comp hπiso (hpIso.of_isOpen_subset ?_ ?_)
    · exact hTa.isClosed.isOpen_compl.preimage π.hom.left.base.hom.continuous
    · intro z hz
      exact (hπiso.mem_intrinsicRegularLocus_iff hz).mpr (hX _)

/-! ### The whole model of a connected manifold is its own component -/

section ComponentIso

variable {n : ℕ} (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [ConnectedSpace M]

theorem connectedSpace_wholeModel : ConnectedSpace (wholeModel (n := n) M).obj.left :=
  (Homeomorph.Set.univ M).symm.connectedSpace_iff.mp inferInstance

theorem componentSet_wholeModel_eq_univ
    (c : ConnectedComponents (wholeModel (n := n) M).obj.left) :
    OriginalSmoothComponents.componentSet c = univ := by
  let := connectedSpace_wholeModel (n := n) M
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  change OriginalSmoothComponents.componentSet (ConnectedComponents.mk y) = univ
  rw [OriginalSmoothComponents.componentSet_eq_connectedComponent,
    PreconnectedSpace.connectedComponent_eq_univ]

/-- The underlying locally ringed isomorphism from the whole model of a connected manifold onto
its unique component object. -/
def wholeModelComponentLeftIso (c : ConnectedComponents (wholeModel (n := n) M).obj.left) :
    (wholeModel (n := n) M).obj.left ≅
      (HironakaG1NoncompactSmoothComponentModel.componentObject
        (isSmooth_wholeModel (n := n) (M := M)) c).obj.left :=
  openImmersionIsoOfRangeEq (𝟙 (wholeModel (n := n) M).obj.left)
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion
      (isSmooth_wholeModel (n := n) (M := M)) c).hom.left
    (by
      rw [HironakaG1NoncompactSmoothComponentModel.componentInclusion_range,
        componentSet_wholeModel_eq_univ]
      exact Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩))

theorem wholeModelComponentLeftIso_hom_fac
    (c : ConnectedComponents (wholeModel (n := n) M).obj.left) :
    (wholeModelComponentLeftIso M c).hom ≫
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion
        (isSmooth_wholeModel (n := n) (M := M)) c).hom.left =
      𝟙 (wholeModel (n := n) M).obj.left :=
  openImmersionIsoOfRangeEq_hom_fac _ _ _

/-- The whole model of a connected manifold is isomorphic, over the complex point, to its unique
component object; the isomorphism is inverse to the component inclusion. -/
def wholeModelComponentIso (c : ConnectedComponents (wholeModel (n := n) M).obj.left) :
    wholeModel (n := n) M ≅
      HironakaG1NoncompactSmoothComponentModel.componentObject
        (isSmooth_wholeModel (n := n) (M := M)) c :=
  ObjectProperty.isoMk _ (Over.isoMk (wholeModelComponentLeftIso M c) (by
    rw [← Over.w (HironakaG1NoncompactSmoothComponentModel.componentInclusion
      (isSmooth_wholeModel (n := n) (M := M)) c).hom, ← Category.assoc,
      wholeModelComponentLeftIso_hom_fac, Category.id_comp]))

theorem wholeModelComponentIso_hom_comp_inclusion
    (c : ConnectedComponents (wholeModel (n := n) M).obj.left) :
    (wholeModelComponentIso M c).hom ≫
      HironakaG1NoncompactSmoothComponentModel.componentInclusion
        (isSmooth_wholeModel (n := n) (M := M)) c = 𝟙 (wholeModel (n := n) M) :=
  morphism_eq_of_pointwise_eq _ _ (fun x =>
    congrArg (fun H : (wholeModel (n := n) M).obj.left ⟶ (wholeModel (n := n) M).obj.left =>
      H.base x) (wholeModelComponentLeftIso_hom_fac M c))

end ComponentIso

/-! ### `thm:liftableflag` for reduced initial models, from the Chow lemma -/

/-- **Source `thm:liftableflag`, arbitrary reduced initial model, from Hironaka's Chow lemma.**
Let `F` be the compact connected Kähler manifold `X` with its smooth flag `Y•`, `Z` an arbitrary
reduced complex space and `π : Z ⟶ X` a proper bimeromorphic morphism of complex spaces.
Assuming the Chow lemma for compact complex manifolds (`HironakaChowLemmaManifold`, the
manifold case of `thm:HironakaChow`), there are a finite composition of blowups with smooth
centres `σ : W → X` (a modification of `X`, `def:modif`), a morphism of complex spaces
`g : W ⟶ Z` with `g ≫ π = σ` (domination), and `Y•` admits a lifting to `W` along `σ`
(`def:lifting`). -/
theorem exists_flagLifting_dominating_reducedModel_of_chow
    (hChow : HironakaChowLemmaManifold.{0}) {n : ℕ} (F : OriginalFlagGeometry.{0} n)
    (Z : SourceReducedComplexSpace) (π : Z ⟶ wholeModel (n := n) F.carrier)
    (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} n) (σ : W.carrier → F.carrier)
      (hσ : IsBlowupSequence n F.carrier W.carrier σ)
      (g : wholeModel (n := n) W.carrier ⟶ Z),
      g ≫ π = nativeMorphism hσ.contMDiff ∧ IsFlagLifting F W σ := by
  -- `Z` is compact, since `π` is proper and `X` is compact.
  have hXc : CompactSpace (wholeModel (n := n) F.carrier).obj.left :=
    isCompact_iff_compactSpace.mp (isCompact_univ : IsCompact (univ : Set F.carrier))
  have hZc : CompactSpace Z.obj.left :=
    ⟨by simpa only [preimage_univ] using hπ.1.isCompact_preimage (@isCompact_univ _ _ hXc)⟩
  -- The compact G11 resolution of `Z` (`thm:res`).
  obtain ⟨Y, p, _hsing, _hmod, hYs, _hres, _hsurj, hpp, hpiso, _hdense, hpthin, _⟩ :=
    HironakaG11PresUnconditional.exists_endpoint Z hZc
  have hG : IsProperBimeromorphic (p ≫ π) :=
    isProperBimeromorphic_comp_of_isIsoOver_regular isSmooth_wholeModel hpp hpiso hpthin hπ
  -- A native manifold component of the resolution mapping onto `X`.
  obtain ⟨x0⟩ := (inferInstance : Nonempty F.carrier)
  let c : ConnectedComponents (wholeModel (n := n) F.carrier).obj.left :=
    ConnectedComponents.mk (⟨x0, mem_univ x0⟩ : (univ : Set F.carrier))
  let I := wholeModelComponentIso (n := n) F.carrier c
  obtain ⟨cY, N, J, G, hGpb, hsq⟩ :=
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hYs
      isSmooth_wholeModel (p ≫ π) hG c (CMfd.of (n := n) F.carrier) I
  have hGmod : IsAnalyticModification (n := n) (nativePointMap G) :=
    isAnalyticModification_of_isProperBimeromorphic G hGpb
  -- Chow domination of the native modification of compact manifolds.
  obtain ⟨X', topX', chartsX', complexX', σ, g, hσ, hg, hgσ⟩ :=
    hChow n F.carrier N (nativePointMap G) hGmod
  let := topX'
  let := chartsX'
  let := complexX'
  -- The finite flag induction on the dominating finite model.
  obtain ⟨W, q, hq, hσq, hLift⟩ :=
    exists_flagLifting_dominating_finiteNativeModification F X' σ hσ
  let gq : wholeModel (n := n) W.carrier ⟶ wholeModel (n := n) N :=
    nativeMorphism (hg.comp hq.contMDiff)
  refine ⟨W, σ ∘ q, hσq, gq ≫ J.hom ≫
      HironakaG1NoncompactSmoothComponentModel.componentInclusion hYs cY ≫ p, ?_, hLift⟩
  have hI : I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
      isSmooth_wholeModel c = 𝟙 _ :=
    wholeModelComponentIso_hom_comp_inclusion (n := n) F.carrier c
  calc (gq ≫ J.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hYs cY ≫ p) ≫ π
        = gq ≫ (J.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hYs cY ≫
            (p ≫ π)) := by simp only [Category.assoc]
    _ = gq ≫ (G ≫ (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion
            isSmooth_wholeModel c)) := by rw [hsq]
    _ = gq ≫ G := by rw [hI, Category.comp_id]
    _ = nativeMorphism hσq.contMDiff :=
        morphism_eq_of_pointwise_eq _ _ (fun w => Subtype.ext (congrFun hgσ (q w.val)))

/-! ### Conversely, the statement contains Chow domination -/

/-- **The conclusion of `thm:liftableflag` contains Chow domination.** If a finite composition of
smooth-centre blowups `σ : W → X` dominates `π : Z ⟶ X` through a morphism `g : W ⟶ Z`, then `π`
is dominated by a modification of `X` in the sense of `def:modif` (the conclusion of
`thm:HironakaChow` for `π`). The flag lifting plays no role: the statement of `thm:liftableflag`
for `π` already implies the Chow lemma for `π`. -/
theorem isDominatedByModification_of_blowupDomination {n : ℕ} {X W : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace W] [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W]
    {Z : SourceReducedComplexSpace} {π : Z ⟶ wholeModel (n := n) X}
    {σ : W → X} (hσ : IsBlowupSequence n X W σ) (g : wholeModel (n := n) W ⟶ Z)
    (hg : g ≫ π = nativeMorphism hσ.contMDiff) :
    HironakaG10GenStatement.IsDominatedByModification π := by
  obtain ⟨P, hP, hPσ⟩ := RIsoAModification.isModification_of_isBlowupSequence hσ
  refine ⟨wholeModel (n := n) W, P, g, hP, ?_⟩
  rw [hg]
  exact morphism_eq_of_pointwise_eq _ _ (fun y => Subtype.ext (hPσ y).symm)

/-- The full conclusion of `thm:liftableflag` for `π` implies Chow domination of `π`. -/
theorem isDominatedByModification_of_flagLifting {n : ℕ} {F : OriginalFlagGeometry.{0} n}
    {Z : SourceReducedComplexSpace} {π : Z ⟶ wholeModel (n := n) F.carrier}
    (h : ∃ (W : OriginalFlagGeometry.{0} n) (σ : W.carrier → F.carrier)
      (hσ : IsBlowupSequence n F.carrier W.carrier σ)
      (g : wholeModel (n := n) W.carrier ⟶ Z),
      g ≫ π = nativeMorphism hσ.contMDiff ∧ IsFlagLifting F W σ) :
    HironakaG10GenStatement.IsDominatedByModification π := by
  obtain ⟨_W, _σ, hσ, g, hg, _⟩ := h
  exact isDominatedByModification_of_blowupDomination hσ g hg

end SGPT.Okounkov.OCLiftableFlag
