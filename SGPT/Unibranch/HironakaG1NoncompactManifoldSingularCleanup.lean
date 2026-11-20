import SGPT.Unibranch.HironakaG1OriginalSingularCleanup
import SGPT.Unibranch.EmbeddedCommonResolutionGeneral
import SGPT.Foundations.Analysis.Pending.HironakaOriginalGlobalProperModification
import SGPT.Foundations.Analysis.Pending.HironakaOriginalGlobalSNCPrincipalization

/-! # Same-map noncompact original singular-locus cleanup

The prior native resolution has a genuine fixed-dimensional manifold source,
without compactness.  The existing global terminal principalization supplies
the same proper native projection, whole original pulled ideal and actual
saturated finite-terminal-range SNC geometry.  No globally finite modification
history or intrinsic canonical resolution assignment is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1NoncompactManifoldSingularCleanup

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaResolutionSpaceComplex
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalTerminalAtlas
  HironakaOriginalTerminalManifold HironakaOriginalTerminalLocalBiholomorphism
  HironakaOriginalGlobalPrincipalization HironakaOriginalGlobalOffZero
  HironakaOriginalGlobalProperModification HironakaOriginalGlobalSNCPrincipalization
  SourceReducedComplexSpace OriginalNativeModification HironakaG11SingularCentreModification
  OriginalIntrinsicSingularLocus HironakaG1OriginalSingularCleanup
open ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {n : ℕ} {M : CMfd.{0} n} (X : SourceReducedComplexSpace)
  (p : wholeModel (n := n) M ⟶ X) (hp : IsResolution p)

/-- The mark-one whole original singular ideal, with genuinely empty boundary. -/
def originalSingularMarkedIdeal : MarkedIdeal n M :=
  ⟨univ, [], originalSingularGermIdeal X p, 1⟩

include hp

private theorem originalSingularGermIdeal_thin :
    interior (originalSingularGermIdeal X p).zeroLocus = ∅ := by
  obtain ⟨_, E, _, _, hpre, hiso⟩ := hp.2
  have ht := hiso.interior_preimage_eq_empty hpre
    (interior_intrinsicSingularLocus_eq_empty X)
  rw [originalSingularGermIdeal_zeroLocus]
  change interior ((Homeomorph.Set.univ M).symm ⁻¹'
    (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅
  change interior ((p.hom.left.base : ↥(univ : Set M) → X.obj.left) ⁻¹'
    intrinsicSingularLocus X.obj) = ∅ at ht
  rw [← (Homeomorph.Set.univ M).symm.preimage_interior, ht, preimage_empty]

/-- Ordinary proper-bimeromorphic geometry internally gives the true domain. -/
theorem originalSingularMarkedDomain : IsInvDomain n (originalSingularMarkedIdeal X p) :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (originalSingularGermIdeal_coherent X p)
    (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
      (originalSingularGermIdeal_coherent X p) (originalSingularGermIdeal_thin X p hp))
    (isSNCDivisor_nil (n := n) (M := M))

/-- The genuine held global terminal manifold of this exact original ideal. -/
def cleanupSource : CMfd.{0} n :=
  originalTerminalManifold (originalSingularMarkedIdeal X p) (originalSingularMarkedDomain X p hp)

/-- The same actual terminal projection, with no compactness assumption. -/
def cleanupProjection : cleanupSource X p hp → M :=
  originalTerminalGluedProjection (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp)

/-- Its entire total-transform effective divisor. -/
def cleanupDivisor : EffectiveDivisor n (cleanupSource X p hp) :=
  originalTerminalPrincipalizationDivisor (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl

private theorem cleanupProjection_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (cleanupProjection X p hp) :=
  originalTerminalGluedProjection_contMDiff _ _

/-- The full native original morphism induced by that same projection. -/
def cleanupNativeProjection : wholeModel (n := n) (cleanupSource X p hp) ⟶ wholeModel (n := n) M :=
  nativeMorphism (cleanupProjection_contMDiff X p hp)

private theorem cleanupNativeProjection_isIsoOver :
    IsIsoOver (cleanupNativeProjection X p hp)
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' (originalSingularGermIdeal X p).zeroLocus)ᶜ := by
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  let U := originalTerminalOffZeroBaseOpen A hA
  let V := originalTerminalOffZeroSourceOpen A hA
  let e := originalTerminalOffZeroBiholomorphism A hA rfl rfl
  let E := actualSubspaceBiholomorphicIso e (univ : Set V) (univ : Set U) (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set (cleanupSource X p hp)) V
  let K := actualOpenSubspaceMap (n := n) (univ : Set M) U
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set (cleanupSource X p hp)) V
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hfacCat : nativeMorphism (M := V) (N := cleanupSource X p hp) contMDiff_subtype_val ≫
      cleanupNativeProjection X p hp =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := U) (N := M) contMDiff_subtype_val := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact (originalTerminalOffZeroBiholomorphism_point A hA rfl rfl z.val).symm
  have hfac : J ≫ (cleanupNativeProjection X p hp).hom.left = E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) V ⟶ wholeModel (n := n) M => H.hom.left) hfacCat
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · exact (range_actualOpenSubspaceMap (n := n) (univ : Set (cleanupSource X p hp)) V).trans (by rfl)
  · rw [hfac]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
  · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set V) ⟶ (wholeModel (n := n) M).obj.left => range H.base) hfac).trans
      ((range_iso_hom_comp_base E K).trans
        ((range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by rfl)))

/-- The actual global projection is proper bimeromorphic, surjective, and a full
native isomorphism over the prescribed original ideal complement. -/
theorem cleanupNativeProjection_geometry :
    IsProperBimeromorphic (cleanupNativeProjection X p hp) ∧
    IsProperMap (cleanupNativeProjection X p hp).hom.left.base ∧
    Function.Surjective (cleanupNativeProjection X p hp).hom.left.base ∧
    IsIsoOver (cleanupNativeProjection X p hp)
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' (originalSingularGermIdeal X p).zeroLocus)ᶜ := by
  obtain ⟨hhol, hproper, ⟨hAc, hAa, hAt, hBc, hBa, hBt, hpre⟩, s, hs, hfs, hsf⟩ :=
    originalTerminalGlobalProperModification_geometry (originalSingularMarkedIdeal X p)
      (originalSingularMarkedDomain X p hp) rfl rfl
  have hmod : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := n) (cleanupProjection X p hp) :=
    ⟨hhol, hproper, (cleanupDivisor X p hp).support,
      (originalSingularGermIdeal X p).zeroLocus, s,
      hAc, hAa, hAt, hBc, hBa, hBt, hpre, hs, hfs, hsf⟩
  have hq : IsProperBimeromorphic (cleanupNativeProjection X p hp) :=
    nativeMorphism_isProperBimeromorphic hmod
  exact ⟨hq, hq.1, hq.surjective, cleanupNativeProjection_isIsoOver X p hp⟩

/-- The actual whole original ideal and both full native scalar maps. -/
theorem cleanupNativeProjection_wholeStalk (x : (univ : Set (cleanupSource X p hp))) :
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set (cleanupSource X p hp))).stalkMap x).hom
      (actualWholeSheafStalkIdeal (cleanupDivisor X p hp).ideal x.val) =
      nativePulledIdealStalkIdeal ((cleanupNativeProjection X p hp) ≫ p).hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  exact map_wholeIdeal_pullback_modelGermIdeal _ _ p.hom.left
    (cleanupProjection_contMDiff X p hp) x

/-- The SAME full native composite preserves precisely the original regular
locus, and is a proper surjective resolution without a finite-history claim. -/
theorem cleanup_same_native_strong_geometry
    (hreg : IsIsoOver p (intrinsicRegularLocus X.obj)) :
    let r := cleanupNativeProjection X p hp ≫ p
    IsResolution r ∧ IsProperMap r.hom.left.base ∧ Function.Surjective r.hom.left.base ∧
      IsIsoOver r (intrinsicRegularLocus X.obj) := by
  let q := cleanupNativeProjection X p hp
  let r := q ≫ p
  obtain ⟨hq, _, _, hIq⟩ := cleanupNativeProjection_geometry X p hp
  have hIq' : IsIsoOver q (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
    convert hIq using 1
    ext x
    change p.hom.left.base x ∈ intrinsicRegularLocus X.obj ↔
      x.val ∉ (originalSingularGermIdeal X p).zeroLocus
    rw [originalSingularGermIdeal_zeroLocus]
    have hx : modelPoint x.val = x := Subtype.ext rfl
    simp only [mem_ofPred_eq, hx, intrinsicSingularLocus, mem_compl_iff, not_not]
  have hiso : IsIsoOver r (intrinsicRegularLocus X.obj) := hreg.comp hIq'
  obtain ⟨_, E, _, _, hpE, hpiso⟩ := hp.2
  have hpS := hpiso.interior_preimage_eq_empty hpE (interior_intrinsicSingularLocus_eq_empty X)
  have hrproper : IsProperMap r.hom.left.base := hp.2.1.comp hq.1
  obtain ⟨_, B, _, _, hqB, hqiso⟩ := hq
  have hrS := hqiso.interior_preimage_eq_empty hqB hpS
  have hr : IsResolution r := by
    refine ⟨isSmooth_wholeModel, hrproper, intrinsicSingularLocus X.obj,
      isAnalyticSubset_intrinsicSingularLocus X, interior_intrinsicSingularLocus_eq_empty X,
      hrS, ?_⟩
    simpa only [intrinsicSingularLocus, compl_compl] using hiso
  exact ⟨hr, hrproper, hr.2.surjective, hiso⟩

/-- The actual divisor support is the inverse ORIGINAL singular locus under
the same original native composite. -/
theorem cleanupDivisor_originalSingularSupport :
    (cleanupDivisor X p hp).support =
      {z | ((cleanupNativeProjection X p hp) ≫ p).hom.left.base (modelPoint z) ∈
        intrinsicSingularLocus X.obj} := by
  have hs := originalTerminalPrincipalizationDivisor_support (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl
  exact hs.trans (by
    ext z
    exact Set.ext_iff.mp (originalSingularGermIdeal_zeroLocus X p) (cleanupProjection X p hp z))

/-- Genuine saturated ranges cover the SAME cleanup source.  Every range is the
actual finite canonical terminal space, with its full ordered SNC boundary and
its exact inverse ORIGINAL singular support.  No local-finiteness assertion is
made about this point-indexed covering family. -/
theorem cleanup_saturated_range_readout :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let a := actualLocalTerminalAtlas A hA
    (∀ z : cleanupSource X p hp, ∃ i : M, z ∈ originalTerminalLocalRangeOpen A hA i) ∧
    ∀ i : M,
      (originalTerminalLocalRangeOpen A hA i : Set (originalTerminalManifold A hA)) =
        cleanupProjection X p hp ⁻¹' (a.openSet i : Set M) ∧
      ResolutionInvariantSpec.IsCanonical
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        ((CanonicalCentres.canonicalInvariant n).inv
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A))
        (a.tower i) ∧
      IsGeoResolution
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        (a.tower i) ∧
      (∀ z : originalTerminalLocalRangeOpen A hA i,
        originalTerminalLocalRangeProjection A hA i z =
          (a.tower i).proj ((originalTerminalLocalBiholomorphism A hA i).symm z)) ∧
      IsSNCDivisor n (originalTerminalRangeBoundary A hA i) ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        ⋃ H ∈ originalTerminalRangeBoundary A hA i, H ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        {z | ((cleanupNativeProjection X p hp) ≫ p).hom.left.base (modelPoint z.val) ∈
          intrinsicSingularLocus X.obj} := by
  dsimp only
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  refine ⟨?_, fun i => ⟨originalTerminalLocalInclusion_range A hA i,
    (actualLocalTerminalAtlas A hA).canonical i, (actualLocalTerminalAtlas A hA).terminal i,
    originalTerminalLocalRangeProjection_inverse A hA i,
    originalTerminalRangeBoundary_isSNCDivisor A hA i,
    originalTerminalRangePrincipalizationDivisor_support A hA rfl rfl rfl i, ?_⟩⟩
  · intro z
    obtain ⟨i, y, rfl⟩ := originalTerminalLocalInclusion_jointly_surjective A hA z
    exact ⟨i, ⟨y, rfl⟩⟩
  · change (GermIdeal.pullback (m := n)
      (Subtype.val : originalTerminalLocalRangeOpen A hA i → cleanupSource X p hp)
      (cleanupDivisor X p hp).ideal).zeroLocus = _
    have hcoh : (cleanupDivisor X p hp).ideal.IsCoherent :=
      GermIdealPullbackCalculus.isCoherent_pullback (cleanupProjection_contMDiff X p hp)
        (originalSingularGermIdeal_coherent X p)
    rw [BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hcoh,
      ← EffectiveDivisor.support, cleanupDivisor_originalSingularSupport]
    rfl

/-- On each actual saturated native range the ENTIRE original ideal is the
literal restricted divisor ideal, with the full original composite scalar map. -/
theorem cleanup_range_wholeStalk (i : M)
    (x : (univ : Set (originalTerminalLocalRangeOpen
      (originalSingularMarkedIdeal X p) (originalSingularMarkedDomain X p hp) i))) :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let R := originalTerminalLocalRangeOpen A hA i
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set R)).stalkMap x).hom
      (actualWholeSheafStalkIdeal
        (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).ideal x.val) =
      nativePulledIdealStalkIdeal
        ((nativeMorphism (M := R) (N := cleanupSource X p hp) contMDiff_subtype_val) ≫
          (cleanupNativeProjection X p hp ≫ p)).hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  dsimp only
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  let R := originalTerminalLocalRangeOpen A hA i
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  have hid : (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).ideal =
      GermIdeal.pullback (m := n)
        (cleanupProjection X p hp ∘ (Subtype.val : R → cleanupSource X p hp))
        (originalSingularGermIdeal X p) :=
    (GermIdealTotalTransform.pullback_comp (cleanupProjection_contMDiff X p hp)
      contMDiff_subtype_val (originalSingularGermIdeal_coherent X p)).symm
  rw [hid]
  have he : nativeMorphism ((cleanupProjection_contMDiff X p hp).comp
        (contMDiff_subtype_val (U := R))) ≫ p =
      nativeMorphism (M := R) (N := cleanupSource X p hp) contMDiff_subtype_val ≫
        (cleanupNativeProjection X p hp ≫ p) :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ fun _ => rfl
  rw [← he]
  exact map_wholeIdeal_pullback_modelGermIdeal
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) p.hom.left
    ((cleanupProjection_contMDiff X p hp).comp (contMDiff_subtype_val (U := R))) x

/-- Adapted holomorphic unit-monomial generators of the SAME whole original
singular ideal on every actual saturated terminal range. -/
theorem cleanup_range_unit_monomial_generator (i : M)
    (x : originalTerminalLocalRangeOpen (originalSingularMarkedIdeal X p)
      (originalSingularMarkedDomain X p hp) i) :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let R := originalTerminalLocalRangeOpen A hA i
    let E := originalTerminalRangeBoundary A hA i
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧ ∃ g : R → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set R, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : R → ℂ,
        (GermIdeal.pullback (m := n) (Subtype.val : R → cleanupSource X p hp)
          (cleanupDivisor X p hp).ideal).mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ j, x ∈ E.get j → (S j).card = 1) ∧ Set.InjOn S {j | x ∈ E.get j} ∧
        (∀ j, x ∈ E.get j → ∀ {y : R}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S j))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j :=
  exists_originalTerminalRange_unit_monomial_generator (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl rfl i x

end
end SGPT.Unibranch.HironakaG1NoncompactManifoldSingularCleanup
