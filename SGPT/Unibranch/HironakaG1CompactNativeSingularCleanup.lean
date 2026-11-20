import SGPT.Unibranch.HironakaG1OriginalSingularCleanup
import SGPT.Unibranch.HironakaG1NativeIsoOverDisjointCover
import SGPT.Unibranch.HironakaG10GenChow
import SGPT.Unibranch.HironakaG11PresUnconditional

/-! # Same-map SNC refinement of arbitrary compact native smooth sources

Actual compact smooth components internally provide their possibly different
manifold dimensions and full native model isomorphisms.  Canonical cleanup of
the whole pulled ORIGINAL singular ideal on each component is assembled by the
held native disjoint-modification theorem.  Every boundary and whole ideal
readout refers to the SAME composite.  No canonical G1 assignment is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CompactNativeSingularCleanup

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaG1OriginalSingularCleanup HironakaG1NativeIsoOverDisjointCover
  SourceReducedComplexSpace OriginalNativeModification HironakaG11SingularCentreModification
  OriginalIntrinsicSingularLocus SmoothCentreModification OriginalSmoothComponents
  OriginalSmoothComponentPairing HironakaG10GenChow HironakaG10GenDisjointModification

noncomputable section

section Manifold

variable {n : ℕ} {M : CMfd.{0} n} [CompactSpace M] (X : SourceReducedComplexSpace)

/-- Thinness is ordinary geometric input; no modification of the entire target
is required of the map from a single smooth component. -/
theorem exists_cleanup_of_thin_original_pullback (a : wholeModel (n := n) M ⟶ X)
    (hthin : interior {x : M |
      a.hom.left.base (modelPoint x) ∈ intrinsicSingularLocus X.obj} = ∅) :
    let I := originalSingularGermIdeal X a
    let A : MarkedIdeal n M := ⟨univ, [], I, 1⟩
    ∃ (D : CMfd.{0} n) (T : BlowupTower M D),
      ResolutionInvariantSpec.IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) T ∧
      IsGeoResolution A T ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      IsSNCDivisor n (geoTransformAlong A T).E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong A T).E, H ∧
      (exceptionalDivisor T).support =
        {z : D | a.hom.left.base (modelPoint (T.proj z)) ∈ intrinsicSingularLocus X.obj} ∧
      IsModification (nativeMorphism T.contMDiff_proj) ∧
      IsIsoOver (nativeMorphism T.contMDiff_proj)
        ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' I.zeroLocus)ᶜ ∧
      ∀ x : (univ : Set D),
        Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set D)).stalkMap x).hom
          (actualWholeSheafStalkIdeal (exceptionalDivisor T).ideal x.val) =
          nativePulledIdealStalkIdeal ((nativeMorphism T.contMDiff_proj) ≫ a).hom.left
            (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
            (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  let I := originalSingularGermIdeal X a
  have hI := originalSingularGermIdeal_coherent X a
  have ht : interior I.zeroLocus = ∅ := by
    rw [originalSingularGermIdeal_zeroLocus]
    exact hthin
  have hnz := PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty hI ht
  have hK : IsCompact I.zeroLocus := (OrderTaylor.isClosed_zeroLocus_of_isCoherent hI).isCompact
  let A : MarkedIdeal n M := ⟨univ, [], I, 1⟩
  let hA := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    hI hnz (isSNCDivisor_nil (n := n) (M := M))
  let hcos : IsCompact A.cosupp := (HironakaAdmissibleSequence.cosupp_univ_one hI).symm ▸ hK
  let P := compactCosupportCanonicalTower A hA hcos
  let T := P.2.val
  obtain ⟨hc, hr, _, _, _, hover, _, hpb, hE, hsupp, hpre, _, _, _⟩ :=
    canonical_boundary_principalization I hI hnz hK [] (isSNCDivisor_nil (n := n) (M := M))
  have hmod : IsModification (nativeMorphism T.contMDiff_proj) := by
    obtain ⟨q, hq, hpt⟩ := RIsoAModification.isModification_of_isBlowupSequence T.isBlowupSequence
    have he : q = nativeMorphism T.contMDiff_proj := by
      apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
      intro x
      exact Subtype.ext (hpt x)
    exact he ▸ hq
  refine ⟨P.1, T, hc, hr, hpb, hE, ?_, ?_, hmod,
    nativeTower_isIsoOver_of_centresOver T I.zeroLocus
      (OrderTaylor.isClosed_zeroLocus_of_isCoherent hI) hover, ?_⟩
  · simpa only [List.length_nil, List.drop_zero] using hsupp
  · exact hpre.trans (by
      ext z
      exact Set.ext_iff.mp (originalSingularGermIdeal_zeroLocus X a) (T.proj z))
  · intro x
    let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
      X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
    rw [← hpb]
    exact map_wholeIdeal_pullback_modelGermIdeal _ _ a.hom.left T.contMDiff_proj x

end Manifold

section CompactNative

variable {X Y : SourceReducedComplexSpace} [CompactSpace Y.obj.left]

/-- An arbitrary compact native smooth resolution source, including distinct
component dimensions, has an internally assembled SAME-map strong refinement.
The displayed disjoint clopen manifold models retain all SNC/whole-ideal data. -/
theorem exists_compact_native_strong_refinement (p : Y ⟶ X)
    (hp : IsSingularCentreModification p) (hY : Y.IsSmooth) :
    ∃ (Z : SourceReducedComplexSpace) (ρ : Z ⟶ Y) (N : ℕ) (n : Fin N → ℕ)
      (D : ∀ i, CMfd.{0} (n i)) (E : ∀ i, List (Set (D i)))
      (Δ : ∀ i, EffectiveDivisor (n i) (D i))
      (L : ∀ i, wholeModel (n := n i) (D i) ⟶ Z),
      let r := ρ ≫ p
      IsModification ρ ∧ IsModification r ∧ Z.IsSmooth ∧ IsResolution r ∧
      IsProperMap r.hom.left.base ∧ Function.Surjective r.hom.left.base ∧
      IsIsoOver r (intrinsicRegularLocus X.obj) ∧
      (∀ i, CompactSpace (D i)) ∧
      (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) ∧
      (∀ i, IsClosedEmbedding (L i).hom.left.base) ∧
      (∀ z : Z.obj.left, ∃ (i : Fin N) (x : (wholeModel (n := n i) (D i)).obj.left),
        (L i).hom.left.base x = z) ∧
      Pairwise (fun i k => Disjoint (range (L i).hom.left.base) (range (L k).hom.left.base)) ∧
      ∀ i, IsSNCDivisor (n i) (E i) ∧ (Δ i).support = ⋃ H ∈ E i, H ∧
        (Subtype.val : ↥(univ : Set (D i)) → D i) ⁻¹' (Δ i).support =
          (L i).hom.left.base ⁻¹' (r.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) ∧
        ∀ x : (univ : Set (D i)),
          Ideal.map ((actualSubspaceInclusion (n := n i) (univ : Set (D i))).stalkMap x).hom
            (actualWholeSheafStalkIdeal (Δ i).ideal x.val) =
            nativePulledIdealStalkIdeal (L i ≫ r).hom.left
              (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
              (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  let : Finite (ConnectedComponents Y.obj.left) := finite_connectedComponents hY
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (ConnectedComponents Y.obj.left)
  let c (i : Fin N) := e.symm i
  let n (i : Fin N) := componentDimension hY (c i)
  let M (i : Fin N) : CMfd.{0} (n i) := by
    let := componentChartedSpace hY (c i)
    let := componentIsComplexManifold hY (c i)
    exact CMfd.of (n := n i) (componentObject hY (c i)).obj.left
  let (i : Fin N) : ChartedSpace (ComplexModel (n i)) (M i) := (M i).chartedSpace
  let (i : Fin N) : IsComplexManifold (n i) (M i) := (M i).isComplexManifold
  let j (i : Fin N) : wholeModel (n := n i) (M i) ⟶ Y := compEmb hY (c i)
  have hj (i : Fin N) : LocallyRingedSpace.IsOpenImmersion (j i).hom.left :=
    compEmb_isOpenImmersion hY (c i)
  have hjr (i : Fin N) : range (j i).hom.left.base = componentSet (c i) :=
    compEmb_range hY (c i)
  have hdisj : Pairwise (fun i k : Fin N =>
      Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)) := by
    intro i k hik
    rw [hjr, hjr]
    exact componentSet_pairwise_disjoint (fun h => hik (e.symm.injective h))
  have hjcover (y : Y.obj.left) :
      ∃ (i : Fin N) (x : (wholeModel (n := n i) (M i)).obj.left), (j i).hom.left.base x = y := by
    have hm : y ∈ range (j (e (ConnectedComponents.mk y))).hom.left.base := by
      rw [hjr]
      change ConnectedComponents.mk y = e.symm (e (ConnectedComponents.mk y))
      exact (e.symm_apply_apply _).symm
    exact ⟨_, hm⟩
  have hMc (i : Fin N) : CompactSpace (M i) := compactSpace_componentObject hY (c i)
  have hthin (i : Fin N) : interior {x : M i |
      (j i ≫ p).hom.left.base (modelPoint x) ∈ intrinsicSingularLocus X.obj} = ∅ := by
    let J := (componentInclusion hY (c i)).hom.left
    have hJI : LocallyRingedSpace.IsOpenImmersion J :=
      componentInclusion_isOpenImmersion hY (c i)
    have heq : {x : M i | (j i ≫ p).hom.left.base (modelPoint x) ∈ intrinsicSingularLocus X.obj} =
        J.base ⁻¹' (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) := by
      ext x
      change p.hom.left.base (J.base ((componentNativeIso hY (c i)).hom.hom.left.base
        (modelPoint x))) ∈ intrinsicSingularLocus X.obj ↔ _
      rw [componentNativeIso_point]
      rfl
    have hi : J.base ⁻¹' interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) =
        interior (J.base ⁻¹' (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) :=
      hJI.base_open.isOpenMap.preimage_interior_eq_interior_preimage J.base.hom.continuous _
    exact (congrArg interior heq).trans (hi.symm.trans
      (by rw [hp.interior_preimage_intrinsicSingularLocus]; rfl))
  let (i : Fin N) : CompactSpace (M i) := hMc i
  choose D T hc hgeo hpb hE hsupp hpre hmod hiso hwhole using
    fun i => exists_cleanup_of_thin_original_pullback X (j i ≫ p) (hthin i)
  let A (i : Fin N) := wholeModel (n := n i) (D i)
  let q (i : Fin N) : A i ⟶ wholeModel (n := n i) (M i) :=
    nativeMorphism (T i).contMDiff_proj
  obtain ⟨Z, ρ, L, hρ, hL, hLc, hcov⟩ := exists_isModification_of_cover j hj
    (fun i => (hjr i).symm ▸ (component_isClopen hY (c i)).1) hdisj
    (fun y => by obtain ⟨i, x, hx⟩ := hjcover y; exact ⟨i, x, hx⟩) q hmod
  have hDcompact (i : Fin N) : CompactSpace (D i) := by
    constructor
    simpa only [preimage_univ] using
      (HironakaLocalPrincipalization.isProperMap_proj (T i)).isCompact_preimage
        (isCompact_univ : IsCompact (univ : Set (M i)))
  have hLIcover (z : Z.obj.left) : ∃ (i : Fin N) (x : (A i).obj.left), (L i).hom.left.base x = z :=
    hcov z
  have hLdisj : Pairwise (fun i k =>
      Disjoint (range (L i).hom.left.base) (range (L k).hom.left.base)) := by
    intro i k hik
    apply disjoint_left.mpr
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    have hia : ρ.hom.left.base ((L i).hom.left.base a) ∈ range (j i).hom.left.base := by
      have hpt := congrArg (fun F : A i ⟶ Y => F.hom.left.base a) (hLc i)
      exact ⟨_, hpt.symm⟩
    have hkb : ρ.hom.left.base ((L k).hom.left.base b) ∈ range (j k).hom.left.base := by
      have hpt := congrArg (fun F : A k ⟶ Y => F.hom.left.base b) (hLc k)
      exact ⟨_, hpt.symm⟩
    rw [ha] at hia
    rw [hb] at hkb
    exact disjoint_left.mp (hdisj hik) hia hkb
  have hLclosed (i : Fin N) : IsClosedEmbedding (L i).hom.left.base := by
    have hAc : CompactSpace (A i).obj.left := by
      change CompactSpace ↥(univ : Set (D i))
      exact isCompact_iff_compactSpace.mp (@isCompact_univ (D i) _ (hDcompact i))
    have hsource := @isCompact_univ (A i).obj.left _ hAc
    have himage := hsource.image (L i).hom.left.base.hom.continuous
    exact ⟨(hL i).base_open.isEmbedding, by
      simpa only [image_univ] using
        (@IsCompact.isClosed Z.obj.left _ Z.property.1 _ himage)⟩
  have hZ : Z.IsSmooth := by
    intro z
    obtain ⟨i, a, rfl⟩ := hLIcover z
    have hs : (A i).IsSmooth := isSmooth_wholeModel
    obtain ⟨d, V, u, hu, hscalar, x, hx⟩ := hs a
    refine ⟨d, V, u ≫ (L i).hom.left,
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ u hu _ (hL i), ?_, x,
      congrArg (L i).hom.left.base hx⟩
    rw [Category.assoc, Over.w (L i).hom]
    exact hscalar
  let U := p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj
  have hU : IsOpen U := (isOpen_intrinsicRegularLocus X.obj).preimage p.hom.left.base.hom.continuous
  have hqU (i : Fin N) : IsIsoOver (q i) ((j i).hom.left.base ⁻¹' U) := by
    convert hiso i using 1
    ext x
    change p.hom.left.base ((j i).hom.left.base x) ∈ intrinsicRegularLocus X.obj ↔
      x.val ∉ (originalSingularGermIdeal X (j i ≫ p)).zeroLocus
    rw [originalSingularGermIdeal_zeroLocus]
    have hx : modelPoint x.val = x := Subtype.ext rfl
    simp only [mem_ofPred_eq, hx, intrinsicSingularLocus, mem_compl_iff, not_not]
    rfl
  have hρU : IsIsoOver ρ U :=
    isIsoOver_of_disjoint_cover ρ j L q hj hL hjcover hLIcover hdisj hLc U hU hqU
  have hrmod : IsModification (ρ ≫ p) := hρ.comp hp.toIsModification
  have hriso : IsIsoOver (ρ ≫ p) (intrinsicRegularLocus X.obj) :=
    hp.isIsoOver_intrinsicRegularLocus.comp hρU
  have hrres : IsResolution (ρ ≫ p) := by
    refine ⟨hZ, hrmod.isProperMap, intrinsicSingularLocus X.obj,
      isAnalyticSubset_intrinsicSingularLocus X, interior_intrinsicSingularLocus_eq_empty X,
      hrmod.interior_preimage_eq_empty (interior_intrinsicSingularLocus_eq_empty X), ?_⟩
    simpa only [intrinsicSingularLocus, compl_compl] using hriso
  refine ⟨Z, ρ, N, n, D,
    (fun i => (geoTransformAlong
      (⟨univ, [], originalSingularGermIdeal X (j i ≫ p), 1⟩ : MarkedIdeal (n i) (M i)) (T i)).E),
    (fun i => exceptionalDivisor (T i)), L, hρ, hrmod, hZ, hrres,
    hrmod.isProperMap, hrmod.surjective, hriso, hDcompact, hL, hLclosed, hLIcover, hLdisj, ?_⟩
  intro i
  refine ⟨hE i, hsupp i, ?_, ?_⟩
  · ext x
    have hpt := congrArg (fun F : A i ⟶ X => F.hom.left.base x)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun F : A i ⟶ Y => F ≫ p) (hLc i)))
    change x.val ∈ (exceptionalDivisor (T i)).support ↔
      (ρ ≫ p).hom.left.base ((L i).hom.left.base x) ∈ intrinsicSingularLocus X.obj
    rw [hpre i]
    change (q i ≫ (j i ≫ p)).hom.left.base x ∈ intrinsicSingularLocus X.obj ↔ _
    exact (congrArg (fun y => y ∈ intrinsicSingularLocus X.obj) hpt).symm.to_iff
  · intro x
    have hh := hwhole i x
    have he : L i ≫ (ρ ≫ p) = q i ≫ (j i ≫ p) := by
      rw [← Category.assoc, hLc i, Category.assoc]
    exact he.symm ▸ hh

end CompactNative

/-- Every compact original reduced complex space has an existential strong
resolution with the entire original singular ideal and all native SNC traces.
The canonical smooth-functorial assignment is a separate theorem. -/
theorem exists_compact_native_strong_resolution (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    ∃ (Z : SourceReducedComplexSpace) (r : Z ⟶ X) (N : ℕ) (n : Fin N → ℕ)
      (D : ∀ i, CMfd.{0} (n i)) (E : ∀ i, List (Set (D i)))
      (Δ : ∀ i, EffectiveDivisor (n i) (D i))
      (L : ∀ i, wholeModel (n := n i) (D i) ⟶ Z),
      IsModification r ∧ Z.IsSmooth ∧ IsResolution r ∧
      IsProperMap r.hom.left.base ∧ Function.Surjective r.hom.left.base ∧
      IsIsoOver r (intrinsicRegularLocus X.obj) ∧
      (∀ i, CompactSpace (D i)) ∧
      (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) ∧
      (∀ i, IsClosedEmbedding (L i).hom.left.base) ∧
      (∀ z : Z.obj.left, ∃ (i : Fin N) (x : (wholeModel (n := n i) (D i)).obj.left),
        (L i).hom.left.base x = z) ∧
      Pairwise (fun i k => Disjoint (range (L i).hom.left.base) (range (L k).hom.left.base)) ∧
      ∀ i, IsSNCDivisor (n i) (E i) ∧ (Δ i).support = ⋃ H ∈ E i, H ∧
        (Subtype.val : ↥(univ : Set (D i)) → D i) ⁻¹' (Δ i).support =
          (L i).hom.left.base ⁻¹' (r.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) ∧
        ∀ x : (univ : Set (D i)),
          Ideal.map ((actualSubspaceInclusion (n := n i) (univ : Set (D i))).stalkMap x).hom
            (actualWholeSheafStalkIdeal (Δ i).ideal x.val) =
            nativePulledIdealStalkIdeal (L i ≫ r).hom.left
              (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
              (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  obtain ⟨Y, p, hp, hY⟩ := HironakaG11PresUnconditional.compactSingularCentreResolution X inferInstance
  let : CompactSpace Y.obj.left := hp.source_compact
  obtain ⟨Z, ρ, N, n, D, E, Δ, L, _hρ, hrest⟩ :=
    exists_compact_native_strong_refinement p hp hY
  exact ⟨Z, ρ ≫ p, N, n, D, E, Δ, L, hrest⟩

end
end SGPT.Unibranch.HironakaG1CompactNativeSingularCleanup
