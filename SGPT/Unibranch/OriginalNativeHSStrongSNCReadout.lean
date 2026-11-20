import SGPT.Unibranch.OriginalNativeHSStrongIdealReadout
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsLocalBranches

/-! Genuine restricted saturated SNC charts of the SAME prescribed recipe.
Blueprint FIRST: original-native-hs-strong-snc-readout.tex.
No new principalization, source, component models or supplied chart/ideal packet. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.OriginalNativeHSStrongSNCReadout
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaEmbeddedNativeMorphism
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalTerminalAtlas
  HironakaOriginalTerminalManifold HironakaOriginalTerminalLocalBiholomorphism HironakaOriginalGlobalPrincipalization
  HironakaOriginalGlobalSNCPrincipalization HironakaNormalCrossingsLocalBranches
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  HironakaG1OriginalSingularCleanup OriginalNativeHSStrongFiniteRecipe

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable (X : SourceReducedComplexSpace) (U : Opens X.obj.left)
  (hU : IsCompact (closure (U : Set X.obj.left)))

private abbrev p := initialProjection X U hU
private abbrev hp := initialResolution X U hU
private abbrev dimension (c : ConnectedComponents (initialState X U hU).source.obj.left) :=
  HironakaG1NativeStrongCleanup.componentDimension (p X U hU) (hp X U hU) c
private abbrev model (c : ConnectedComponents (initialState X U hU).source.obj.left) :=
  HironakaG1NativeStrongCleanup.componentManifold (p X U hU) (hp X U hU) c
private abbrev oldModelMap (c : ConnectedComponents (initialState X U hU).source.obj.left) :=
  HironakaG1NativeStrongCleanup.componentModelMap (p X U hU) (hp X U hU) c
private abbrev oldComponent (c : ConnectedComponents (initialState X U hU).source.obj.left) :=
  HironakaG1NativeStrongCleanup.cleanupComponent (p X U hU) (hp X U hU) c
private abbrev componentMap (c : ConnectedComponents (initialState X U hU).source.obj.left) :=
  HironakaG1NativeStrongCleanup.strongComponentInclusion (p X U hU) (hp X U hU) c

private theorem modelMap_open (c : ConnectedComponents (initialState X U hU).source.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (oldModelMap X U hU c).hom.left := by
  have hi : ∀ {A B C : SourceReducedComplexSpace} (e : A ≅ B) (f : B ⟶ C),
      LocallyRingedSpace.IsOpenImmersion f.hom.left →
        LocallyRingedSpace.IsOpenImmersion (e.hom ≫ f).hom.left := by
    intro A B C e f hf
    let := hf
    have he : LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft e).hom
      infer_instance
    let := he
    change LocallyRingedSpace.IsOpenImmersion (_ ≫ _)
    infer_instance
  unfold oldModelMap HironakaG1NativeStrongCleanup.componentModelMap
  apply hi
  infer_instance

private theorem originalIdeal_thin (c : ConnectedComponents (initialState X U hU).source.obj.left) :
    interior (originalSingularGermIdeal (initialState X U hU).base
      (oldModelMap X U hU c ≫ p X U hU)).zeroLocus = ∅ := by
  obtain ⟨_, E, _, _, hpre, hiso⟩ := (hp X U hU).2
  have ht := hiso.interior_preimage_eq_empty hpre
    (interior_intrinsicSingularLocus_eq_empty (initialState X U hU).base)
  have hs := (modelMap_open X U hU c).base_open.isOpenMap.preimage_interior_eq_interior_preimage
    (oldModelMap X U hU c).hom.left.base.hom.continuous
    ((p X U hU).hom.left.base ⁻¹' intrinsicSingularLocus (initialState X U hU).base.obj)
  have hcomp : interior ((oldModelMap X U hU c).hom.left.base ⁻¹'
      ((p X U hU).hom.left.base ⁻¹' intrinsicSingularLocus (initialState X U hU).base.obj)) = ∅ :=
    hs.symm.trans (by rw [ht, preimage_empty])
  rw [originalSingularGermIdeal_zeroLocus]
  change interior ((Homeomorph.Set.univ (model X U hU c)).symm ⁻¹'
    ((oldModelMap X U hU c).hom.left.base ⁻¹'
      ((p X U hU).hom.left.base ⁻¹' intrinsicSingularLocus (initialState X U hU).base.obj))) = ∅
  have he := congrArg (fun S : Set (wholeModel (n := dimension X U hU c) (model X U hU c)).obj.left =>
    (Homeomorph.Set.univ (model X U hU c)).symm ⁻¹' S) hcomp
  exact ((Homeomorph.Set.univ (model X U hU c)).symm.preimage_interior _).symm.trans
    (he.trans (preimage_empty))

private abbrev marked (c : ConnectedComponents (initialState X U hU).source.obj.left) :
    MarkedIdeal (dimension X U hU c) (model X U hU c) :=
  ⟨univ, [], originalSingularGermIdeal (initialState X U hU).base (oldModelMap X U hU c ≫ p X U hU), 1⟩
private theorem domain (c : ConnectedComponents (initialState X U hU).source.obj.left) :
    ResolutionInvariantSpec.IsInvDomain (dimension X U hU c) (marked X U hU c) :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (originalSingularGermIdeal_coherent (initialState X U hU).base (oldModelMap X U hU c ≫ p X U hU))
    (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
      (originalSingularGermIdeal_coherent (initialState X U hU).base (oldModelMap X U hU c ≫ p X U hU))
      (originalIdeal_thin X U hU c))
    (isSNCDivisor_nil (n := dimension X U hU c) (M := model X U hU c))

/-- The SAME old actual saturated terminal range, with no new choice. -/
def rangeOpen (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : Opens (oldComponent X U hU c) :=
  originalTerminalLocalRangeOpen (marked X U hU c) (domain X U hU c) i

/-- Its full native map to the SAME old strong source. -/
def rangeMap (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : wholeModel (n := dimension X U hU c) (rangeOpen X U hU c i) ⟶
      strongSource X U hU :=
  nativeMorphism (M := rangeOpen X U hU c i) (N := oldComponent X U hU c) contMDiff_subtype_val ≫
    componentMap X U hU c

/-- The SAME old entire effective divisor on that range. -/
def rangeDivisor (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : EffectiveDivisor (dimension X U hU c) (rangeOpen X U hU c i) :=
  originalTerminalRangePrincipalizationDivisor (marked X U hU c) (domain X U hU c) rfl rfl i

/-- The ENTIRE ordered old terminal boundary. -/
def rangeBoundary (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : List (Set (rangeOpen X U hU c i)) :=
  originalTerminalRangeBoundary (marked X U hU c) (domain X U hU c) i

/-- The genuine open trace of the prescribed inverse source in that old range. -/
def chartOpen (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : Opens (rangeOpen X U hU c i) where
  carrier := {x | (rangeMap X U hU c i).hom.left.base (modelPoint x) ∈
    OriginalRelativelyCompactRestriction.preimageOpen (prescribedOpen X U hU) (strongProjection X U hU)}
  is_open' := (OriginalRelativelyCompactRestriction.preimageOpen
    (prescribedOpen X U hU) (strongProjection X U hU)).isOpen.preimage
      ((rangeMap X U hU c i).hom.left.base.hom.continuous.comp (continuous_id.subtype_mk _))

/-- The actual restricted chart into the OLD strong source. -/
def chartToOld (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : wholeModel (n := dimension X U hU c) (chartOpen X U hU c i) ⟶
      strongSource X U hU :=
  nativeMorphism (M := chartOpen X U hU c i) (N := rangeOpen X U hU c i) contMDiff_subtype_val ≫
    rangeMap X U hU c i

private theorem openVal_isOpenImmersion {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (O : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (nativeMorphism (n := n) (m := n) (M := O) (N := M) contMDiff_subtype_val).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) (univ : Set M) O)
  infer_instance

private theorem rangeMap_open (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : LocallyRingedSpace.IsOpenImmersion (rangeMap X U hU c i).hom.left := by
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (nativeMorphism (n := dimension X U hU c) (m := dimension X U hU c)
      (M := rangeOpen X U hU c i) (N := oldComponent X U hU c) contMDiff_subtype_val).hom.left
    (openVal_isOpenImmersion (n := dimension X U hU c) (rangeOpen X U hU c i))
    (componentMap X U hU c).hom.left
    (((HironakaG1NativeStrongCleanup.strong_component_cover (p X U hU) (hp X U hU)).1 c).1)

private theorem chartToOld_open (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : LocallyRingedSpace.IsOpenImmersion (chartToOld X U hU c i).hom.left := by
  let := openVal_isOpenImmersion (n := dimension X U hU c) (chartOpen X U hU c i)
  let := rangeMap_open X U hU c i
  change LocallyRingedSpace.IsOpenImmersion (_ ≫ _)
  infer_instance

private theorem chart_lift (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) :
    ∃ k : wholeModel (n := dimension X U hU c) (chartOpen X U hU c i) ⟶ source X U hU,
      LocallyRingedSpace.IsOpenImmersion k.hom.left ∧
        k ≫ sourceInclusion X U hU = chartToOld X U hU c i := by
  apply OriginalNativeSmoothOpenLocality.exists_native_open_lift
    (sourceInclusion X U hU) (chartToOld X U hU c i)
    (sourceInclusion_isOpenImmersion X U hU) (chartToOld_open X U hU c i)
  rintro _ ⟨x, rfl⟩
  change (chartToOld X U hU c i).hom.left.base x ∈
    range (OriginalRelativelyCompactRestriction.inclusion _ _ _).hom.left.base
  rw [OriginalRelativelyCompactRestriction.inclusion_range]
  exact x.val.property

/-- The actual full native lift to the LITERAL prescribed source. -/
def chartMap (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : wholeModel (n := dimension X U hU c) (chartOpen X U hU c i) ⟶
      source X U hU := Classical.choose (chart_lift X U hU c i)

theorem chartMap_isOpenImmersion (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : LocallyRingedSpace.IsOpenImmersion (chartMap X U hU c i).hom.left :=
  (Classical.choose_spec (chart_lift X U hU c i)).1

/-- Full original structure-sheaf factorization, not just a point square. -/
theorem chartMap_square (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : chartMap X U hU c i ≫ sourceInclusion X U hU = chartToOld X U hU c i :=
  (Classical.choose_spec (chart_lift X U hU c i)).2

theorem chartMap_scalar (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) :
    (chartMap X U hU c i).hom.left ≫ (source X U hU).obj.hom =
      (wholeModel (n := dimension X U hU c) (chartOpen X U hU c i)).obj.hom :=
  Over.w (chartMap X U hU c i).hom

/-- Genuine actual native coverage of EVERY point of the SAME prescribed source. -/
theorem chart_cover (y : (source X U hU).obj.left) :
    ∃ (c : ConnectedComponents (initialState X U hU).source.obj.left) (i : model X U hU c)
      (z : (wholeModel (n := dimension X U hU c) (chartOpen X U hU c i)).obj.left),
      (chartMap X U hU c i).hom.left.base z = y := by
  obtain ⟨c, u, hu⟩ := (HironakaG1NativeStrongCleanup.strong_component_cover
    (p X U hU) (hp X U hU)).2.1 ((sourceInclusion X U hU).hom.left.base y)
  obtain ⟨i, hi⟩ := (HironakaG1NativeStrongCleanup.strong_saturated_range_readout
    (p X U hU) (hp X U hU) c).1 u.val
  let a : rangeOpen X U hU c i := ⟨u.val, hi⟩
  have ha : (rangeMap X U hU c i).hom.left.base (modelPoint a) =
      (sourceInclusion X U hU).hom.left.base y := by
    change (componentMap X U hU c).hom.left.base (modelPoint u.val) = _
    exact hu
  have hmem : a ∈ chartOpen X U hU c i := by
    change (rangeMap X U hU c i).hom.left.base (modelPoint a) ∈
      OriginalRelativelyCompactRestriction.preimageOpen
        (prescribedOpen X U hU) (strongProjection X U hU)
    rw [ha]
    exact y.property
  let z : chartOpen X U hU c i := ⟨a, hmem⟩
  refine ⟨c, i, modelPoint z, ?_⟩
  apply (sourceInclusion_isOpenImmersion X U hU).base_open.injective
  have hs := congrArg (fun f => f.hom.left.base (modelPoint z)) (chartMap_square X U hU c i)
  exact hs.trans ha

/-- Actual restricted effective divisor, with the entire old ideal. -/
def divisor (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : EffectiveDivisor (dimension X U hU c) (chartOpen X U hU c i) :=
  restrictDivisor (rangeDivisor X U hU c i) (chartOpen X U hU c i)

/-- ENTIRE ordered boundary, retaining every empty trace and original position. -/
def boundary (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : List (Set (chartOpen X U hU c i)) :=
  (rangeBoundary X U hU c i).map ((Subtype.val : chartOpen X U hU c i → rangeOpen X U hU c i) ⁻¹' ·)

theorem boundary_snc (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : IsSNCDivisor (dimension X U hU c) (boundary X U hU c i) :=
  NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val (chartOpen X U hU c i)) continuous_subtype_val
    ((HironakaG1NativeStrongCleanup.strong_saturated_range_readout (p X U hU) (hp X U hU) c).2 i).2.2.2.2.1

theorem divisor_support (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) : (divisor X U hU c i).support = ⋃ H ∈ boundary X U hU c i, H := by
  rw [divisor, support_restrictDivisor]
  have hs : (rangeDivisor X U hU c i).support = ⋃ H ∈ rangeBoundary X U hU c i, H :=
    ((HironakaG1NativeStrongCleanup.strong_saturated_range_readout
      (p X U hU) (hp X U hU) c).2 i).2.2.2.2.2.1
  change (Subtype.val : chartOpen X U hU c i → rangeOpen X U hU c i) ⁻¹'
    (rangeDivisor X U hU c i).support = _
  rw [hs]
  ext z
  simp only [boundary, mem_preimage, mem_iUnion, List.mem_map]
  constructor
  · rintro ⟨H, hH, hz⟩
    exact ⟨_, ⟨H, hH, rfl⟩, hz⟩
  · rintro ⟨_, ⟨H, hH, rfl⟩, hz⟩
    exact ⟨H, hH, hz⟩

theorem divisor_original_support (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) :
    (divisor X U hU c i).support = {z |
      (chartMap X U hU c i ≫ projection X U hU).hom.left.base (modelPoint z) ∈
        intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj} := by
  rw [divisor, support_restrictDivisor]
  have hs : (rangeDivisor X U hU c i).support = {z : rangeOpen X U hU c i |
      (rangeMap X U hU c i ≫ strongProjection X U hU).hom.left.base (modelPoint z) ∈
        intrinsicSingularLocus (initialState X U hU).base.obj} :=
    ((HironakaG1NativeStrongCleanup.strong_saturated_range_readout
      (p X U hU) (hp X U hU) c).2 i).2.2.2.2.2.2
  change (Subtype.val : chartOpen X U hU c i → rangeOpen X U hU c i) ⁻¹'
    (rangeDivisor X U hU c i).support = _
  rw [hs]
  ext z
  have hSing := Set.ext_iff.mp (OriginalNativeHSStrongIdealReadout.singular_preimage X U hU)
    ((chartMap X U hU c i).hom.left.base (modelPoint z))
  have hsq := congrArg (fun f => f.hom.left.base (modelPoint z)) (chartMap_square X U hU c i)
  exact (iff_of_eq (congrArg (fun t => (strongProjection X U hU).hom.left.base t ∈
    intrinsicSingularLocus (initialState X U hU).base.obj) hsq.symm)).trans hSing.symm

/-- ENTIRE divisor ideal at the SAME actual native chart/projection stalk. -/
theorem wholeStalk (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) (x : (univ : Set (chartOpen X U hU c i))) :
    Ideal.map ((actualSubspaceInclusion (n := dimension X U hU c)
      (univ : Set (chartOpen X U hU c i))).stalkMap x).hom
      (actualWholeSheafStalkIdeal (divisor X U hU c i).ideal x.val) =
    nativePulledIdealStalkIdeal (chartMap X U hU c i ≫ projection X U hU).hom.left
      (intrinsicReducedCentreIdealModule (OriginalRelativelyCompactRestriction.restriction X U hU).obj.left
        (intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj))
      (intrinsicReducedCentreIdealInclusion (OriginalRelativelyCompactRestriction.restriction X U hU).obj.left
        (intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj)) x := by
  let v := nativeMorphism (n := dimension X U hU c) (m := dimension X U hU c) (M := chartOpen X U hU c i) (N := rangeOpen X U hU c i) contMDiff_subtype_val
  let J := intrinsicReducedCentreIdealModule (initialState X U hU).base.obj.left
    (intrinsicSingularLocus (initialState X U hU).base.obj)
  let b := intrinsicReducedCentreIdealInclusion (initialState X U hU).base.obj.left
    (intrinsicSingularLocus (initialState X U hU).base.obj)
  let J' := intrinsicReducedCentreIdealModule (OriginalRelativelyCompactRestriction.restriction X U hU).obj.left
    (intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj)
  let b' := intrinsicReducedCentreIdealInclusion (OriginalRelativelyCompactRestriction.restriction X U hU).obj.left
    (intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj)
  have hold : Ideal.map ((actualSubspaceInclusion (n := dimension X U hU c)
      (univ : Set (rangeOpen X U hU c i))).stalkMap (v.hom.left.base x)).hom
      (actualWholeSheafStalkIdeal (rangeDivisor X U hU c i).ideal (v.hom.left.base x).val) =
      nativePulledIdealStalkIdeal ((rangeMap X U hU c i).hom.left ≫
        (strongProjection X U hU).hom.left) J b (v.hom.left.base x) := by
    exact HironakaG1NativeStrongCleanup.strong_range_wholeStalk
      (p X U hU) (hp X U hU) c i (v.hom.left.base x)
  have hpull := HironakaSingularSubspaceBlowupCartier.map_actualSubspace_stalk_ideal_pullback
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ, ComplexModel (dimension X U hU c))
      𝓘(ℂ, ComplexModel (dimension X U hU c)) ∞
        (Subtype.val : chartOpen X U hU c i → rangeOpen X U hU c i))
    (fun _ (_ : _ ∈ (univ : Set (chartOpen X U hU c i))) => mem_univ _)
    (rangeDivisor X U hU c i).ideal
    (DivisorMetric.isCoherent_of_isInvertible (rangeDivisor X U hU c i).isInvertible) x
  have hfinal := congrArg (Ideal.map ((chartMap X U hU c i).hom.left.stalkMap x).hom)
    (OriginalNativeHSStrongIdealReadout.wholeStalk X U hU ((chartMap X U hU c i).hom.left.base x))
  have hnew : nativePulledIdealStalkIdeal
      ((chartMap X U hU c i).hom.left ≫ (projection X U hU).hom.left) J' b' x =
      nativePulledIdealStalkIdeal
        ((chartMap X U hU c i).hom.left ≫ (sourceInclusion X U hU).hom.left)
        (OriginalNativeHSStrongIdealReadout.oldTotalIdeal X U hU)
        (OriginalNativeHSStrongIdealReadout.oldTotalInclusion X U hU) x :=
    (nativePulledIdealStalkIdeal_comp J' b'
      (chartMap X U hU c i).hom.left (projection X U hU).hom.left x).trans
      (hfinal.trans (nativePulledIdealStalkIdeal_comp
        (OriginalNativeHSStrongIdealReadout.oldTotalIdeal X U hU)
        (OriginalNativeHSStrongIdealReadout.oldTotalInclusion X U hU)
        (chartMap X U hU c i).hom.left (sourceInclusion X U hU).hom.left x).symm)
  have hsquare : (chartMap X U hU c i).hom.left ≫ (sourceInclusion X U hU).hom.left =
      (chartToOld X U hU c i).hom.left :=
    congrArg (fun f => f.hom.left) (chartMap_square X U hU c i)
  have ha := hpull.symm.trans (congrArg (Ideal.map (v.hom.left.stalkMap x).hom) hold)
  have hb := (nativePulledIdealStalkIdeal_comp J b v.hom.left
    ((rangeMap X U hU c i).hom.left ≫ (strongProjection X U hU).hom.left) x).symm
  have hc := congrArg
    (fun f : (wholeModel (n := dimension X U hU c) (chartOpen X U hU c i)).obj.left ⟶
      (initialState X U hU).base.obj.left => nativePulledIdealStalkIdeal f J b x)
    (Category.assoc v.hom.left (rangeMap X U hU c i).hom.left (strongProjection X U hU).hom.left).symm
  have hd := (HironakaNativePulledIdealComposition.stalkIdeal_comp
    (strongProjection X U hU).hom.left (chartToOld X U hU c i).hom.left J b x).symm
  have he := congrArg
    (fun f : (wholeModel (n := dimension X U hU c) (chartOpen X U hU c i)).obj.left ⟶
      (strongSource X U hU).obj.left => nativePulledIdealStalkIdeal f
        (OriginalNativeHSStrongIdealReadout.oldTotalIdeal X U hU)
        (OriginalNativeHSStrongIdealReadout.oldTotalInclusion X U hU) x) hsquare.symm
  exact ha.trans (hb.trans (hc.trans (hd.trans (he.trans hnew.symm))))

/-- The SAME whole ideal has actual adapted holomorphic unit-monomial generators. -/
theorem unit_monomial_generator (c : ConnectedComponents (initialState X U hU).source.obj.left)
    (i : model X U hU c) (x : chartOpen X U hU c i) :
    ∃ O : Set (chartOpen X U hU c i), IsOpen O ∧ x ∈ O ∧ ∃ g : chartOpen X U hU c i → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (dimension X U hU c)) 𝓘(ℂ, ℂ) g O ∧
      (∀ W : Set (chartOpen X U hU c i), IsOpen W → W ⊆ O → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ O, ∀ f : chartOpen X U hU c i → ℂ,
        (divisor X U hU c i).ideal.mem y f ↔ IsInSpanAt (n := dimension X U hU c) (· = g) y f) ∧
      ∃ (S : Fin (boundary X U hU c i).length → Finset (Fin (dimension X U hU c)))
        (Φ : LocalHolomorphicEquivAt (n := dimension X U hU c)
          ((complexChartAt (n := dimension X U hU c) x).val x)),
        Φ.source ⊆ (complexChartAt (n := dimension X U hU c) x).val.target ∧
        Φ.toFun ((complexChartAt (n := dimension X U hU c) x).val x) = 0 ∧
        (∀ j, x ∈ (boundary X U hU c i).get j → (S j).card = 1) ∧
        Set.InjOn S {j | x ∈ (boundary X U hU c i).get j} ∧
        (∀ j, x ∈ (boundary X U hU c i).get j → ∀ {y : chartOpen X U hU c i},
          y ∈ (complexChartAt (n := dimension X U hU c) x).val.source →
          (complexChartAt (n := dimension X U hU c) x).val y ∈ Φ.source →
          (y ∈ (boundary X U hU c i).get j ↔
            Φ.toFun ((complexChartAt (n := dimension X U hU c) x).val y) ∈ coordSubspace (S j))) ∧
        ∃ (a : Fin (dimension X U hU c) → ℕ) (H : ComplexModel (dimension X U hU c) → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := dimension X U hU c) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin (dimension X U hU c), z j ^ a j :=
  SNCDivisorLocalGenerator.exists_adapted_unit_monomial_generator
    (divisor X U hU c i) (boundary X U hU c i) (boundary_snc X U hU c i) (divisor_support X U hU c i) x

end
end SGPT.Unibranch.OriginalNativeHSStrongSNCReadout
