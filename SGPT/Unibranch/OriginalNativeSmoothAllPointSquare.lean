import SGPT.Unibranch.OriginalNativeSmoothCanonicalSquare
import SGPT.Unibranch.OriginalLocalCanonicalResolutionCover
import SGPT.Unibranch.HironakaG11ModificationCalculus

/-! Genuine regular-image identity windows and all-point local native
resolution squares, with actual regular/canonical provenance retained.
Blueprint first: `original-native-smooth-all-point-square.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalNativeSmoothAllPointSquare
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaEmbeddedAnalytic HironakaResolutionSpace
  SourceReducedComplexSpace OriginalNativeSmoothLocalProduct OriginalNativeSmoothSingularLocus
  OriginalLocalCanonicalStrictResolution OriginalLocalCanonicalResolutionCover
  OriginalNativeSmoothCanonicalSquare

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {x : X.obj.left}
  {V : Opens X.obj.left} {T : Opens Y.obj.left}

theorem identity_resolution_properties (Z : SourceReducedComplexSpace) (hZ : Z.IsSmooth)
    {O : Set Z.obj.left} (hO : IsOpen O) :
    IsResolution (𝟙 Z) ∧ Function.Surjective (𝟙 Z : Z ⟶ Z).hom.left.base ∧
      IsProperMap (𝟙 Z : Z ⟶ Z).hom.left.base ∧ IsIsoOver (𝟙 Z) O := by
  have hp : IsProperMap (𝟙 Z : Z ⟶ Z).hom.left.base := isProperMap_id
  have hb : IsProperBimeromorphic (𝟙 Z) := by
    refine ⟨hp,∅,isAnalyticSubset_empty,by simp,by simp,?_⟩
    exact IsIsoOver.id_of_isOpen Z (by simp)
  exact ⟨⟨hZ,hb⟩,Function.surjective_id,hp,IsIsoOver.id_of_isOpen Z hO⟩

/-- Actual regular-window OUTPUT; its native factor is internally constructed below. -/
structure RegularWindow (f : X ⟶ Y) (x : X.obj.left)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) where
  sourceChart : LocalEmbedding X
  targetChart : LocalEmbedding Y
  sourceWhole : sourceChart.carrier = univ
  targetWhole : targetChart.carrier = univ
  sourceOpen : Opens sourceChart.ambient
  sourcePoint : windowCarrier sourceChart sourceOpen
  point : (windowMorphism sourceChart sourceOpen).hom.left.base sourcePoint = x
  map : windowSpace sourceChart sourceOpen ⟶ OriginalNativeProductWindow.chartSpace targetChart
  square : windowMorphism sourceChart sourceOpen ≫ f = map ≫ OriginalNativeProductWindow.chartInclusion targetChart
  source_range : range (windowMorphism sourceChart sourceOpen).hom.left.base ⊆ (V : Set X.obj.left)
  target_range : range targetChart.toPoint ⊆ (T : Set Y.obj.left)

/-- Original regularity at the image and ordinary smoothness produce both actual windows. -/
theorem exists_regular_window (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (hreg : f.hom.left.base x ∈ intrinsicRegularLocus Y.obj)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    Nonempty (RegularWindow f x V T) := by
  have hxReg := (smoothAt_regular_iff f x hsm).mpr hreg
  obtain ⟨eS,cS,hcS,heV,hWholeS⟩ := exists_whole_localEmbedding_of_regular X x hxReg V hxV
  obtain ⟨eT,cT,hcT,heT,hWholeT⟩ := exists_whole_localEmbedding_of_regular Y (f.hom.left.base x) hreg T hfxT
  let Q : Opens eS.carrier :=
    ⟨(fun c => f.hom.left.base (eS.toPoint c)) ⁻¹' range eT.toPoint,
      eT.isOpenEmbedding_toPoint.isOpen_range.preimage
        (f.hom.left.base.hom.continuous.comp eS.isOpenEmbedding_toPoint.continuous)⟩
  have hcSQ : cS ∈ Q := by
    change f.hom.left.base (eS.toPoint cS) ∈ range eT.toPoint
    exact ⟨cT,hcT.trans (congrArg f.hom.left.base hcS).symm⟩
  obtain ⟨Pset,hPset,hPtrace⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let P : Opens eS.ambient := ⟨Pset,hPset⟩
  have hcSP : cS.val ∈ P := by
    change cS ∈ (Subtype.val : eS.carrier → eS.ambient) ⁻¹' Pset
    rw [hPtrace]
    exact hcSQ
  let jS := windowMorphism eS P
  let jT := eT.map
  let g := jS.hom.left ≫ f.hom.left
  have hr : range g.base ⊆ range jT.base := by
    rintro _ ⟨z,rfl⟩
    let c : eS.carrier := ⟨z.val.val,z.property⟩
    have hc : c ∈ (Subtype.val : eS.carrier → eS.ambient) ⁻¹' Pset := z.val.property
    have hq := (Set.ext_iff.mp hPtrace c).mp hc
    exact hq
  let : LocallyRingedSpace.IsOpenImmersion jT := eT.isOpenImmersion
  let l := LocallyRingedSpace.IsOpenImmersion.lift jT g hr
  have hfac : l ≫ jT = g := LocallyRingedSpace.IsOpenImmersion.lift_fac jT g hr
  have hscalar : l ≫ (OriginalNativeProductWindow.chartSpace eT).obj.hom =
      (windowSpace eS P).obj.hom := by
    exact (congrArg (fun a => l ≫ a) eT.overPoint.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ Y.obj.hom) hfac).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun a => jS.hom.left ≫ a) (Over.w f.hom)).trans (Over.w jS.hom)))))
  let q : windowSpace eS P ⟶ OriginalNativeProductWindow.chartSpace eT :=
    ObjectProperty.homMk (Over.homMk l hscalar)
  have hsq : jS ≫ f = q ≫ OriginalNativeProductWindow.chartInclusion eT := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hfac.symm
  let s : windowCarrier eS P := ⟨⟨cS.val,hcSP⟩,cS.property⟩
  refine ⟨⟨eS,eT,hWholeS,hWholeT,P,s,hcS,q,hsq,?_,heT⟩⟩
  rintro _ ⟨z,rfl⟩
  exact heV ⟨⟨z.val.val,z.property⟩,rfl⟩

namespace RegularWindow
variable (r : RegularWindow f x V T)

theorem sourceCarrier_eq_univ : windowCarrier r.sourceChart r.sourceOpen = univ := by
  simp only [windowCarrier,r.sourceWhole,Set.preimage_univ]

theorem source_isSmooth : (windowSpace r.sourceChart r.sourceOpen).IsSmooth := by
  have hSM : IsClosedSubmanifold r.sourceChart.dim
      (univ : Set r.sourceOpen) :=
    ⟨isClosed_univ,fun z _ => ⟨r.sourceChart.dim,AnalyticIrreducibleComponents.regularAtDim_univ z⟩⟩
  apply isSmooth_ofClosedAnalytic_of_isClosedSubmanifold
  exact (sourceCarrier_eq_univ r).symm ▸ hSM

theorem target_isSmooth : (OriginalNativeProductWindow.chartSpace r.targetChart).IsSmooth := by
  have hSM : IsClosedSubmanifold r.targetChart.dim (univ : Set r.targetChart.ambient) :=
    ⟨isClosed_univ,fun z _ => ⟨r.targetChart.dim,AnalyticIrreducibleComponents.regularAtDim_univ z⟩⟩
  apply isSmooth_ofClosedAnalytic_of_isClosedSubmanifold
  exact r.targetWhole.symm ▸ hSM

/-- Both actual ambient histories are literal refl towers, with full strict geometry. -/
theorem zero_stages :
    (BlowupTowers.BlowupTower.refl : BlowupTowers.BlowupTower
      (BlowupTowers.CMfd.of (n := r.sourceChart.dim) r.sourceOpen)
      (BlowupTowers.CMfd.of (n := r.sourceChart.dim) r.sourceOpen)).length = 0 ∧
    (BlowupTowers.BlowupTower.refl : BlowupTowers.BlowupTower
      (BlowupTowers.CMfd.of (n := r.targetChart.dim) r.targetChart.ambient)
      (BlowupTowers.CMfd.of (n := r.targetChart.dim) r.targetChart.ambient)).length = 0 ∧
    IsStrictTransformResolution r.sourceChart.dim (windowCarrier r.sourceChart r.sourceOpen)
      (id : r.sourceOpen → r.sourceOpen) [] ∧
    IsStrictTransformResolution r.targetChart.dim r.targetChart.carrier
      (id : r.targetChart.ambient → r.targetChart.ambient) [] := by
  refine ⟨rfl,rfl,?_,?_⟩
  · exact (sourceCarrier_eq_univ r).symm ▸
      whole_refl_strictResolution (BlowupTowers.CMfd.of (n := r.sourceChart.dim) r.sourceOpen)
  · exact r.targetWhole.symm ▸
      whole_refl_strictResolution (BlowupTowers.CMfd.of (n := r.targetChart.dim) r.targetChart.ambient)

theorem source_properties :
    IsResolution (𝟙 (windowSpace r.sourceChart r.sourceOpen)) ∧
      Function.Surjective (𝟙 (windowSpace r.sourceChart r.sourceOpen) : _ ⟶ _).hom.left.base ∧
      IsProperMap (𝟙 (windowSpace r.sourceChart r.sourceOpen) : _ ⟶ _).hom.left.base ∧
      IsIsoOver (𝟙 (windowSpace r.sourceChart r.sourceOpen))
        ((windowMorphism r.sourceChart r.sourceOpen).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
  identity_resolution_properties _ (source_isSmooth r)
    ((isOpen_intrinsicRegularLocus X.obj).preimage
      (windowMorphism r.sourceChart r.sourceOpen).hom.left.base.hom.continuous)

theorem target_properties :
    IsResolution (𝟙 (OriginalNativeProductWindow.chartSpace r.targetChart)) ∧
      Function.Surjective (𝟙 (OriginalNativeProductWindow.chartSpace r.targetChart) : _ ⟶ _).hom.left.base ∧
      IsProperMap (𝟙 (OriginalNativeProductWindow.chartSpace r.targetChart) : _ ⟶ _).hom.left.base ∧
      IsIsoOver (𝟙 (OriginalNativeProductWindow.chartSpace r.targetChart))
        ((OriginalNativeProductWindow.chartInclusion r.targetChart).hom.left.base ⁻¹' intrinsicRegularLocus Y.obj) :=
  identity_resolution_properties _ (target_isSmooth r)
    ((isOpen_intrinsicRegularLocus Y.obj).preimage
      (OriginalNativeProductWindow.chartInclusion r.targetChart).hom.left.base.hom.continuous)

end RegularWindow

/-- Actual construction provenance, with no arbitrary comparison or endpoint fields. -/
inductive LocalSquare (f : X ⟶ Y) (x : X.obj.left) (V : Opens X.obj.left) (T : Opens Y.obj.left) where
  | regular : RegularWindow f x V T → LocalSquare f x V T
  | singular : LocalCanonicalPullback f x V T → LocalSquare f x V T

theorem exists_local_square (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    Nonempty (LocalSquare f x V T) := by
  by_cases hreg : f.hom.left.base x ∈ intrinsicRegularLocus Y.obj
  · obtain ⟨r⟩ := exists_regular_window f x hsm hreg V T hxV hfxT
    exact ⟨.regular r⟩
  · obtain ⟨a⟩ := exists_local_canonical_pullback f x hsm hreg V T hxV hfxT
    exact ⟨.singular a⟩

namespace LocalSquare
variable (a : LocalSquare f x V T)

def sourceBase : SourceReducedComplexSpace := match a with
  | .regular r => windowSpace r.sourceChart r.sourceOpen
  | .singular c => sourceSpace c.window c.neighbourhood

def targetBase : SourceReducedComplexSpace := match a with
  | .regular r => OriginalNativeProductWindow.chartSpace r.targetChart
  | .singular c => targetSpace c.window c.neighbourhood

def sourceResolved : SourceReducedComplexSpace := match a with
  | .regular r => windowSpace r.sourceChart r.sourceOpen
  | .singular c => c.sourceStrictSpace

def targetResolved : SourceReducedComplexSpace := match a with
  | .regular r => OriginalNativeProductWindow.chartSpace r.targetChart
  | .singular c => c.targetStrictSpace

def sourceInclusion : sourceBase a ⟶ X := match a with
  | .regular r => windowMorphism r.sourceChart r.sourceOpen
  | .singular c => OriginalNativeSmoothCanonicalSquare.sourceInclusion c.window c.neighbourhood

def targetInclusion : targetBase a ⟶ Y := match a with
  | .regular r => OriginalNativeProductWindow.chartInclusion r.targetChart
  | .singular c => OriginalNativeSmoothCanonicalSquare.targetInclusion c.window c.neighbourhood

def baseMap : sourceBase a ⟶ targetBase a := match a with
  | .regular r => r.map
  | .singular c => baseProjection c.window c.neighbourhood

def sourceProjection : sourceResolved a ⟶ sourceBase a := match a with
  | .regular _ => 𝟙 _
  | .singular c => c.sourceResolution

def targetProjection : targetResolved a ⟶ targetBase a := match a with
  | .regular _ => 𝟙 _
  | .singular c => c.targetResolution

def lift : sourceResolved a ⟶ targetResolved a := match a with
  | .regular r => r.map
  | .singular c => c.nativeLift

theorem base_square : sourceInclusion a ≫ f = baseMap a ≫ targetInclusion a := by
  cases a with
  | regular r => exact r.square
  | singular c => exact OriginalNativeSmoothCanonicalSquare.base_square c.window c.neighbourhood

theorem native_square : sourceProjection a ≫ baseMap a = lift a ≫ targetProjection a := by
  cases a with
  | regular r => exact (Category.id_comp r.map).trans (Category.comp_id r.map).symm
  | singular c => exact c.native_square

theorem original_square : sourceProjection a ≫ (sourceInclusion a ≫ f) =
    lift a ≫ (targetProjection a ≫ targetInclusion a) := by
  rw [base_square,← Category.assoc,native_square,Category.assoc]

theorem source_properties : IsResolution (sourceProjection a) ∧
    Function.Surjective (sourceProjection a).hom.left.base ∧ IsProperMap (sourceProjection a).hom.left.base ∧
    IsIsoOver (sourceProjection a) ((sourceInclusion a).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  cases a with
  | regular r => exact r.source_properties
  | singular c => exact c.source_properties

theorem target_properties : IsResolution (targetProjection a) ∧
    Function.Surjective (targetProjection a).hom.left.base ∧ IsProperMap (targetProjection a).hom.left.base ∧
    IsIsoOver (targetProjection a) ((targetInclusion a).hom.left.base ⁻¹' intrinsicRegularLocus Y.obj) := by
  cases a with
  | regular r => exact r.target_properties
  | singular c => exact c.target_properties

theorem source_covers : x ∈ range (sourceInclusion a).hom.left.base := by
  cases a with
  | regular r => exact ⟨r.sourcePoint,r.point⟩
  | singular c => exact sourceInclusion_covers c.window c.neighbourhood c.point_mem

theorem source_range : range (sourceInclusion a).hom.left.base ⊆ (V : Set X.obj.left) := by
  cases a with
  | regular r => exact r.source_range
  | singular c => exact sourceInclusion_range c.window c.neighbourhood

theorem target_range : range (targetInclusion a).hom.left.base ⊆ (T : Set Y.obj.left) := by
  cases a with
  | regular r => exact r.target_range
  | singular c => exact targetInclusion_range c.window c.neighbourhood

theorem source_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (sourceInclusion a).hom.left := by
  cases a with
  | regular r => exact windowMorphism_isOpenImmersion r.sourceChart r.sourceOpen
  | singular c => exact sourceInclusion_isOpenImmersion c.window c.neighbourhood

theorem target_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (targetInclusion a).hom.left := by
  cases a with
  | regular r => exact r.targetChart.isOpenImmersion
  | singular c => exact targetInclusion_isOpenImmersion c.window c.neighbourhood

end LocalSquare

end
end SGPT.Unibranch.OriginalNativeSmoothAllPointSquare
