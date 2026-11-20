import SGPT.Unibranch.NativeNov16NormalizationAtlasGlueData
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperAtlasDescent

/-! The actual global finite normal source and full proper map, from only X.
Blueprint: native-nov16-normalization-space.tex. Regular-locus ISO is separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16NormalizationSpace
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps

variable (X : SourceReducedComplexSpace)

abbrev data := NativeNov16NormalizationAtlasGlueData.glueData X
def scalar (i : X.obj.left) : (data X).U i ⟶ complexPoint := (atPoint X i).source.obj.hom
theorem local_property (i : X.obj.left) : sourceReducedComplexSpaceProperty (Over.mk (scalar X i)) :=
  (atPoint X i).source.property
def baseInclusion (i : X.obj.left) : (atPoint X i).base ⟶ X := (atPoint X i).into
def localProjection (i : X.obj.left) :
    OriginalNativeProperAtlas.localSource (data X) (scalar X) (local_property X) i ⟶
      (atPoint X i).base := (atPoint X i).projection

theorem overlap_triangle (i j : X.obj.left) :
    (data X).f i j ≫ OriginalNativeProperAtlas.localProjection
      (data X) (scalar X) (local_property X) (baseInclusion X) (localProjection X) i =
    ((data X).t i j ≫ (data X).f j i) ≫ OriginalNativeProperAtlas.localProjection
      (data X) (scalar X) (local_property X) (baseInclusion X) (localProjection X) j := by
  change NativeNov16NormalizationAtlasGlueData.inclusion X i j ≫
      NativeNov16NormalizationAtlasGlueData.projection X i =
    (NativeNov16NormalizationAtlasGlueData.transition X i j ≫
      NativeNov16NormalizationAtlasGlueData.inclusion X j i) ≫
        NativeNov16NormalizationAtlasGlueData.projection X j
  simpa only [Category.assoc] using (NativeNov16NormalizationAtlasGlueData.overlap_square X i j).symm

theorem overlap_range (i j : X.obj.left) : range ((data X).f i j).base =
    (OriginalNativeProperAtlas.localProjection (data X) (scalar X) (local_property X)
      (baseInclusion X) (localProjection X) i).base ⁻¹' range (baseInclusion X j).hom.left.base :=
  NativeNov16NormalizationAtlasGlueData.inclusion_range X i j

theorem base_open (i : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (baseInclusion X i).hom.left := (atPoint X i).into_open

theorem base_cover (x : X.obj.left) :
    ∃ (i : X.obj.left) (b : (atPoint X i).base.obj.left),(baseInclusion X i).hom.left.base b=x :=
  ⟨x,(atPoint X x).center,(atPoint X x).center_eq⟩

theorem local_proper (i : X.obj.left) : IsProperMap (localProjection X i).hom.left.base :=
  (atPoint X i).proper

def source : SourceReducedComplexSpace :=
  OriginalNativeProperAtlas.sourceObject (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X)

def projection : source X ⟶ X :=
  OriginalNativeProperAtlas.projectionMorphism (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X)

theorem normal_proper_finite_surjective :
    (∀ y : (source X).obj.left,IsDomain ((source X).obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((source X).obj.left.presheaf.stalk y).carrier) ∧
    IsProperMap (projection X).hom.left.base ∧
    (∀ x : X.obj.left,((projection X).hom.left.base ⁻¹' {x}).Finite) ∧
    Function.Surjective (projection X).hom.left.base :=
  PrimeNov16AnalyticNormalizationOriginalProperAtlasDescent.sourceObject_normal_proper_finite_surjective
    (data X) (scalar X) (local_property X) (baseInclusion X) (localProjection X)
    (overlap_triangle X) (overlap_range X) (base_open X) (base_cover X) (local_proper X)
    (fun i => (atPoint X i).normal) (fun i => (atPoint X i).finite) (fun i => (atPoint X i).onto)

end SGPT.Unibranch.NativeNov16NormalizationSpace
