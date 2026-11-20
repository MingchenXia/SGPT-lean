import SGPT.Unibranch.NativeNov16NormalizationSpace
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRegularLocusInverse
import SGPT.Unibranch.OriginalIntrinsicSingularLocus
import SGPT.Unibranch.OriginalNativeIsoOverSaturatedCover

/-! Source-only global normal finite proper-bimeromorphic normalization.
Blueprint: native-nov16-normalization-existence.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
namespace SGPT.Unibranch.NativeNov16NormalizationExistence
open SourceReducedComplexSpace
open NativeNov16NormalizationSpace
open PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
open PrimeNov16AnalyticNormalizationOriginalRegularLocusInverse

variable (X : SourceReducedComplexSpace)

def chartMorphism (i : X.obj.left) : (atPoint X i).source ⟶ source X :=
  OriginalNativeProperAtlas.localMorphism (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

instance chartMorphism_open (i : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (chartMorphism X i).hom.left :=
  OriginalNativeProperAtlas.localMorphism_isOpenImmersion (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

theorem chart_projection (i : X.obj.left) :
    chartMorphism X i ≫ projection X = (atPoint X i).projection ≫ (atPoint X i).into :=
  OriginalNativeProperAtlas.localMorphism_projection (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

theorem chart_range (i : X.obj.left) :
    range (chartMorphism X i).hom.left.base =
      (projection X).hom.left.base ⁻¹' range (atPoint X i).into.hom.left.base :=
  (OriginalNativeProperAtlas.preimage_chart_range (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X) i).symm

theorem chart_cover (y : (source X).obj.left) :
    ∃ (i : X.obj.left) (a : (atPoint X i).source.obj.left),(chartMorphism X i).hom.left.base a=y :=
  OriginalNativeProperAtlas.localMorphism_cover (data X) (scalar X) (local_property X)
    (baseInclusion X) (localProjection X) (overlap_triangle X) (overlap_range X)
    (base_open X) (base_cover X) (local_proper X) y

theorem isIsoOver_intrinsicRegularLocus : IsIsoOver (projection X) (intrinsicRegularLocus X.obj) :=
  OriginalNativeIsoOverSaturatedCover.isIsoOver_of_saturated_cover (projection X)
    (fun i => (atPoint X i).into) (chartMorphism X) (fun i => (atPoint X i).projection)
    (base_open X) (chartMorphism_open X) (base_cover X) (chart_projection X) (chart_range X)
    (intrinsicRegularLocus X.obj) (isOpen_intrinsicRegularLocus X.obj) (atPoint_regular_isIsoOver X)

theorem dense_preimage_intrinsicRegularLocus :
    Dense ((projection X).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  intro y
  obtain ⟨i,a,rfl⟩ := chart_cover X y
  apply mem_closure_iff.mpr
  intro U hU haU
  obtain ⟨b,hbU,hbR⟩ := mem_closure_iff.mp (atPoint_regular_dense X i a)
    ((chartMorphism X i).hom.left.base ⁻¹' U)
    (hU.preimage (chartMorphism X i).hom.left.base.hom.continuous) haU
  refine ⟨(chartMorphism X i).hom.left.base b,hbU,?_⟩
  have he := congrArg (fun f => f.hom.left.base b) (chart_projection X i)
  change (projection X).hom.left.base ((chartMorphism X i).hom.left.base b) ∈
    intrinsicRegularLocus X.obj
  exact he.symm ▸ hbR

theorem projection_proper_bimeromorphic : IsProperBimeromorphic (projection X) := by
  refine ⟨(normal_proper_finite_surjective X).2.1,intrinsicSingularLocus X.obj,
    OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus X,
    OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty X,?_,?_⟩
  · apply interior_eq_empty_iff_dense_compl.mpr
    simpa only [Set.preimage_compl,intrinsicSingularLocus,compl_compl] using
      dense_preimage_intrinsicRegularLocus X
  · simpa only [intrinsicSingularLocus,compl_compl] using isIsoOver_intrinsicRegularLocus X

theorem exists_normalization :
    ∃ (N : SourceReducedComplexSpace) (p : N ⟶ X),
      (∀ y : N.obj.left,IsDomain (N.obj.left.presheaf.stalk y).carrier ∧
        IsIntegrallyClosed (N.obj.left.presheaf.stalk y).carrier) ∧
      IsProperBimeromorphic p ∧
      (∀ x : X.obj.left,(p.hom.left.base ⁻¹' {x}).Finite) ∧ Function.Surjective p.hom.left.base :=
  ⟨source X,projection X,(normal_proper_finite_surjective X).1,
    projection_proper_bimeromorphic X,(normal_proper_finite_surjective X).2.2.1,
    (normal_proper_finite_surjective X).2.2.2⟩

end SGPT.Unibranch.NativeNov16NormalizationExistence
