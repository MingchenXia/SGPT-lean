import SGPT.PSH.PrimeNov16OriginalHypersurfaceDictionary
import SGPT.PSH.PrimeNov16OriginalStrictTransformEquality

/-! Primitive ORIGINAL primes and ONE literal common-resolution witness.
No native model/dictionary is a primitive field. Full blueprint first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalPrimePresentation
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic
open PrimeNov16OriginalHypersurface PrimeNov16OriginalStrictTransform

/-- Exact intrinsic original presentation: no chosen native representative. -/
structure PrimePresentation (X : SourceReducedComplexSpace) where
  model : SourceReducedComplexSpace
  smooth : model.IsSmooth
  projection : model ⟶ X
  resolution : IsResolution projection
  divisor : Set model.obj.left
  hypersurface : IsOriginalHypersurface model divisor

variable {X : SourceReducedComplexSpace}

/-- The literal ORIGINAL centre. -/
def presentationCenter (p : PrimePresentation X) : Set X.obj.left :=
  p.projection.hom.left.base '' p.divisor

theorem exists_actual_native_representation (p : PrimePresentation X) :
    ∃ (c : ConnectedComponents p.model.obj.left) (n : ℕ) (M : CMfd n)
      (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject p.smooth c) (k : ℕ),
      IsClosedConnectedSubmanifold n
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion p.smooth c) ⁻¹' p.divisor) k ∧
      k+1=n ∧
      pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion p.smooth c) ''
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion p.smooth c) ⁻¹' p.divisor) = p.divisor :=
  exists_actual_native_hypersurface p.smooth p.hypersurface

theorem exists_component_containing_divisor (p : PrimePresentation X) :
    ∃ c : ConnectedComponents p.model.obj.left, p.divisor ⊆ OriginalSmoothComponents.componentSet c := by
  obtain ⟨x, hx⟩ := p.hypersurface.2.1.nonempty
  refine ⟨ConnectedComponents.mk x, ?_⟩
  rw [OriginalSmoothComponents.componentSet_eq_connectedComponent]
  exact p.hypersurface.2.1.subset_connectedComponent hx

/-- ONE genuine full original common resolution and literal WHOLE-source strict equality. -/
structure CommonResolutionGeometry (p q : PrimePresentation X) where
  model : SourceReducedComplexSpace
  smooth : model.IsSmooth
  left : model ⟶ p.model
  right : model ⟶ q.model
  left_modification : IsProperBimeromorphic left
  right_modification : IsProperBimeromorphic right
  over_base : left ≫ p.projection = right ≫ q.projection
  resolution : IsResolution (left ≫ p.projection)
  strict_equal : originalStrictTransform left p.divisor = originalStrictTransform right q.divisor

def commonResolutionRelation (p q : PrimePresentation X) : Prop :=
  Nonempty (CommonResolutionGeometry p q)

private theorem identity_pb (Y : SourceReducedComplexSpace) : IsProperBimeromorphic (𝟙 Y) := by
  refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
  exact IsIsoOver.id_of_isOpen Y (by simp)

theorem commonResolutionRelation_refl (p : PrimePresentation X) : commonResolutionRelation p p := by
  refine ⟨⟨p.model, p.smooth, 𝟙 p.model, 𝟙 p.model, identity_pb _, identity_pb _, rfl, ?_, rfl⟩⟩
  simpa only [Category.id_comp] using p.resolution

theorem commonResolutionRelation_symm {p q : PrimePresentation X}
    (h : commonResolutionRelation p q) : commonResolutionRelation q p := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.model, h.smooth, h.right, h.left, h.right_modification, h.left_modification,
    h.over_base.symm, Eq.mp (congrArg IsResolution h.over_base) h.resolution, h.strict_equal.symm⟩⟩

end SGPT.PSH.PrimeNov16OriginalPrimePresentation
