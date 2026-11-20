import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalBimeromorphicLift

/-! The actual full resolution-to-normalization map on the same given original resolution.
Blueprint: prime-nov16-analytic-normalization-original-resolution-normalization-lift.tex. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalIntrinsicRegularNormal

theorem exists_unique_lift_of_resolution {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsResolution f) :
    ∃! L : Y ⟶ NativeNov16NormalizationSpace.source X,
      L ≫ NativeNov16NormalizationSpace.projection X=f :=
  PrimeNov16AnalyticNormalizationOriginalNormalBimeromorphicLift.exists_unique_lift
    (fun y => normal_stalk_of_intrinsicRegular Y y (hf.1 y)) f hf.2

def resolutionLift {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hf : IsResolution f) :
    Y ⟶ NativeNov16NormalizationSpace.source X :=
  Classical.choose (exists_unique_lift_of_resolution f hf)

theorem resolutionLift_projection {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsResolution f) :
    resolutionLift f hf ≫ NativeNov16NormalizationSpace.projection X=f :=
  (Classical.choose_spec (exists_unique_lift_of_resolution f hf)).1

theorem resolutionLift_unique {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsResolution f) (L : Y ⟶ NativeNov16NormalizationSpace.source X)
    (hL : L ≫ NativeNov16NormalizationSpace.projection X=f) : L=resolutionLift f hf :=
  (Classical.choose_spec (exists_unique_lift_of_resolution f hf)).2 L hL
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
