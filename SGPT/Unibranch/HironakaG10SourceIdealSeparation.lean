import SGPT.Unibranch.HironakaG10SourceIdentifiedSumCentre
import SGPT.Unibranch.HironakaG10NativeSumCentreSeparation

/-! # Separation of the source ideal families -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10SourceIdealSeparation

open SGPT.Foundations.Analysis.Pending HironakaSingularModuleSheafStalk
open SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowOneStepStrictTransform
  SGPT.Unibranch.HironakaG10NativeSumCentreSeparation

noncomputable section

/-- If the centre retains the equation supplied by
`exists_sourceIdentified_sumCentre`, it separates the strict transforms of
  the original ideal family and the local flattener family throughout its
  domain, not just an existentially chosen ideal at a centre point. -/
theorem source_families_separated
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)) (β : ℕ)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (hStalk : ∀ x ∈ Z.V, LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = IS x ^ β ⊔ Z.H x)
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hx : (stepProj B b hDense).hom.left.base x' ∈ Z.V) :
    ¬ (OnStrictTransform (stepProj B b hDense) x'
         (IS ((stepProj B b hDense).hom.left.base x') ^ β)
         (IS ((stepProj B b hDense).hom.left.base x') ^ β ⊔
           Z.H ((stepProj B b hDense).hom.left.base x')) ∧
       OnStrictTransform (stepProj B b hDense) x'
         (Z.H ((stepProj B b hDense).hom.left.base x'))
         (IS ((stepProj B b hDense).hom.left.base x') ^ β ⊔
           Z.H ((stepProj B b hDense).hom.left.base x'))) :=
  not_both_on_strictTransform B b hDense x' _ _ (hStalk _ hx)

end
end SGPT.Unibranch.HironakaG10SourceIdealSeparation
