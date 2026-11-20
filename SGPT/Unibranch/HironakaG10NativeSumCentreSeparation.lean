import SGPT.Unibranch.HironakaG10SumCentreSeparation
import SGPT.Unibranch.HironakaG10ChowTrackedDatum
import SGPT.Unibranch.HironakaG10ChowProductCentre

/-! # Separation on the actual finite-ideal blowup -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10NativeSumCentreSeparation

open SGPT.Foundations.Analysis.Pending HironakaSingularModuleSheafStalk
open SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowOneStepStrictTransform
  SGPT.Unibranch.HironakaG10ChowProductCentre
  SGPT.Unibranch.HironakaG10ChowLeavingRounds
  SGPT.Unibranch.HironakaG10SumCentreSeparation
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- At an actual blowup point, a sum-centre equation separates the two
  algebraic strict transforms. -/
theorem not_both_on_strictTransform
    {X : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (I J : Ideal (X.obj.left.presheaf.stalk ((stepProj B b hDense).hom.left.base x')))
    (hB : LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      ((stepProj B b hDense).hom.left.base x')) = I ⊔ J) :
    ¬ (OnStrictTransform (stepProj B b hDense) x' I (I ⊔ J) ∧
       OnStrictTransform (stepProj B b hDense) x' J (I ⊔ J)) := by
  intro ⟨hI, hJ⟩
  obtain ⟨G, hD, hG⟩ := stepProj_pulledIdeal_regular B b hDense x'
  have hD' : Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom (I ⊔ J) =
      Ideal.span {G} := by rw [← hB]; exact hD
  apply strictIdeals_not_both_proper _ I J G hG hD'
  exact ⟨IsLocalRing.le_maximalIdeal (hI G hG hD'),
    IsLocalRing.le_maximalIdeal (hJ G hG hD')⟩


/-- The tracked flattener strict transform and the powered auxiliary ideal
  strict transform are disjoint pointwise at every point over a sum centre. -/
theorem sumCentre_separates
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (f : Y ⟶ X) (β : ℕ) (hSum : IsSumCentreFor B b f β)
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hx : (stepProj B b hDense).hom.left.base x' ∈ nonunitLocus B b) :
    ∃ IS : Ideal (X.obj.left.presheaf.stalk ((stepProj B b hDense).hom.left.base x')),
      ¬ (OnStrictTransform (stepProj B b hDense) x' (IS ^ β)
           (IS ^ β ⊔ germFlattener f ((stepProj B b hDense).hom.left.base x')) ∧
         OnStrictTransform (stepProj B b hDense) x'
           (germFlattener f ((stepProj B b hDense).hom.left.base x'))
           (IS ^ β ⊔ germFlattener f ((stepProj B b hDense).hom.left.base x'))) := by
  obtain ⟨IS, α, hα, hAR, hB⟩ := hSum _ hx
  exact ⟨IS, not_both_on_strictTransform B b hDense x' _ _ hB⟩

end
end SGPT.Unibranch.HironakaG10NativeSumCentreSeparation
