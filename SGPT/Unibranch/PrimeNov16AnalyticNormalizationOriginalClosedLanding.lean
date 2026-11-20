import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction

/-! Full actual original landing in a true base open, and closed-embedding properness.
Blueprint: prime-nov16-analytic-normalization-original-closed-landing.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

variable {B X : SourceReducedComplexSpace} (g : B ⟶ X)
  (U : Opens X.obj.left) [ParacompactSpace U]
  (hland : range g.hom.left.base ⊆ (U : Set X.obj.left))

include hland

private theorem lands : range g.hom.left.base ⊆ range (baseInclusion U).hom.left.base := by
  rintro _ ⟨b,rfl⟩
  exact ⟨⟨g.hom.left.base b,hland ⟨b,rfl⟩⟩,rfl⟩

def landingMap : B ⟶ restrictedBase U := by
  let L := LocallyRingedSpace.IsOpenImmersion.lift (baseInclusion U).hom.left g.hom.left (lands g U hland)
  have hL := LocallyRingedSpace.IsOpenImmersion.lift_fac (baseInclusion U).hom.left g.hom.left (lands g U hland)
  have hs : L ≫ (restrictedBase U).obj.hom=B.obj.hom := by
    rw [← Over.w (baseInclusion U).hom,← Category.assoc,hL]
    exact Over.w g.hom
  exact ObjectProperty.homMk (Over.homMk L hs)

theorem landingMap_square : landingMap g U hland ≫ baseInclusion U=g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (lands g U hland)

theorem landingMap_point (b : B.obj.left) :
    ((landingMap g U hland).hom.left.base b).val=g.hom.left.base b :=
  congrArg (fun f : B ⟶ X => f.hom.left.base b) (landingMap_square g U hland)

theorem landingMap_closed (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    Topology.IsClosedEmbedding (landingMap g U hland).hom.left.base := by
  have hcomp : (Subtype.val : U → X.obj.left) ∘ (landingMap g U hland).hom.left.base=
      g.hom.left.base := funext (landingMap_point g U hland)
  have he : Topology.IsEmbedding (landingMap g U hland).hom.left.base := by
    exact Topology.IsEmbedding.of_comp
      (landingMap g U hland).hom.left.base.hom.continuous continuous_subtype_val
      (show Topology.IsEmbedding ((Subtype.val : U → X.obj.left) ∘
        (landingMap g U hland).hom.left.base) from hcomp.symm ▸ hg)
  refine ⟨he,?_⟩
  have hr : range (landingMap g U hland).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
    exact LocallyRingedSpace.IsOpenImmersion.lift_range _ _ (lands g U hland)
  rw [hr]
  exact hc

theorem landingMap_proper (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    IsProperMap (landingMap g U hland).hom.left.base :=
  (landingMap_closed g U hland hg hc).isProperMap

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding
