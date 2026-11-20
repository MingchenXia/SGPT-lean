import SGPT.Unibranch.OriginalNativeProperAtlas

/-! Global normality, whole finite fibres and onto on the SAME actual native proper atlas.
Blueprint: prime-nov16-analytic-normalization-original-proper-atlas-descent.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperAtlasDescent
open OriginalNativeProperAtlas
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SourceReducedComplexSpace

theorem glued_normal_stalks (D : LocallyRingedSpace.GlueData.{0})
    (hnormal : ∀ i,∀ y : D.U i,IsDomain ((D.U i).presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((D.U i).presheaf.stalk y).carrier) (x : glued D) :
    IsDomain ((glued D).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((glued D).presheaf.stalk x).carrier := by
  obtain ⟨i,y,rfl⟩ := inclusion_cover D x
  obtain ⟨hd,hn⟩ := hnormal i y
  let : IsDomain ((D.U i).presheaf.stalk y).carrier := hd
  let : IsIntegrallyClosed ((D.U i).presheaf.stalk y).carrier := hn
  let E := (asIso ((inclusion D i).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain E E.injective,IsIntegrallyClosed.of_equiv E.symm⟩

variable (D : LocallyRingedSpace.GlueData.{0})
  (σ : ∀ i : D.J,D.U i ⟶ SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces.complexPoint)
  (hA : ∀ i,sourceReducedComplexSpaceProperty (Over.mk (σ i)))
  {X : SourceReducedComplexSpace} {B : D.J → SourceReducedComplexSpace}
  (J : ∀ i,B i ⟶ X) (p : ∀ i,localSource D σ hA i ⟶ B i)
  (hover : ∀ i j,D.f i j ≫ localProjection D σ hA J p i =
    (D.t i j ≫ D.f j i) ≫ localProjection D σ hA J p j)
  (hOverlap : ∀ i j,range (D.f i j).base =
    (localProjection D σ hA J p i).base ⁻¹' range (J j).hom.left.base)
  (hJ : ∀ i,LocallyRingedSpace.IsOpenImmersion (J i).hom.left)
  (hcover : ∀ x : X.obj.left,∃ i b,(J i).hom.left.base b=x)

include hOverlap hJ hcover in
theorem projection_fibres_finite
    (hfinite : ∀ i,∀ b : (B i).obj.left,((p i).hom.left.base ⁻¹' {b}).Finite)
    (x : X.obj.left) : ((projection D σ hA J p hover).base ⁻¹' {x}).Finite := by
  obtain ⟨i,b,hb⟩ := hcover x
  have hsub : (projection D σ hA J p hover).base ⁻¹' {x} ⊆
      (inclusion D i).base '' ((p i).hom.left.base ⁻¹' {b}) := by
    intro y hy
    have hyEq : (projection D σ hA J p hover).base y=x := hy
    have hs : y ∈ range (inclusion D i).base := by
      rw [← preimage_chart_range D σ hA J p hover hOverlap i]
      exact ⟨b,hb.trans hyEq.symm⟩
    obtain ⟨a,ha⟩ := hs
    refine ⟨a,?_,ha⟩
    change (p i).hom.left.base a=b
    apply (hJ i).base_open.injective
    calc
      (J i).hom.left.base ((p i).hom.left.base a) =
          (projection D σ hA J p hover).base ((inclusion D i).base a) :=
        (congrArg (fun t => t.base a) (inclusion_projection D σ hA J p hover i)).symm
      _ = (projection D σ hA J p hover).base y := congrArg _ ha
      _ = x := hyEq
      _ = (J i).hom.left.base b := hb.symm
  exact ((hfinite i b).image (inclusion D i).base).subset hsub

include hcover in
theorem projection_surjective
    (honto : ∀ i,Function.Surjective (p i).hom.left.base) :
    Function.Surjective (projection D σ hA J p hover).base := by
  intro x
  obtain ⟨i,b,hb⟩ := hcover x
  obtain ⟨a,ha⟩ := honto i b
  refine ⟨(inclusion D i).base a,?_⟩
  calc
    (projection D σ hA J p hover).base ((inclusion D i).base a) =
        (J i).hom.left.base ((p i).hom.left.base a) :=
      congrArg (fun t => t.base a) (inclusion_projection D σ hA J p hover i)
    _ = (J i).hom.left.base b := congrArg _ ha
    _ = x := hb

theorem sourceObject_normal_proper_finite_surjective
    (hproper : ∀ i,IsProperMap (p i).hom.left.base)
    (hnormal : ∀ i,∀ y : D.U i,IsDomain ((D.U i).presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((D.U i).presheaf.stalk y).carrier)
    (hfinite : ∀ i,∀ b : (B i).obj.left,((p i).hom.left.base ⁻¹' {b}).Finite)
    (honto : ∀ i,Function.Surjective (p i).hom.left.base) :
    (∀ y : (sourceObject D σ hA J p hover hOverlap hJ hcover hproper).obj.left,
      IsDomain (((sourceObject D σ hA J p hover hOverlap hJ hcover hproper).obj.left).presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (((sourceObject D σ hA J p hover hOverlap hJ hcover hproper).obj.left).presheaf.stalk y).carrier) ∧
    IsProperMap (projectionMorphism D σ hA J p hover hOverlap hJ hcover hproper).hom.left.base ∧
    (∀ x : X.obj.left,((projectionMorphism D σ hA J p hover hOverlap hJ hcover hproper).hom.left.base ⁻¹' {x}).Finite) ∧
    Function.Surjective (projectionMorphism D σ hA J p hover hOverlap hJ hcover hproper).hom.left.base := by
  exact ⟨glued_normal_stalks D hnormal,
    projection_isProperMap D σ hA J p hover hOverlap hJ hcover hproper,
    projection_fibres_finite D σ hA J p hover hOverlap hJ hcover hfinite,
    projection_surjective D σ hA J p hover hcover honto⟩
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperAtlasDescent
