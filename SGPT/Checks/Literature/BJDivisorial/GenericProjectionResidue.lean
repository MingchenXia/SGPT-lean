import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeGenericFieldGraph
import Mathlib.AlgebraicGeometry.ResidueField

/-! # The literal original generic residue map is bijective
An actual dominant original field point and its actual generic projection
internally derive birationality of the original scheme morphism, including
its literal residueFieldMap at the generic point. No equivalence or
birationality certificate is supplied.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope
universe u

/-- A dominant actual field point has the genuine generic support. -/
theorem dominant_fieldPoint_generic {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] (g : Spec (.of K) ⟶ Y) [IsDominant g] :
    g (IsLocalRing.closedPoint K) = genericPoint Y := by
  rw [show IsLocalRing.closedPoint K = genericPoint (Spec (.of K)) from Subsingleton.elim _ _]
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, g.denseRange.closure_range] using
    (genericPoint_spec (Spec (.of K))).image g.continuous

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : Y ⟶ X) (g : Spec X.functionField ⟶ Y) [IsDominant g]
  (hp : g ≫ π = X.fromSpecStalk (genericPoint X))

include g hp

/-- The actual projection takes the genuine generic point to the original
one, derived from the whole generic triangle. -/
theorem genericProjection_image_generic : π (genericPoint Y) = genericPoint X := by
  rw [← dominant_fieldPoint_generic g]
  change (g ≫ π) (IsLocalRing.closedPoint X.functionField) = _
  rw [hp, Scheme.fromSpecStalk_closedPoint]

/-- The actual original generic stalk pullback is bijective. -/
theorem genericProjection_stalkMap_bijective :
    Function.Bijective (π.stalkMap (genericPoint Y)).hom := by
  let a : X.functionField ⟶ X.presheaf.stalk (π (genericPoint Y)) :=
    (X.presheaf.stalkCongr (.of_eq (genericProjection_image_generic π g hp).symm)).hom
  let r : X.functionField ⟶ Y.functionField := a ≫ π.stalkMap (genericPoint Y)
  have hr : Spec.map r ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ π := by
    dsimp only [r, a]
    rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hcomp : r ≫ SchemeGenericFieldGraph.fieldHom g = 𝟙 X.functionField := by
    have hc : Spec.map (r ≫ SchemeGenericFieldGraph.fieldHom g) ≫
        X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) := by
      rw [Spec.map_comp, Category.assoc, hr, ← Category.assoc,
        SchemeGenericFieldGraph.fieldHom_fromSpecStalk, hp]
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    simpa only [Spec.map_id] using hc.trans (Category.id_comp _).symm
  let e := SchemeGenericFieldGraph.functionFieldEquiv g π hp
  have hrbi : Function.Bijective r.hom := by
    refine ⟨r.hom.injective, ?_⟩
    intro y
    refine ⟨e y, e.injective ?_⟩
    exact congrArg (fun f : X.functionField ⟶ X.functionField => f (e y)) hcomp
  have ha : Function.Bijective a.hom :=
    ConcreteCategory.bijective_of_isIso a
  exact (Function.Bijective.of_comp_iff (π.stalkMap (genericPoint Y)).hom ha).mp hrbi

/-- The LITERAL original generic residueFieldMap is bijective, exactly the
field required by the source PrimeDivisorOver definition. -/
theorem genericProjection_residueFieldMap_bijective :
    Function.Bijective (π.residueFieldMap (genericPoint Y)).hom := by
  let e := RingEquiv.ofBijective (π.stalkMap (genericPoint Y)).hom
    (genericProjection_stalkMap_bijective π g hp)
  exact (IsLocalRing.ResidueField.mapEquiv e).bijective

end SGPT.NAPotential.BJ.Divisorial
