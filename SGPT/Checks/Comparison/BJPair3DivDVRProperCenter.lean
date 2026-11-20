import SGPT.Checks.Comparison.BJPair3DivDVRProperTrait
import SGPT.Foundations.Envelope.AlgGeom.SchemeLocalResidueCoefficients

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DVRProperCenter.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# The actual center has its original DVR as its canonical local ring

The entire constructed trait maps into the actual open Spec A of its
projective compactification. Pull this open back to the normal proper
model, construct its actual morphism to Spec A, and derive the canonical
coefficient square. Localization and generic dominance prove equality of
the actual center stalk with V. No center/stalk/divisorial certificate is
an incoming hypothesis.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
open SGPT.Support.Alterations SGPT.Foundations.Envelope

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsVariety p] [IsProper p]

local instance center_baseFieldAlgebra : Algebra k X.functionField :=
  p.stalkAlgebra (genericPoint X)

variable (V : Subalgebra k X.functionField) [Algebra.EssFiniteType k V]
  [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]

/-- The actual affine-presentation open pulled back to the proper model. -/
def presentationOpen : (model p V).Opens :=
  presentation p V ⁻¹ᵁ (DVRPresentation.inclusion V).opensRange

omit [IsProper p] [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
private theorem presentationOpen_range :
    Set.range ((presentationOpen p V).ι ≫ presentation p V) ⊆
      Set.range (DVRPresentation.inclusion V) := by
  rintro _ ⟨z, rfl⟩
  exact z.2

/-- The actual coefficient morphism on the actual pulled-back open. -/
def openPresentation : (presentationOpen p V).toScheme ⟶ Spec (.of (DVRPresentation.coefficientAlgebra V)) :=
  IsOpenImmersion.lift (DVRPresentation.inclusion V)
    ((presentationOpen p V).ι ≫ presentation p V) (presentationOpen_range p V)

omit [IsProper p] [IsDiscreteValuationRing V] [IsFractionRing V X.functionField] in
@[reassoc]
theorem openPresentation_inclusion :
    openPresentation p V ≫ DVRPresentation.inclusion V =
      (presentationOpen p V).ι ≫ presentation p V := IsOpenImmersion.lift_fac _ _ _

private theorem trait_range_in_presentationOpen :
    Set.range (trait p V) ⊆ Set.range (presentationOpen p V).ι := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨trait p V z, ?_⟩, rfl⟩
  change (presentation p V) (trait p V z) ∈ Set.range (DVRPresentation.inclusion V)
  change (trait p V ≫ presentation p V) z ∈ _
  rw [trait_presentation]
  exact ⟨(Spec.map (CommRingCat.ofHom
    (algebraMap (DVRPresentation.coefficientAlgebra V) V))) z, rfl⟩

/-- The WHOLE original trait actually factors through the presentation open. -/
def openTrait : Spec (.of V) ⟶ (presentationOpen p V).toScheme :=
  IsOpenImmersion.lift (presentationOpen p V).ι (trait p V)
    (trait_range_in_presentationOpen p V)

@[reassoc]
theorem openTrait_inclusion : openTrait p V ≫ (presentationOpen p V).ι = trait p V :=
  IsOpenImmersion.lift_fac _ _ _

instance presentationOpen_nonempty : Nonempty (presentationOpen p V) :=
  ⟨openTrait p V (closedPoint V)⟩

instance presentationOpen_integral : IsIntegral (presentationOpen p V).toScheme :=
  isIntegral_of_isOpenImmersion (presentationOpen p V).ι

instance openTrait_fraction_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ openTrait p V) := by
  let : IsDominant ((Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
      openTrait p V) ≫ (presentationOpen p V).ι) := by
    rw [Category.assoc, openTrait_inclusion]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ (presentationOpen p V).ι

/-- EVERY presentation coefficient retains the WHOLE actual trait square. -/
theorem openTrait_coefficients :
    openTrait p V ≫ openPresentation p V = Spec.map (CommRingCat.ofHom
      (algebraMap (DVRPresentation.coefficientAlgebra V) V)) := by
  apply (cancel_mono (DVRPresentation.inclusion V)).mp
  rw [Category.assoc, openPresentation_inclusion, ← Category.assoc, openTrait_inclusion]
  exact trait_presentation p V

/-- The actual canonical local map on the presentation open is bijective,
with all coefficients derived from the global original diagram. -/
theorem openTrait_stalkMap_bijective :
    Function.Bijective (Scheme.stalkClosedPointTo (openTrait p V)).hom := by
  apply trait_stalkMap_bijective_of_localization (K := X.functionField) (openTrait p V)
    (Algebra.EssFiniteType.submonoid k V)
    (SchemeStalkCoefficients.coefficientMap (openPresentation p V)
      (openTrait p V (closedPoint V)))
  exact SchemeLocalResidueCoefficients.stalkClosedPointTo_coefficients
    (openPresentation p V) (openTrait p V)
    (algebraMap (DVRPresentation.coefficientAlgebra V) V) (openTrait_coefficients p V)

/-- The canonical stalk on the actual pulled-back open is the original DVR. -/
theorem openTrait_stalk_isDVR : IsDiscreteValuationRing
    ((presentationOpen p V).toScheme.presheaf.stalk (openTrait p V (closedPoint V))) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective _ (openTrait_stalkMap_bijective p V)).symm

/-- The whole original trait presented through the actual open inclusion. -/
def centeredTrait : Spec (.of V) ⟶ model p V := openTrait p V ≫ (presentationOpen p V).ι

theorem centeredTrait_eq_trait : centeredTrait p V = trait p V := openTrait_inclusion p V

instance centeredTrait_fraction_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ centeredTrait p V) := by
  rw [centeredTrait_eq_trait]
  infer_instance

/-- The actual center on the NORMAL PROPER model has a DVR stalk; its
codimension and original fraction orders are now consequences. -/
theorem centeredTrait_stalk_isDVR : IsDiscreteValuationRing
    ((model p V).presheaf.stalk (centeredTrait p V (closedPoint V))) := by
  have he : centeredTrait p V (closedPoint V) =
      (presentationOpen p V).ι (openTrait p V (closedPoint V)) :=
    Scheme.Hom.comp_apply _ _ _
  rw [he]
  let := openTrait_stalk_isDVR p V
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso ((presentationOpen p V).ι.stalkMap
      (openTrait p V (closedPoint V)))).commRingCatIsoToRingEquiv.symm

@[reassoc]
theorem centeredTrait_genericProjection :
    (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ centeredTrait p V) ≫
      projection p V = X.fromSpecStalk (genericPoint X) := by
  rw [centeredTrait_eq_trait, trait_fraction, normalizedGenericPoint_projection]

/-- Its actual original center has codimension one, DERIVED from its true
canonical local DVR rather than supplied by a model certificate. -/
theorem center_coheight : Order.coheight (centeredTrait p V (closedPoint V)) = 1 := by
  let := centeredTrait_stalk_isDVR p V
  exact SchemeTraitCenterNativeOrders.center_coheight (centeredTrait p V) (projection p V)
    (centeredTrait_genericProjection p V)

end SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
