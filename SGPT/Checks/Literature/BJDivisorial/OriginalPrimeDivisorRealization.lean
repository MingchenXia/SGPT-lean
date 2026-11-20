import SGPT.Checks.Literature.BJDivisorial.PrimeDivisorNativeData
import SGPT.Checks.Literature.BJDivisorial.DVRProperCenter
import SGPT.Checks.Literature.BJDivisorial.GenericProjectionResidue

/-!
# Actual realization as the source PrimeDivisorOver X

Starting with a genuine essentially finite type DVR in the ORIGINAL
function field, construct the normal proper graph model, its whole trait
and its actual codimension-one center. The literal original generic
residueFieldMap is proved bijective. This is a geometric producer for the
original divisorial dictionary; no model/correspondence certificate enters.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [hProj : IsProjective p]

local instance realization_originalProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

local instance realization_originalVariety : Alterations.IsVariety p := {}

variable (V : letI := p.stalkAlgebra (genericPoint X); Subalgebra ℂ X.functionField) [Algebra.EssFiniteType ℂ V]
  [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]

/-- A genuine geometric DVR in the actual original function field produces
an ACTUAL source prime divisor on a normal proper birational model. -/
def primeDivisorOfGeometricDVR : PrimeDivisorOver X where
  Y := DVRProperModel.model p V
  π := DVRProperModel.projection p V
  normal := DVRProperModel.model_stalk_normal p V
  birational := genericProjection_residueFieldMap_bijective
    (DVRProperModel.projection p V) (DVRProperModel.normalizedGenericPoint p V)
    (DVRProperModel.normalizedGenericPoint_projection p V)
  point := DVRProperModel.centeredTrait p V (closedPoint V)
  coheight_point := DVRProperModel.center_coheight p V

/-- Its actual original center stalk is canonically the WHOLE original DVR. -/
def primeDivisorStalkEquiv :
    (primeDivisorOfGeometricDVR p V).Y.presheaf.stalk
      (primeDivisorOfGeometricDVR p V).point ≃+* V := by
  let := DVRProperModel.centeredTrait_stalk_isDVR p V
  exact SchemeTraitCenterNativeOrders.stalkRingEquiv (DVRProperModel.centeredTrait p V)
    (DVRProperModel.projection p V) (DVRProperModel.centeredTrait_genericProjection p V)

/-- The canonical local map, rather than an arbitrary ring identification,
is the original whole stalk equivalence. -/
theorem primeDivisorStalkEquiv_apply
    (a : (primeDivisorOfGeometricDVR p V).Y.presheaf.stalk
      (primeDivisorOfGeometricDVR p V).point) :
    primeDivisorStalkEquiv p V a = Scheme.stalkClosedPointTo (DVRProperModel.centeredTrait p V) a := rfl

/-- The literal original function-field order has the true canonical DVR
valuation at every nonzero fraction of the constructed original model. -/
theorem primeDivisor_nativeOrder_value (f : (primeDivisorOfGeometricDVR p V).Y.functionField)
    (hf : f ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField
      ((SchemeGenericFieldGraph.fieldHom
        (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
          DVRProperModel.centeredTrait p V)) f) =
      WithZero.exp (- (primeDivisorOfGeometricDVR p V).Y.ord f
        (primeDivisorOfGeometricDVR p V).point) := by
  let := DVRProperModel.centeredTrait_stalk_isDVR p V
  exact SchemeTraitCenterNativeOrders.valuation_eq_exp_neg_ord
    (DVRProperModel.centeredTrait p V) (DVRProperModel.projection p V)
    (DVRProperModel.centeredTrait_genericProjection p V) f hf

end SGPT.NAPotential.BJ.Divisorial
