import SGPT.Checks.Comparison.BJPair3DivDVRPresentationCompactification
import SGPT.Support.Alterations.Geometry.ProjectiveGraphModificationProperTarget
import SGPT.Foundations.Envelope.AlgGeom.SchemeStalkCoefficients
import SGPT.Foundations.Envelope.AlgGeom.FiniteSchemeNormalization
import SGPT.Foundations.Envelope.AlgGeom.NormalSchemeNormalization
import SGPT.Foundations.Envelope.AlgGeom.SchemeDVRNormalizationLift
import Mathlib.AlgebraicGeometry.Birational.RationalMap

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DVRProperGraph.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# The genuine graph model of the finite DVR presentation over original X

The actual field point of its constructed projective compactification
spreads over a dense open of X. Its actual graph closure is proper over X.
Finite normalization gives a normal proper integral model. All schemes,
partial maps and projections are constructed from X, its coefficient map
and the actual DVR, without a supplied birational model or dictionary.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry SGPT.Foundations.Envelope

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsVariety p]

local instance original_functionField_algebra : Algebra k X.functionField :=
  p.stalkAlgebra (genericPoint X)

variable (V : Subalgebra k X.functionField) [Algebra.EssFiniteType k V]

include p in
private theorem original_noetherian : AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

/-- The actual generic coefficient triangle, using p's genuine stalk algebra. -/
theorem fieldPoint_base :
    DVRPresentation.fieldPoint V ≫ DVRPresentation.structureMap V =
      X.fromSpecStalk (genericPoint X) ≫ p := by
  rw [DVRPresentation.fieldPoint_structure, SchemeStalkCoefficients.fromSpecStalk_structureMap]
  rfl

/-- The actual field point spread to a genuine dense open of original X. -/
def partialMap : X.PartialMap (DVRPresentation.compactification V) :=
  Scheme.PartialMap.ofFromSpecStalk p (DVRPresentation.structureMap V)
    (DVRPresentation.fieldPoint V) (fieldPoint_base p V)

@[reassoc]
theorem partialMap_structure :
    (partialMap p V).hom ≫ DVRPresentation.structureMap V = (partialMap p V).domain.ι ≫ p :=
  Scheme.PartialMap.ofFromSpecStalk_comp p (DVRPresentation.structureMap V)
    (DVRPresentation.fieldPoint V) (fieldPoint_base p V)

instance partialMap_nonempty : Nonempty (partialMap p V).domain :=
  ⟨⟨genericPoint X, Scheme.PartialMap.mem_domain_ofFromSpecStalk p
    (DVRPresentation.structureMap V) (DVRPresentation.fieldPoint V) (fieldPoint_base p V)⟩⟩

/-- The actual integral schematic graph closure. -/
def graphModel : Scheme.{u} :=
  ProjectiveGraphModification.ProperTarget.modification p (DVRPresentation.structureMap V)
    (partialMap p V).domain (partialMap p V).hom (partialMap_structure p V)

/-- The actual proper graph projection to the original scheme. -/
def graphProjection : graphModel p V ⟶ X :=
  ProjectiveGraphModification.ProperTarget.projection p (DVRPresentation.structureMap V)
    (partialMap p V).domain (partialMap p V).hom (partialMap_structure p V)

/-- The actual everywhere-defined presentation map on the graph. -/
def graphPresentation : graphModel p V ⟶ DVRPresentation.compactification V :=
  ProjectiveGraphModification.ProperTarget.projectiveMap p (DVRPresentation.structureMap V)
    (partialMap p V).domain (partialMap p V).hom (partialMap_structure p V)

instance graphProjection_isProper : IsProper (graphProjection p V) := by
  dsimp only [graphProjection]
  infer_instance

instance graphModel_isIntegral : IsIntegral (graphModel p V) := by
  let := original_noetherian p
  dsimp only [graphModel]
  infer_instance

/-- The actual normal integral model, using cached finite normalization. -/
def model : Scheme.{u} := IntegralSchemeNormalization.normalization (graphModel p V)

/-- Its literal projection to original X. -/
def projection : model p V ⟶ X :=
  IntegralSchemeNormalization.projection (graphModel p V) ≫ graphProjection p V

/-- Its actual global presentation map to the original compactification. -/
def presentation : model p V ⟶ DVRPresentation.compactification V :=
  IntegralSchemeNormalization.projection (graphModel p V) ≫ graphPresentation p V

instance model_isIntegral : IsIntegral (model p V) := by
  dsimp only [model]
  infer_instance

/-- Every stalk on this actual constructed normal model is integrally closed. -/
theorem model_stalk_normal (y : model p V) : IsIntegrallyClosed ((model p V).presheaf.stalk y) :=
  IntegralSchemeNormalization.stalk_isIntegrallyClosed (graphModel p V) y

instance projection_isProper : IsProper (projection p V) :=
  IntegralSchemeNormalization.projection_comp_isProper k (graphModel p V)
    (graphProjection p V ≫ p) (graphProjection p V)

instance model_locallyNoetherian : IsLocallyNoetherian (model p V) :=
  LocallyOfFiniteType.isLocallyNoetherian (projection p V ≫ p)

end SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
