import SGPT.Checks.Literature.BJDivisorial.DVRProperGraph
import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeGenericFieldGraph
import SGPT.Foundations.PublishedEnvelope.ProperPruferGenericExtension

/-! # Actual generic field points of the graph and its finite normalization -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGPT.NAPotential.BJ.Divisorial.DVRProperModel
open Alterations Alterations.Geometry SGPT.Foundations.PublishedEnvelope

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsVariety p]

local instance generic_baseFieldAlgebra : Algebra k X.functionField :=
  p.stalkAlgebra (genericPoint X)

variable (V : Subalgebra k X.functionField) [Algebra.EssFiniteType k V]

include p in
private theorem generic_original_noetherian : AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

/-- The actual open graph inclusion. -/
def graphInclusion : (partialMap p V).domain.toScheme ⟶ graphModel p V :=
  ProjectiveGraphModification.ProperTarget.inclusion p (DVRPresentation.structureMap V)
    (partialMap p V).domain (partialMap p V).hom (partialMap_structure p V)

instance graphInclusion_isDominant : IsDominant (graphInclusion p V) := by
  let := generic_original_noetherian p
  dsimp only [graphInclusion]
  infer_instance

/-- The actual generic point belongs to the spread-out domain. -/
theorem generic_mem_partialDomain : genericPoint X ∈ (partialMap p V).domain :=
  Scheme.PartialMap.mem_domain_ofFromSpecStalk p
    (DVRPresentation.structureMap V) (DVRPresentation.fieldPoint V) (fieldPoint_base p V)

/-- The literal original function-field morphism to the spread-out open. -/
def openGenericPoint : Spec X.functionField ⟶ (partialMap p V).domain.toScheme :=
  (partialMap p V).domain.fromSpecStalkOfMem (genericPoint X) (generic_mem_partialDomain p V)

@[reassoc]
theorem openGenericPoint_inclusion :
    openGenericPoint p V ≫ (partialMap p V).domain.ι = X.fromSpecStalk (genericPoint X) :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

instance openGenericPoint_isDominant : IsDominant (openGenericPoint p V) := by
  let : IsDominant (openGenericPoint p V ≫ (partialMap p V).domain.ι) := by
    rw [openGenericPoint_inclusion]
    exact SGPT.Foundations.PublishedEnvelope.isDominant_fromSpecFunctionField
  exact IsDominant.of_comp_of_isOpenImmersion _ (partialMap p V).domain.ι

/-- The genuine original field point of the graph closure. -/
def graphGenericPoint : Spec X.functionField ⟶ graphModel p V :=
  openGenericPoint p V ≫ graphInclusion p V

instance graphGenericPoint_isDominant : IsDominant (graphGenericPoint p V) := by
  dsimp only [graphGenericPoint]
  infer_instance

@[reassoc]
theorem graphGenericPoint_projection :
    graphGenericPoint p V ≫ graphProjection p V = X.fromSpecStalk (genericPoint X) := by
  rw [graphGenericPoint, Category.assoc]
  change openGenericPoint p V ≫
    (ProjectiveGraphModification.ProperTarget.inclusion p _ _ _ _ ≫
      ProjectiveGraphModification.ProperTarget.projection p _ _ _ _) = _
  rw [ProjectiveGraphModification.ProperTarget.inclusion_projection]
  exact openGenericPoint_inclusion p V

@[reassoc]
theorem graphGenericPoint_presentation :
    graphGenericPoint p V ≫ graphPresentation p V = DVRPresentation.fieldPoint V := by
  rw [graphGenericPoint, Category.assoc]
  change openGenericPoint p V ≫
    (ProjectiveGraphModification.ProperTarget.inclusion p _ _ _ _ ≫
      ProjectiveGraphModification.ProperTarget.projectiveMap p _ _ _ _) = _
  rw [ProjectiveGraphModification.ProperTarget.inclusion_projectiveMap]
  exact Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk p
    (DVRPresentation.structureMap V) (DVRPresentation.fieldPoint V) (fieldPoint_base p V)

/-- The actual original function field is derived from the original generic
projection, rather than supplied as a birationality/equivalence assumption. -/
def graphFunctionFieldEquiv : (graphModel p V).functionField ≃+* X.functionField :=
  SchemeGenericFieldGraph.functionFieldEquiv (graphGenericPoint p V) (graphProjection p V)
    (graphGenericPoint_projection p V)

/-- The SAME original field point of the actual normalized graph. -/
def normalizedGenericPoint : Spec X.functionField ⟶ model p V :=
  Spec.map (CommRingCat.ofHom (graphFunctionFieldEquiv p V).toRingHom) ≫
    IntegralSchemeNormalization.genericLift (graphModel p V)

@[reassoc]
theorem normalizedGenericPoint_normalizationProjection :
    normalizedGenericPoint p V ≫ IntegralSchemeNormalization.projection (graphModel p V) =
      graphGenericPoint p V := by
  rw [normalizedGenericPoint, Category.assoc, IntegralSchemeNormalization.genericLift_comp_projection]
  exact SchemeGenericFieldGraph.fieldHom_fromSpecStalk (graphGenericPoint p V)

@[reassoc]
theorem normalizedGenericPoint_projection :
    normalizedGenericPoint p V ≫ projection p V = X.fromSpecStalk (genericPoint X) := by
  rw [projection, ← Category.assoc, normalizedGenericPoint_normalizationProjection,
    graphGenericPoint_projection]

@[reassoc]
theorem normalizedGenericPoint_presentation :
    normalizedGenericPoint p V ≫ presentation p V = DVRPresentation.fieldPoint V := by
  rw [presentation, ← Category.assoc, normalizedGenericPoint_normalizationProjection,
    graphGenericPoint_presentation]

instance normalizedGenericPoint_isDominant : IsDominant (normalizedGenericPoint p V) := by
  let : IsIso (Spec.map (CommRingCat.ofHom (graphFunctionFieldEquiv p V).toRingHom)) :=
    isIso_SpecMap_iff.mpr (graphFunctionFieldEquiv p V).bijective
  let : IsDominant (IntegralSchemeNormalization.genericLift (graphModel p V)) := by
    dsimp only [IntegralSchemeNormalization.genericLift]
    infer_instance
  dsimp only [normalizedGenericPoint]
  infer_instance

/-- The actual normalized model retains its original coefficient triangle. -/
@[reassoc]
theorem presentation_structure :
    presentation p V ≫ DVRPresentation.structureMap V = projection p V ≫ p := by
  rw [presentation, projection, Category.assoc, Category.assoc]
  congr 1
  exact ProjectiveGraphModification.ProperTarget.structure_triangle p _ _ _ _

instance projection_isDominant : IsDominant (projection p V) := by
  let : IsDominant (normalizedGenericPoint p V ≫ projection p V) := by
    rw [normalizedGenericPoint_projection]
    exact SGPT.Foundations.PublishedEnvelope.isDominant_fromSpecFunctionField
  exact IsDominant.of_comp (normalizedGenericPoint p V) _

end SGPT.NAPotential.BJ.Divisorial.DVRProperModel
