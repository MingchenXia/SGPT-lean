import SGPT.PSH.AtlasComponentCohomologyEquivalence
import SGPT.PSH.AtlasBiholomorphicDerivative

/-! ACTUAL closed native forms glue to a genuine original global closed
form, with true cohomology readback and genuine global Kahler positivity. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
variable (A : VariableComplexAtlas X)
local instance originalFormFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c
local instance originalFormFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c

/-- Actual native closed (1,1) forms GLUE to one genuine original global
closed tensor on X, using the produced true component biholomorphism. -/
def originalGluedNativeForm
    (F : ∀ c : ConnectedComponents X,ClosedRealOneOneForm (actualComponentDimension A c) (actualComponentPoint A c)) :
    AtlasClosedRealOneOneForm A :=
  (sigmaGluedForm F).holomorphicPullback (actualComponentHomeomorph_inverse_isHolomorphic A)

/-- EVERY actual native class is recovered by genuine original restriction,
with full tensor inverse chain-rule readback and accepted native normalization. -/
theorem originalGluedNativeForm_component_class
    (F : ∀ c : ConnectedComponents X,ClosedRealOneOneForm (actualComponentDimension A c) (actualComponentPoint A c))
    (c : ConnectedComponents X) :
    originalComponentBottChernEquiv A (originalClass (originalGluedNativeForm A F)) c=
      RealBottChern.ofRepresentative (F c) := by
  change RealBottChern.ofRepresentative
    (sigmaRestrictedForm (((sigmaGluedForm F).holomorphicPullback
      (actualComponentHomeomorph_inverse_isHolomorphic A)).holomorphicPullback
        (actualComponentHomeomorph_isHolomorphic A)) c)=_
  calc
    _ = RealBottChern.ofRepresentative (sigmaRestrictedForm (sigmaGluedForm F) c) := by
      apply RealBottChern.ofRepresentative_eq_of_geometricallyEq
      intro e z hz
      exact original_biholomorphic_pullback_roundtrip_coeff (sigmaGluedForm F) (actualComponentHomeomorph A)
        (actualComponentHomeomorph_isHolomorphic A) (actualComponentHomeomorph_inverse_isHolomorphic A) ⟨c,e⟩ hz
    _ = _ := sigmaRestrictedGluedForm_class F c

/-- Genuine original GLOBAL class gluing: the inverse equivalence is the
class of an ACTUAL globally glued smooth closed form, not merely a product flag. -/
theorem originalGluedNativeForm_class
    (F : ∀ c : ConnectedComponents X,ClosedRealOneOneForm (actualComponentDimension A c) (actualComponentPoint A c)) :
    originalClass (originalGluedNativeForm A F)=
      (originalComponentBottChernEquiv A).symm (fun c => RealBottChern.ofRepresentative (F c)) := by
  apply (originalComponentBottChernEquiv A).injective
  funext c
  exact (originalGluedNativeForm_component_class A F c).trans
    (congrFun ((originalComponentBottChernEquiv A).apply_symm_apply
      (fun d => RealBottChern.ofRepresentative (F d))) c).symm

/-- ACTUAL smooth native Kahler representatives GLUE into ONE original
GLOBAL smooth closed strictly positive form on ALL original charts. -/
theorem originalGluedNativeForm_isKahler
    (F : ∀ c : ConnectedComponents X,ClosedRealOneOneForm (actualComponentDimension A c) (actualComponentPoint A c))
    (hF : ∀ c,(F c).val.IsKahler) : OriginalFormIsKahler (originalGluedNativeForm A F) :=
  (sigmaGluedForm_isKahler F hF).biholomorphicPullback (actualComponentHomeomorph A).symm
    (actualComponentHomeomorph_inverse_isHolomorphic A) (actualComponentHomeomorph_isHolomorphic A)

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
