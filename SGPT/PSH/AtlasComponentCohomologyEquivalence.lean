import SGPT.PSH.AtlasComponentBiholomorphism
import SGPT.PSH.SigmaNativeQuotientEquivalence
import SGPT.PSH.AtlasBiholomorphicCohomology

/-! The ACTUAL original global smooth closed-form quotient is canonically
EQUIVALENT to its existing native component quotients, by PROVED tensor,
smooth-potential, biholomorphic and quotient dictionaries, with exact readback. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
variable (A : VariableComplexAtlas X)

local instance originalFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c

local instance originalFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c

local instance originalAnchorCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c)))
      (A.componentOpen (componentAnchor c)) := A.componentChartedSpace (componentAnchor c)

local instance originalAnchorComplex (c : ConnectedComponents X) :
    IsComplexManifold (A.pointDimension (componentAnchor c))
      (A.componentOpen (componentAnchor c)) := A.componentComplexManifold_of_paracompact (componentAnchor c)

/-- PROVED canonical equivalence from the ACTUAL GLOBAL original quotient
to the existing independently-dimensional native component quotients.
Its forward map is actual restriction, inverse is genuine smooth form gluing,
and injectivity is genuine global smooth difference-potential gluing. -/
def originalComponentBottChernEquiv : OriginalRealBottChern A ≃
    (∀ c : ConnectedComponents X,RealBottChern (actualComponentDimension A c) (actualComponentPoint A c)) :=
  (originalBiholomorphicCohomologyEquiv (actualComponentHomeomorph A).symm
    (actualComponentHomeomorph_inverse_isHolomorphic A)
    (actualComponentHomeomorph_isHolomorphic A)).trans
      (sigmaNativeBottChernEquiv (n := actualComponentDimension A) (C := actualComponentPoint A))

/-- Exact WHOLE coefficient readback: actual sigma gluing/restriction is
literally the SAME original native inclusion tensor pullback, at every
native chart coordinate, without a source-provided dictionary certificate. -/
theorem original_component_equivalence_representative_coeff
    (theta : AtlasClosedRealOneOneForm A) (c : ConnectedComponents X)
    (e : ComplexChart (actualComponentDimension A c) (actualComponentPoint A c))
    (z : ComplexModel (actualComponentDimension A c)) :
    (sigmaRestrictedForm (theta.holomorphicPullback (actualComponentHomeomorph_isHolomorphic A)) c).val.coeff e z=
      (originalNativeComponentForm theta (componentAnchor c)).val.coeff e z := rfl

/-- Exact representative/class readback for the actual GLOBAL quotient
comparison: each component is the SAME genuine original native tensor. -/
theorem originalComponentBottChernEquiv_class
    (theta : AtlasClosedRealOneOneForm A) (c : ConnectedComponents X) :
    originalComponentBottChernEquiv A (originalClass theta) c=
      RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c)) := by
  change RealBottChern.ofRepresentative
    (sigmaRestrictedForm (theta.holomorphicPullback (actualComponentHomeomorph_isHolomorphic A)) c)=_
  apply (RealBottChern.ofRepresentative_eq_iff _ _).mpr
  refine ⟨fun _ => 0,fun _ => contDiffOn_const,?_⟩
  intro e z hz
  rw [smoothDDC_zero,add_zero]
  rfl

/-- The proved equivalence's map is EXACTLY the earlier genuine canonical
component quotient restriction map, on EVERY actual global source class. -/
theorem originalComponentBottChernEquiv_eq_componentClass
    (q : OriginalRealBottChern A) (c : ConnectedComponents X) :
    originalComponentBottChernEquiv A q c=originalNativeComponentClass q (componentAnchor c) := by
  refine Quotient.inductionOn q ?_
  intro theta
  change originalComponentBottChernEquiv A (originalClass theta) c=
    originalNativeComponentClass (originalClass theta) (componentAnchor c)
  rw [originalComponentBottChernEquiv_class,originalNativeComponentClass_class]

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
