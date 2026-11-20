import SGPT.PSH.AtlasComponentCohomologyEquivalence
import SGPT.PSH.CompactGeometricDivisorClass

/-! The fixed ORIGINAL geometric rational-divisor class is an actual
GLOBAL closed-form quotient class. Its every component has EXACT standard
original prime integration-current sums, including all zero coefficients. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open SGPT.Hodge.BDivChain.SourceAugmentedDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [CompactSpace X]
variable (A : VariableComplexAtlas X)
local instance originalDivisorFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c
local instance originalDivisorFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c
local instance originalDivisorFamilyCompact (c : ConnectedComponents X) : CompactSpace (actualComponentPoint A c) :=
  isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := componentAnchor c)).isCompact
local instance originalDivisorAnchorCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c)))
      (A.componentOpen (componentAnchor c)) := A.componentChartedSpace (componentAnchor c)
local instance originalDivisorAnchorComplex (c : ConnectedComponents X) :
    IsComplexManifold (A.pointDimension (componentAnchor c))
      (A.componentOpen (componentAnchor c)) := A.componentComplexManifold_of_paracompact (componentAnchor c)

/-- The FIXED actual original divisor class, in the GENUINE global
closed-form quotient and independent of any potential, metric or class
certificate. Its normalization is the EXISTING actual prime integration
current class in EVERY actual component, under the PROVED canonical equivalence. -/
def originalGeometricDivisorClass (D : AtlasEffectiveGeometricQDivisor A) : OriginalRealBottChern A :=
  (originalComponentBottChernEquiv A).symm
    (fun c => compact_geometric_divisor_class (D.nativeComponent (componentAnchor c)))

/-- EXACT standard prime-current class readback on EVERY original component. -/
theorem originalGeometricDivisorClass_component (D : AtlasEffectiveGeometricQDivisor A)
    (c : ConnectedComponents X) :
    originalComponentBottChernEquiv A (originalGeometricDivisorClass A D) c=
      compact_geometric_divisor_class (D.nativeComponent (componentAnchor c)) :=
  congrFun ((originalComponentBottChernEquiv A).apply_symm_apply
    (fun d => compact_geometric_divisor_class (D.nativeComponent (componentAnchor d)))) c

/-- EVERY original prime coefficient, including all absent zeros, occurs in
the ACTUAL original integration-current class sum on its own native component.
The original/native prime dictionary and class sum are PROVED, not assumed. -/
theorem originalGeometricDivisorClass_component_current_sum
    (D : AtlasEffectiveGeometricQDivisor A) (c : ConnectedComponents X) :
    HasDivisorClassSumAny
      (fun P => (D.coefficient (A.nativePrimeOriginalCarrier (componentAnchor c) P) : ℝ))
      (originalComponentBottChernEquiv A (originalGeometricDivisorClass A D) c) := by
  rw [originalGeometricDivisorClass_component]
  have h := hasSum_compact_geometric_divisor_class (D.nativeComponent (componentAnchor c))
  simpa only [AtlasEffectiveGeometricQDivisor.nativeComponent_coefficient] using h

/-- The fixed genuine global divisor class is uniquely determined by its
ACTUAL standard prime integration-current classes on all original components. -/
theorem originalGeometricDivisorClass_unique (D : AtlasEffectiveGeometricQDivisor A)
    (alpha : OriginalRealBottChern A)
    (h : ∀ c : ConnectedComponents X,originalComponentBottChernEquiv A alpha c=
      compact_geometric_divisor_class (D.nativeComponent (componentAnchor c))) :
    alpha=originalGeometricDivisorClass A D := by
  apply (originalComponentBottChernEquiv A).injective
  funext c
  exact (h c).trans (originalGeometricDivisorClass_component A D c).symm

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
