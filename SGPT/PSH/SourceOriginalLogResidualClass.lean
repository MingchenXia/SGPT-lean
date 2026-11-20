import SGPT.PSH.AtlasCohomologyAlgebra
import SGPT.PSH.AtlasDivisorClass
import SGPT.PSH.AtlasNativeFormGluing
import SGPT.PSH.AtlasNefGluing
import SGPT.PSH.AtlasNefClass
import SGPT.PSH.AtlasCurrentComponent
import SGPT.PSH.SourceNativeLogResidualClass

/-! Literal original varying-atlas logsingrem: BOTH nef and Kahler
conclusions for the SAME fixed genuine GLOBAL original divisor class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [CompactSpace X]
variable (A : VariableComplexAtlas X)
local instance originalResidualFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c
local instance originalResidualFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c
local instance originalResidualFamilyCompact (c : ConnectedComponents X) : CompactSpace (actualComponentPoint A c) :=
  isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := componentAnchor c)).isCompact
local instance originalResidualAnchorCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c)))
      (A.componentOpen (componentAnchor c)) := A.componentChartedSpace (componentAnchor c)
local instance originalResidualAnchorComplex (c : ConnectedComponents X) :
    IsComplexManifold (A.pointDimension (componentAnchor c))
      (A.componentOpen (componentAnchor c)) := A.componentComplexManifold_of_paracompact (componentAnchor c)

/-- The SAME original GLOBAL residual class has EXACTLY the SAME original
native theta minus fixed prime-current divisor class in EVERY component. -/
theorem original_residual_class_component (theta : AtlasClosedRealOneOneForm A)
    (D : AtlasEffectiveGeometricQDivisor A) (c : ConnectedComponents X) :
    originalComponentBottChernEquiv A (originalClass theta-originalGeometricDivisorClass A D) c=
      RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c))-
        compact_geometric_divisor_class (D.nativeComponent (componentAnchor c)) := by
  have hmap := (originalComponentBottChernLinearEquiv (A := A)).map_sub
    (originalClass theta) (originalGeometricDivisorClass A D)
  exact (congrFun hmap c).trans
    (congrArg₂ (·-·) (originalComponentBottChernEquiv_class A theta c)
      (originalGeometricDivisorClass_component A D c))

/-- Original source Kahler class means an ACTUAL original GLOBAL smooth
closed strictly positive representative in the GENUINE global quotient. -/
def OriginalClassIsKahler (alpha : OriginalRealBottChern A) : Prop :=
  ∃ kappa : AtlasClosedRealOneOneForm A,OriginalFormIsKahler kappa ∧ originalClass kappa=alpha

/-- Literal ORIGINAL nef clause: compact Kahler X, original theta-PSH,
original D and complete literal source logarithms internally give nefness
of the SAME genuine GLOBAL class {theta}-{D}, with ONE actual global smooth
potential for every epsilon. No native/class/metric/residual output premises. -/
theorem original_log_divisor_class_nef
    (omega theta : AtlasClosedRealOneOneForm A) (homega : OriginalFormIsKahler omega)
    (D : AtlasEffectiveGeometricQDivisor A) (u : X → EReal)
    (hu : A.IsThetaPSH theta u) (hlog : SourceHasLogSingularitiesAlong D u) :
    OriginalClassNefWithRespectTo omega (originalClass theta-originalGeometricDivisorClass A D) := by
  let alpha : OriginalRealBottChern A := originalClass theta-originalGeometricDivisorClass A D
  let eta : AtlasClosedRealOneOneForm A := alpha.out
  have heta : originalClass eta=alpha := Quotient.out_eq alpha
  have hnatives (c : ConnectedComponents X) :
      NefWithRespectTo (originalComponentBackground A omega homega c)
        (originalNativeComponentForm eta (componentAnchor c)) := by
    have hnative := native_original_log_divisor_class_nef
      (originalComponentBackground A omega homega c)
      (originalNativeComponentForm theta (componentAnchor c)) (D.nativeComponent (componentAnchor c))
      (fun p : A.componentOpen (componentAnchor c) => u p.val)
      (original_thetaPsh_native_component hu (componentAnchor c))
      (original_log_nativeComponent hlog (componentAnchor c))
    have hread : RealBottChern.ofRepresentative (originalNativeComponentForm eta (componentAnchor c))=
        RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c))-
          compact_geometric_divisor_class (D.nativeComponent (componentAnchor c)) :=
      (originalComponentBottChernEquiv_class A eta c).symm.trans
        ((congrArg (fun q => originalComponentBottChernEquiv A q c) heta).trans
          (original_residual_class_component A theta D c))
    have hclass : ClassNefWithRespectTo (originalComponentBackground A omega homega c)
        (RealBottChern.ofRepresentative (originalNativeComponentForm eta (componentAnchor c))) := hread ▸ hnative
    exact hclass
  have hglobal := original_nef_of_native_components A omega eta homega hnatives
  have hclass : OriginalClassNefWithRespectTo omega (originalClass eta) := hglobal
  exact (congrArg (OriginalClassNefWithRespectTo omega) heta).mp hclass

/-- Literal ORIGINAL Kahler clause: the SAME original dominated GLOBAL
Kahler form/current and literal source log hypothesis produce an ACTUAL
GLOBAL smooth closed strictly positive representative of SAME {theta}-{D}.
No component flag, native current/class certificate or fixed dimension. -/
theorem original_log_divisor_class_kahler
    (theta : AtlasClosedRealOneOneForm A) (D : AtlasEffectiveGeometricQDivisor A) (u : X → EReal)
    (hu : OriginalIsKahlerCurrentPotential theta u)
    (hlog : SourceHasLogSingularitiesAlong D u) :
    OriginalClassIsKahler A (originalClass theta-originalGeometricDivisorClass A D) := by
  have hnatives (c : ConnectedComponents X) :
      ∃ kappa : ClosedRealOneOneForm (actualComponentDimension A c) (actualComponentPoint A c),
      kappa.val.IsKahler ∧ RealBottChern.ofRepresentative kappa=
        RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c))-
          compact_geometric_divisor_class (D.nativeComponent (componentAnchor c)) :=
    native_original_log_divisor_class_kahler
      (originalNativeComponentForm theta (componentAnchor c)) (D.nativeComponent (componentAnchor c))
      (fun p : A.componentOpen (componentAnchor c) => u p.val)
      (original_kahlerCurrent_native_component hu c) (original_log_nativeComponent hlog (componentAnchor c))
  choose kappa hkappa hclass using hnatives
  refine ⟨originalGluedNativeForm A kappa,originalGluedNativeForm_isKahler A kappa hkappa,?_⟩
  apply (originalComponentBottChernEquiv A).injective
  funext c
  exact (originalGluedNativeForm_component_class A kappa c).trans
    ((hclass c).trans (original_residual_class_component A theta D c).symm)

/-- ENTIRE literal original lma:logsingrem, BOTH source clauses and SAME
actual original global class, with no connectedness/nonempty/uniform-dimension
or source-provided native/metric/residual/class/positivity output certificates. -/
theorem original_logsingrem_both_clauses
    (omega theta : AtlasClosedRealOneOneForm A) (homega : OriginalFormIsKahler omega)
    (D : AtlasEffectiveGeometricQDivisor A) (u : X → EReal)
    (hu : A.IsThetaPSH theta u) (hlog : SourceHasLogSingularitiesAlong D u) :
    OriginalClassNefWithRespectTo omega (originalClass theta-originalGeometricDivisorClass A D) ∧
      (OriginalIsKahlerCurrentPotential theta u →
        OriginalClassIsKahler A (originalClass theta-originalGeometricDivisorClass A D)) :=
  ⟨original_log_divisor_class_nef A omega theta homega D u hu hlog,
    fun hK => original_log_divisor_class_kahler A theta D u hK hlog⟩

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
