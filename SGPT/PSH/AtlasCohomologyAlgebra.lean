import SGPT.PSH.AtlasComponentCohomologyEquivalence
import SGPT.PSH.AtlasNativeTensorAlgebra
import Mathlib.Algebra.Module.TransferInstance

/-! Real vector space algebra on the ACTUAL global original quotient,
transported by the PROVED equivalence and checked against original tensors. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual whole tensor addition commutes with genuine holomorphic pullback. -/
theorem original_holomorphicPullback_add_coeff (theta eta : AtlasClosedRealOneOneForm B)
    {f : X → Y} (hf : A.IsHolomorphic B f) (i : A.Index)
    {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    ((theta.add eta).holomorphicPullback hf).coeff i z=
      (theta.holomorphicPullback hf).coeff i z+(eta.holomorphicPullback hf).coeff i z := by
  obtain ⟨j,hj⟩ := B.cover (f ((A.chart i).symm z))
  have hzj : z∈atlasCoordinateDomain A B f i j := ⟨hz,hj⟩
  rw [(theta.add eta).holomorphicPullback_coeff hf i j hzj,
    theta.holomorphicPullback_coeff hf i j hzj,eta.holomorphicPullback_coeff hf i j hzj]
  ext w
  rfl

/-- Actual original scalar multiplication commutes with genuine pullback. -/
theorem original_holomorphicPullback_scale_coeff (theta : AtlasClosedRealOneOneForm B)
    (a : ℝ) {f : X → Y} (hf : A.IsHolomorphic B f) (i : A.Index)
    {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    ((theta.scale a).holomorphicPullback hf).coeff i z=a • (theta.holomorphicPullback hf).coeff i z := by
  obtain ⟨j,hj⟩ := B.cover (f ((A.chart i).symm z))
  have hzj : z∈atlasCoordinateDomain A B f i j := ⟨hz,hj⟩
  rw [(theta.scale a).holomorphicPullback_coeff hf i j hzj,
    theta.holomorphicPullback_coeff hf i j hzj]
  ext w
  rfl

variable [T2Space X] [ParacompactSpace X]

/-- The genuine global quotient has a real additive group, transported along
the PROVED canonical actual quotient equivalence, without extra class flags. -/
instance originalRealBottChernAddCommGroup : AddCommGroup (OriginalRealBottChern A) :=
  (originalComponentBottChernEquiv A).addCommGroup

/-- The genuine global quotient is a REAL vector space with exactly the
accepted native scalar convention. Representative compatibility is proved below. -/
instance originalRealBottChernModule : Module ℝ (OriginalRealBottChern A) :=
  Equiv.module ℝ (originalComponentBottChernEquiv A)

/-- The PROVED actual quotient equivalence is a genuine real linear equivalence. -/
def originalComponentBottChernLinearEquiv :=
  (originalComponentBottChernEquiv A).linearEquiv ℝ

/-- Actual class restriction preserves the TRUE source sum. -/
theorem originalComponentBottChernEquiv_add (q r : OriginalRealBottChern A) :
    originalComponentBottChernEquiv A (q+r)=
      originalComponentBottChernEquiv A q+originalComponentBottChernEquiv A r :=
  (originalComponentBottChernLinearEquiv (A := A)).map_add q r

/-- Actual class restriction preserves the TRUE source scalar action. -/
theorem originalComponentBottChernEquiv_smul (a : ℝ) (q : OriginalRealBottChern A) :
    originalComponentBottChernEquiv A (a • q)=a • originalComponentBottChernEquiv A q :=
  (originalComponentBottChernLinearEquiv (A := A)).map_smul a q

/-- Full ORIGINAL tensor addition represents the genuine global quotient
sum; this proves EXACT source representative meaning of the transported algebra. -/
theorem originalClass_add (theta eta : AtlasClosedRealOneOneForm A) :
    originalClass (theta.add eta)=originalClass theta+originalClass eta := by
  apply (originalComponentBottChernEquiv A).injective
  funext c
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  let : AddCommGroup (RealBottChern (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c))) := RealBottChern.instAddCommGroup
  let : Module ℝ (RealBottChern (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c))) := RealBottChern.instModule
  calc
    _ = RealBottChern.ofRepresentative (originalNativeComponentForm (theta.add eta) (componentAnchor c)) :=
      originalComponentBottChernEquiv_class A (theta.add eta) c
    _ = RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c))+
        RealBottChern.ofRepresentative (originalNativeComponentForm eta (componentAnchor c)) :=
      nativeSourcePulledForm_class_add (n := A.pointDimension (componentAnchor c))
        (M := A.componentOpen (componentAnchor c)) theta eta (A.nativeComponentInclusion_isHolomorphic (componentAnchor c))
    _ = originalComponentBottChernEquiv A (originalClass theta) c+
        originalComponentBottChernEquiv A (originalClass eta) c :=
      congrArg₂ (·+·) (originalComponentBottChernEquiv_class A theta c).symm
        (originalComponentBottChernEquiv_class A eta c).symm
    _ = _ := (congrFun (originalComponentBottChernEquiv_add (originalClass theta) (originalClass eta)) c).symm

/-- Full ORIGINAL real tensor scaling represents the genuine quotient
scalar action, with EXACT accepted native normalization in EVERY component. -/
theorem originalClass_scale (theta : AtlasClosedRealOneOneForm A) (a : ℝ) :
    originalClass (theta.scale a)=a • originalClass theta := by
  apply (originalComponentBottChernEquiv A).injective
  funext c
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  let : AddCommGroup (RealBottChern (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c))) := RealBottChern.instAddCommGroup
  let : Module ℝ (RealBottChern (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c))) := RealBottChern.instModule
  calc
    _ = RealBottChern.ofRepresentative (originalNativeComponentForm (theta.scale a) (componentAnchor c)) :=
      originalComponentBottChernEquiv_class A (theta.scale a) c
    _ = a • RealBottChern.ofRepresentative (originalNativeComponentForm theta (componentAnchor c)) :=
      nativeSourcePulledForm_class_scale (n := A.pointDimension (componentAnchor c))
        (M := A.componentOpen (componentAnchor c)) theta a (A.nativeComponentInclusion_isHolomorphic (componentAnchor c))
    _ = a • originalComponentBottChernEquiv A (originalClass theta) c :=
      congrArg (a • ·) (originalComponentBottChernEquiv_class A theta c).symm
    _ = _ := (congrFun (originalComponentBottChernEquiv_smul a (originalClass theta)) c).symm

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
