import SGPT.PSH.AtlasNativeTensorAlgebra
import SGPT.PSH.AtlasThetaComponent
import SGPT.PSH.AtlasNefGluing

/-! EXACT global original Kahler-current lower-form hypothesis and genuine
native current/potential readback on actual independently-dimensional components. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open scoped Topology Manifold ContDiff Classical
universe u v
variable {Y : Type v} [TopologicalSpace Y] {B : VariableComplexAtlas Y}
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ENTIRE true native-source residual form readback, by actual full
original tensor addition/scaling; no cohomology or potential flag replaces it. -/
theorem nativeSourcePulledForm_sub (theta omega : AtlasClosedRealOneOneForm B)
    {f : M → Y} (hf : (ofFixedModel n M).IsHolomorphic B f) :
    atlasClosedFormToNative ((theta.add (omega.scale (-1))).holomorphicPullback hf)=
      atlasClosedFormToNative (theta.holomorphicPullback hf)-
      atlasClosedFormToNative (omega.holomorphicPullback hf) := by
  rw [nativeSourcePulledForm_add,nativeSourcePulledForm_scale,neg_one_smul,sub_eq_add_neg]

variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- EXACT source lower-form meaning of a Kahler current: one ACTUAL global
smooth closed strictly positive original form is dominated, expressed by
the original universal theta-PSH criterion for the SAME residual background. -/
def OriginalIsKahlerCurrentPotential (theta : AtlasClosedRealOneOneForm A) (u : X → EReal) : Prop :=
  ∃ omega : AtlasClosedRealOneOneForm A,OriginalFormIsKahler omega ∧
    A.IsThetaPSH (theta.add (omega.scale (-1))) u

variable [T2Space X] [ParacompactSpace X]

/-- The actual original global lower Kahler form and source theta-PSH
hypothesis INTERNALLY produce the accepted native Kahler-current potential
on EVERY actual original component, with SAME potential and theta. -/
theorem original_kahlerCurrent_native_component
    {theta : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : OriginalIsKahlerCurrentPotential theta u) (c : ConnectedComponents X) :
    letI := A.componentChartedSpace (componentAnchor c)
    letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
    IsKahlerCurrentPotential (originalNativeComponentForm theta (componentAnchor c))
      (fun p : A.componentOpen (componentAnchor c) => u p.val) := by
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  obtain ⟨omega,homega,hpot⟩ := hu
  have hdom := original_thetaPsh_native_component hpot (componentAnchor c)
  change IsThetaPshPotential
    (atlasClosedFormToNative ((theta.add (omega.scale (-1))).holomorphicPullback
      (A.nativeComponentInclusion_isHolomorphic (componentAnchor c)))).val
      (fun p : A.componentOpen (componentAnchor c) => u p.val) at hdom
  rw [nativeSourcePulledForm_sub] at hdom
  refine ⟨originalComponentBackground A omega homega c,?_⟩
  exact hdom

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
