import SGPT.PSH.AtlasCohomologyPullback

/-! The original universal theta-PSH source condition gives the SAME
actual native theta-PSH potential on every internally produced component. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- Genuine original theta-PSH, including its produced local nondegeneracy,
restricts to the SAME actual native original theta and potential. No native
PSH/finite-point or connectedness certificate is supplied as source hypothesis. -/
theorem original_thetaPsh_native_component {theta : AtlasClosedRealOneOneForm A}
    {u : X → EReal} (hu : A.IsThetaPSH theta u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    IsThetaPshPotential (originalNativeComponentForm theta x).val
      (fun p : A.componentOpen x => u p.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  have hqpsh : A.IsQPSH u := ⟨theta,hu⟩
  have htheta : (ofFixedModel (A.pointDimension x) (A.componentOpen x)).IsThetaPSH
      (theta.holomorphicPullback (A.nativeComponentInclusion_isHolomorphic x))
      (fun p : A.componentOpen x => u p.val) := by
    apply (hu.comp_holomorphic_iff_component_nonbot (A.nativeComponentInclusion_isHolomorphic x)).mpr
    let : ConnectedSpace (A.componentOpen x) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    intro p
    obtain ⟨q,hq,hqfin⟩ := hqpsh.locallyNondegenerate p.val (A.componentOpen x)
      (A.componentOpen x).isOpen p.property
    refine ⟨⟨q,hq⟩,?_,hqfin⟩
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact mem_univ _
  exact (isThetaPSH_iff_nativeThetaPotential _ _).mp htheta

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
