import SGPT.PSH.GeometricDivisorMetricAlgebra

/-! Dimension zero retains the SAME complete literal log presentation;
its empty genuine prime type gives an actual zero metric and local residual. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]

/-- ALL literal local fields, including the bounded remainder on the entire
original open, give local type along the actual zero metric in dimension0. -/
theorem native_zero_log_metric_local_type
    {D : EffectiveGeometricQDivisor 0 M} {u : M → EReal}
    (hu : NativeHasLogSingularitiesAlongAnyDimension D u) :
    HasLocalDivisorLogType (MeteredDivisorOperations.zero 0 M) u := by
  intro x
  obtain ⟨U,hxU,r,W,a,p,R,C,_hW,_ha,_hp,_hideal,_hcoeff,hC,hR,hlog⟩ := hu.2 x
  have hreal (y : U) : u y=(R y : EReal) := by
    have hsum : (∑ i,((a i : ℝ) : EReal)*logNormSq (p i y))=0 :=
      Finset.sum_eq_zero (fun i _ => isEmptyElim (W i))
    simpa only [hsum,zero_add] using hlog y
  let b : M → ℝ := fun y => if hy : y∈U then R ⟨y,hy⟩ else 0
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel 0) M
  obtain ⟨V,⟨hV,hxV,hconn⟩,hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (U.isOpen.mem_nhds hxU)
  refine ⟨V,b,C,hC,hV,hconn,hxV,?_,?_⟩
  · intro y hy
    have hb : b y=R ⟨y,hVU hy⟩ := dif_pos (hVU hy)
    rw [hb]
    exact hR ⟨y,hVU hy⟩
  · intro y hy
    change u y=(0 : EReal)+(b y : EReal)
    have hb : b y=R ⟨y,hVU hy⟩ := dif_pos (hVU hy)
    rw [zero_add,hb]
    exact hreal ⟨y,hVU hy⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
