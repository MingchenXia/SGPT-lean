import SGPT.PSH.NativeCartierLogReconstruction
import SGPT.PSH.NativeLogBiholomorphicEquivalence

/-! Original logarithmic input gives complete native logarithmic data on an
actual open neighborhood of the SAME original point in its ambient component. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL source input alone gives a complete native logarithmic predicate
on an actual ambient-component open containing the actual original point.
The genuine chosen open/component geometry and dimension equality are internal. -/
theorem original_log_exists_component_neighborhood
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∃ O : Opens (A.componentOpen x),
      (⟨x,mem_connectedComponent⟩ : A.componentOpen x)∈O ∧
      NativeHasLogSingularitiesAlongAnyDimension
        (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) O)
        (fun q : O => u q.val.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨U,hx,hlocal⟩ := original_log_exists_local_native hu x
  let := A.openRestriction_paracompactSpace U
  let B := A.openRestriction U
  let p : U := ⟨x,hx⟩
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  obtain ⟨O,e,heval,hD⟩ :=
    (Classical.choose_spec (exists_native_open_component_q_divisor D U p)).2
  change D.nativeOpenRestrictionComponent U p = _ at hD
  change NativeHasLogSingularitiesAlongAnyDimension (D.nativeOpenRestrictionComponent U p)
    (fun q : B.componentOpen p => u q.val.val) at hlocal
  have hfun : (fun q : O => u q.val.val) ∘ e.toHomeomorph=
      (fun q : B.componentOpen p => u q.val.val) := by
    funext q
    change u (e q).val.val=u q.val.val
    rw [heval q]
    rfl
  rw [hD,←hfun] at hlocal
  have hn := (native_log_preimage_of_dimensionEq_iff
    (A.openRestriction_pointDimension U p)
    (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent p.val) O)
    (fun q : O => u q.val.val) e.toHomeomorph e.contMDiff e.symm.contMDiff).mp hlocal
  refine ⟨O,?_,hn⟩
  let p0 : B.componentOpen p := ⟨p,mem_connectedComponent⟩
  have hpoint : (e p0).val=(⟨x,mem_connectedComponent⟩ : A.componentOpen x) := by
    rw [heval p0]
    rfl
  rw [←hpoint]
  exact (e p0).property

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
