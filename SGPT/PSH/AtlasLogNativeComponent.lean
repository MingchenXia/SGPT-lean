import SGPT.PSH.AtlasLogComponentNeighborhood
import SGPT.PSH.NativeLogNeighborhoodNaturality
import SGPT.PSH.NativeLogLocality

/-! The literal original logarithmic predicate produces the ENTIRE native
predicate on every actual original component, with no uniform dimension. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.SourceLogSingularitiesDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- The ORIGINAL finite logarithmic predicate ALONE produces the COMPLETE
native logarithmic predicate on EVERY actual original component. Actual
neighborhoods, reanchors, dimensions and every full coefficient/ideal field
are manufactured internally, with no native or restriction certificate input. -/
theorem original_log_nativeComponent
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    NativeHasLogSingularitiesAlongAnyDimension (D.nativeComponent x)
      (fun q : A.componentOpen x => u q.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  apply native_log_of_local _ _ (hu.1.nativeComponent x)
  intro y
  let := A.componentChartedSpace y.val
  let := A.componentComplexManifold_of_paracompact y.val
  obtain ⟨O,hyO,hO⟩ := original_log_exists_component_neighborhood hu y.val
  let e := A.componentReanchorHomeomorph x y.val y.property
  let he := A.componentReanchorHomeomorph_contMDiff x y.val y.property
  let hei := A.componentReanchorHomeomorph_symm_contMDiff x y.val y.property
  have hdim := (A.pointDimension_eq_on_connectedComponent x y.property).symm
  have hlocal := native_log_neighborhood_preimage_of_dimensionEq hdim (D.nativeComponent y.val)
    (fun q : A.componentOpen y.val => u q.val) e he hei O hO
  rw [←D.nativeComponent_reanchor x y.val y.property] at hlocal
  refine ⟨preimageOpen e O,?_,hlocal⟩
  change e y∈O
  have hpoint : e y=(⟨y.val,mem_connectedComponent⟩ : A.componentOpen y.val) := Subtype.ext rfl
  rw [hpoint]
  exact hyO

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
