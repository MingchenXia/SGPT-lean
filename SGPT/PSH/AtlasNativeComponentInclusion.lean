import SGPT.PSH.AtlasNativeComponentMap
import SGPT.PSH.AtlasThetaHolomorphicPullback
import SGPT.PSH.VariableComponentCountability

open Lean in
local macro "pinnedNativeCoordinateRestrictionKernel" : term =>
  pure (mkIdent (Name.append
    (Name.num `_private.SGPT.PSH.AtlasNativeComponentMap 0)
    `SGPT.PSH.VariableComplexAtlas.restricted_coordinate_contDiffOn))

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- PURE dimension equality substitution, definitionally the existing exact
coordinate mother's chart transport. No new chart geometry is assumed. -/
def nativeCoordinateDimensionTransport {Z : Type*} [TopologicalSpace Z] {d n : ℕ}
    (e : OpenPartialHomeomorph Z (ComplexModel d)) (h : d = n) :
    OpenPartialHomeomorph Z (ComplexModel n) := h ▸ e

/-- EXACT fully read existing generic original-coordinate restriction producer.
Literal private root/type/proof/DIRECT wrapper occurrence are guarded; origin
and maintenance dependence: native-component-inclusion-coordinate-mother-pin.json. -/
theorem nativeOpenSubtypeCoordinate_contDiffOn {d e n m : ℕ}
    (s : OpenPartialHomeomorph X (ComplexModel d))
    (t : OpenPartialHomeomorph Y (ComplexModel e)) (hs : d = n) (ht : e = m)
    (U : Opens X) (V : Opens Y) (hU : Nonempty U) (hV : Nonempty V)
    (f : X → Y) (F : U → V) (hF : ∀ p, (F p : Y) = f p)
    (hcoord : ContDiffOn ℂ ∞ (t ∘ f ∘ s.symm)
      (s.target ∩ s.symm ⁻¹' (f ⁻¹' t.source))) :
    ContDiffOn ℂ ∞
      (((nativeCoordinateDimensionTransport t ht).subtypeRestr hV) ∘ F ∘
        ((nativeCoordinateDimensionTransport s hs).subtypeRestr hU).symm)
      (((nativeCoordinateDimensionTransport s hs).subtypeRestr hU).target ∩
        ((nativeCoordinateDimensionTransport s hs).subtypeRestr hU).symm ⁻¹'
          (F ⁻¹' ((nativeCoordinateDimensionTransport t ht).subtypeRestr hV).source)) :=
  pinnedNativeCoordinateRestrictionKernel s t hs ht U V hU hV f F hF hcoord

/-- ORIGINAL atlas and x internally give genuine all-chart holomorphy of
SAME native-component inclusion into the ORIGINAL independently dimensional atlas. -/
theorem nativeComponentInclusion_isHolomorphic (A : VariableComplexAtlas X) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    (ofFixedModel (A.pointDimension x) (A.componentOpen x)).IsHolomorphic A
      (Subtype.val : A.componentOpen x → X) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  refine ⟨continuous_subtype_val, ?_⟩
  intro e j
  obtain ⟨i, hi⟩ := e.property
  change DifferentiableOn ℂ (A.chart j ∘ Subtype.val ∘ e.val.symm)
    (e.val.target ∩ e.val.symm ⁻¹' ((Subtype.val : A.componentOpen x → X) ⁻¹' (A.chart j).source))
  rw [← hi]
  let V : Opens X := ⊤
  let F : A.componentOpen x → V := fun p => ⟨p.val, mem_univ _⟩
  have hV : Nonempty V := ⟨⟨x, mem_univ _⟩⟩
  have hcoord : ContDiffOn ℂ ∞ (A.chart j ∘ id ∘ (A.chart i.val).symm)
      ((A.chart i.val).target ∩ (A.chart i.val).symm ⁻¹' (id ⁻¹' (A.chart j).source)) := by
    simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Function.comp_id, Function.id_comp, preimage_id] using
      contDiffOn_of_differentiableOn_complex (A.holomorphic i.val j)
        ((A.chart i.val).symm.trans (A.chart j)).open_source
  have h := nativeOpenSubtypeCoordinate_contDiffOn (A.chart i.val) (A.chart j)
    (A.componentChartDimension x i) rfl (A.componentOpen x) V (A.componentNonempty x) hV
    id F (fun _ => rfl) hcoord
  simp only [OpenPartialHomeomorph.subtypeRestr_source] at h
  change ContDiffOn ℂ ∞ (A.chart j ∘ Subtype.val ∘ (A.componentChart x i).symm)
    ((A.componentChart x i).target ∩ (A.componentChart x i).symm ⁻¹'
      ((Subtype.val : A.componentOpen x → X) ⁻¹' (A.chart j).source)) at h
  exact h.differentiableOn (by simp)

/-- ORIGINAL QPSH internally supplies true native component QPSH with its
actual pulled closed background. No native/finite-point/ND certificate is supplied. -/
theorem IsQPSH.nativeComponent [T2Space X] [ParacompactSpace X]
    {A : VariableComplexAtlas X} {u : X → EReal} (hu : A.IsQPSH u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (ofFixedModel (A.pointDimension x) (A.componentOpen x)).IsQPSH
      (fun p : A.componentOpen x => u p.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  apply (hu.comp_holomorphic_iff_component_nonbot (A.nativeComponentInclusion_isHolomorphic x)).mpr
  have hconnected : IsConnected (A.componentOpen x : Set X) := isConnected_connectedComponent
  let : ConnectedSpace (A.componentOpen x) := isConnected_iff_connectedSpace.mp hconnected
  intro p
  obtain ⟨q, hq, hn⟩ := hu.locallyNondegenerate p.val (A.componentOpen x)
    (A.componentOpen x).isOpen p.property
  refine ⟨⟨q, hq⟩, ?_, hn⟩
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ _

end SGPT.PSH.VariableComplexAtlas
