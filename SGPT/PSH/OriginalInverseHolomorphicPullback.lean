import SGPT.PSH.AtlasModificationComponentDimension
import SGPT.Toric.ThetaPSHExtension

/-! Genuine original inverse-holomorphic PSH pullback, including nonpole
production through an actual open partial homeomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- An actual inverse holomorphic open map preserves the original PSH
predicate on every genuine open subdomain. Nondegeneracy is transported
through the actual inverse equations, never a hypothesis on the output. -/
theorem IsPSHOn.comp_openPartialHolomorphicInverse
    {e : OpenPartialHomeomorph X Y} {w : X → EReal} {O : Set X} {U : Set Y}
    (hw : A.IsPSHOn w O) (hO : IsOpen O) (hU : IsOpen U)
    (hUt : U ⊆ e.target) (hmap : MapsTo e.symm U O)
    (he : B.IsHolomorphicOn A e.symm e.target) :
    B.IsPSHOn (w ∘ e.symm) U := by
  apply (isPSHOn_iff_chart_and_nondegenerate hU).mpr
  constructor
  · intro j z hz
    obtain ⟨i, hi⟩ := A.cover (e.symm ((B.chart j).symm z))
    let Q := U ∩ e.symm ⁻¹' (A.chart i).source
    let D := (B.chart j).target ∩ (B.chart j).symm ⁻¹' Q
    have hQ : IsOpen Q := by
      have h := e.symm.isOpen_inter_preimage (A.chart i).open_source
      have hEq : Q=U ∩ (e.target ∩ e.symm ⁻¹' (A.chart i).source) := by
        ext x
        exact ⟨fun hx => ⟨hx.1,hUt hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
      rw [hEq]
      exact hU.inter h
    have hD : IsOpen D := (B.chart j).isOpen_inter_preimage_symm hQ
    have hzD : z∈D := ⟨hz.1,hz.2,hi⟩
    have hsub : D ⊆ (B.chart j).target ∩ (B.chart j).symm ⁻¹'
        (e.target ∩ e.symm ⁻¹' (A.chart i).source) :=
      fun _ hy => ⟨hy.1,hUt hy.2.1,hy.2.2⟩
    have hF : DifferentiableOn ℂ (atlasCoordinateMap B A e.symm j i) D :=
      (he.2 j i).mono hsub
    have hFi : atlasCoordinateMap B A e.symm j i z ∈
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' O := by
      refine ⟨(A.chart i).map_source hi,?_⟩
      change (A.chart i).symm ((A.chart i) (e.symm ((B.chart j).symm z))) ∈ O
      rw [(A.chart i).left_inv hi]
      exact hmap hz.2
    have hp := Pending.HolomorphicPullback.plurisubharmonicAt_comp_holomorphic
      hD hF hzD (hw.chartPlurisubharmonic i _ hFi)
    apply hp.congr
    filter_upwards [hD.mem_nhds hzD] with y hy
    change w ((A.chart i).symm ((A.chart i) (e.symm ((B.chart j).symm y))))=
      w (e.symm ((B.chart j).symm y))
    rw [(A.chart i).left_inv hy.2.2]
  · intro x hx V hV hxV
    let W := e.source ∩ e ⁻¹' (U ∩ V)
    have hW : IsOpen W := e.isOpen_inter_preimage (hU.inter hV)
    have hxW : e.symm x∈W := by
      refine ⟨e.map_target (hUt hx),?_⟩
      change e (e.symm x)∈U ∩ V
      rw [e.right_inv (hUt hx)]
      exact ⟨hx,hxV⟩
    obtain ⟨y,hy,hfin⟩ := (hw.locallyNondegenerate hO)
      (e.symm x) (hmap hx) W hW hxW
    refine ⟨e y,⟨hy.2.2.1,hy.2.2.2⟩,?_⟩
    change w (e.symm (e y))≠⊥
    rwa [e.left_inv hy.2.1]

end SGPT.PSH.VariableComplexAtlas
