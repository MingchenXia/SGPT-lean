import SGPT.PSH.VariableNativeComponent
import SGPT.PSH.AtlasHolomorphicCoordinates

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- The ORIGINAL map on the SAME original connected component subtypes.
Actual continuity internally proves the target component qualification. -/
def IsHolomorphic.componentMap {f : X → Y} (hf : A.IsHolomorphic B f) (x : X) :
    A.componentOpen x → B.componentOpen (f x) :=
  fun p => ⟨f p, hf.1.mapsTo_connectedComponent x p.property⟩

private def mapTransportChart {Z : Type*} [TopologicalSpace Z] {d n : ℕ}
    (e : OpenPartialHomeomorph Z (ComplexModel d)) (h : d = n) :
    OpenPartialHomeomorph Z (ComplexModel n) := h ▸ e

private theorem restricted_coordinate_contDiffOn {d e n m : ℕ}
    (s : OpenPartialHomeomorph X (ComplexModel d))
    (t : OpenPartialHomeomorph Y (ComplexModel e)) (hs : d = n) (ht : e = m)
    (U : Opens X) (V : Opens Y) (hU : Nonempty U) (hV : Nonempty V)
    (f : X → Y) (F : U → V) (hF : ∀ p, (F p : Y) = f p)
    (hcoord : ContDiffOn ℂ ∞ (t ∘ f ∘ s.symm)
      (s.target ∩ s.symm ⁻¹' (f ⁻¹' t.source))) :
    ContDiffOn ℂ ∞
      (((mapTransportChart t ht).subtypeRestr hV) ∘ F ∘
        ((mapTransportChart s hs).subtypeRestr hU).symm)
      (((mapTransportChart s hs).subtypeRestr hU).target ∩
        ((mapTransportChart s hs).subtypeRestr hU).symm ⁻¹'
          (F ⁻¹' ((mapTransportChart t ht).subtypeRestr hV).source)) := by
  subst n
  subst m
  change ContDiffOn ℂ ∞ ((t.subtypeRestr hV) ∘ F ∘ (s.subtypeRestr hU).symm)
    ((s.subtypeRestr hU).target ∩ (s.subtypeRestr hU).symm ⁻¹'
      (F ⁻¹' (t.subtypeRestr hV).source))
  have hsub : (s.subtypeRestr hU).target ∩ (s.subtypeRestr hU).symm ⁻¹'
      (F ⁻¹' (t.subtypeRestr hV).source) ⊆ s.target ∩ s.symm ⁻¹' (f ⁻¹' t.source) := by
    intro z hz
    refine ⟨s.subtypeRestr_target_subset hU hz.1, ?_⟩
    have hval := s.subtypeRestr_symm_apply hU hz.1
    change ((s.subtypeRestr hU).symm z).val = s.symm z at hval
    have hzT := hz.2
    simp only [mem_preimage, OpenPartialHomeomorph.subtypeRestr_source] at hzT
    rw [hF, hval] at hzT
    exact hzT
  apply (hcoord.mono hsub).congr
  intro z hz
  have hval := s.subtypeRestr_symm_apply hU hz.1
  change ((s.subtypeRestr hU).symm z).val = s.symm z at hval
  change t (F ((s.subtypeRestr hU).symm z)).val = t (f (s.symm z))
  rw [hF, hval]

/-- Original all-chart holomorphy internally gives genuine native smoothness
on the SAME original components. The two actual native dimensions are
independent, and no native map/structure certificate is supplied. -/
theorem IsHolomorphic.componentMap_contMDiff {f : X → Y} (hf : A.IsHolomorphic B f) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    letI := B.componentChartedSpace (f x)
    letI := B.componentIsManifold (f x)
    ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension x))
      𝓘(ℂ, ComplexModel (B.pointDimension (f x))) ∞ (hf.componentMap x) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  let := B.componentChartedSpace (f x)
  let := B.componentIsManifold (f x)
  apply contMDiff_iff.mpr
  refine ⟨(hf.1.comp continuous_subtype_val).subtype_mk _, ?_⟩
  intro p q
  let i := Classical.choose (A.componentChart_cover x p)
  let j := Classical.choose (B.componentChart_cover (f x) q)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
    Set.inter_univ, Function.comp_id, Function.id_comp]
  change ContDiffOn ℂ ∞
    ((B.componentChart (f x) j) ∘ hf.componentMap x ∘ (A.componentChart x i).symm)
    ((A.componentChart x i).target ∩ (A.componentChart x i).symm ⁻¹'
      ((hf.componentMap x) ⁻¹' (B.componentChart (f x) j).source))
  exact restricted_coordinate_contDiffOn (A.chart i.val) (B.chart j.val)
    (A.componentChartDimension x i) (B.componentChartDimension (f x) j)
    (A.componentOpen x) (B.componentOpen (f x)) (A.componentNonempty x) (B.componentNonempty (f x))
    f (hf.componentMap x) (fun _ => rfl) (atlasCoordinateMap_contDiffOn hf i.val j.val)

end SGPT.PSH.VariableComplexAtlas
