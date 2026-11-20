import SGPT.PSH.AtlasComponentHomeomorphism

/-! The ACTUAL canonical component homeomorphism is biholomorphic in BOTH
original varying-dimension atlases, with every chart comparison produced. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X]

private theorem coordinate_dimensionTransport_differentiableOn {d e m : ℕ}
    (s : OpenPartialHomeomorph X (ComplexModel d))
    (t : OpenPartialHomeomorph X (ComplexModel e)) (ht : e=m)
    (hcoord : DifferentiableOn ℂ (s.symm.trans t) (s.symm.trans t).source) :
    DifferentiableOn ℂ ((nativeCoordinateDimensionTransport t ht) ∘ s.symm)
      (s.target ∩ s.symm ⁻¹' (nativeCoordinateDimensionTransport t ht).source) := by
  subst m
  exact hcoord

private theorem coordinate_dimensionTransport_source {d m : ℕ}
    (t : OpenPartialHomeomorph X (ComplexModel d)) (ht : d=m) :
    (nativeCoordinateDimensionTransport t ht).source=t.source := by
  subst m
  rfl

variable [T2Space X] [ParacompactSpace X]

/-- The actual component-to-original map is holomorphic by the ALREADY
proved genuine native inclusion, with exactly the SAME coordinate functions. -/
theorem actualComponentHomeomorph_isHolomorphic (A : VariableComplexAtlas X) :
    (actualComponentSigmaAtlas A).IsHolomorphic A (actualComponentHomeomorph A) := by
  let (c : ConnectedComponents X) : ChartedSpace (ComplexModel (actualComponentDimension A c))
      (actualComponentPoint A c) := actualComponentChartedSpace A c
  let (c : ConnectedComponents X) : IsComplexManifold (actualComponentDimension A c)
      (actualComponentPoint A c) := actualComponentComplexManifold A c
  refine ⟨(actualComponentHomeomorph A).continuous,?_⟩
  rintro ⟨c,e⟩ j
  change DifferentiableOn ℂ (A.chart j ∘ (Subtype.val : actualComponentPoint A c → X) ∘ e.val.symm)
    (e.val.target ∩ e.val.symm ⁻¹' ((Subtype.val : actualComponentPoint A c → X) ⁻¹' (A.chart j).source))
  exact (A.nativeComponentInclusion_isHolomorphic (componentAnchor c)).2 e j

/-- The true inverse is holomorphic on EVERY original chart domain. Its
coordinate function equals the actual inherited native chart on that open
domain; the only dimension change is the INTERNALLY PROVED chart equality. -/
theorem actualComponentHomeomorph_inverse_isHolomorphic (A : VariableComplexAtlas X) :
    A.IsHolomorphic (actualComponentSigmaAtlas A) (actualComponentHomeomorph A).symm := by
  let (c : ConnectedComponents X) : ChartedSpace (ComplexModel (actualComponentDimension A c))
      (actualComponentPoint A c) := actualComponentChartedSpace A c
  let (c : ConnectedComponents X) : IsComplexManifold (actualComponentDimension A c)
      (actualComponentPoint A c) := actualComponentComplexManifold A c
  refine ⟨(actualComponentHomeomorph A).symm.continuous,?_⟩
  rintro i ⟨c,e⟩
  obtain ⟨j,hj⟩ := e.property
  change DifferentiableOn ℂ
    ((e.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk) ∘
      (actualComponentHomeomorph A).symm ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' ((actualComponentHomeomorph A).symm ⁻¹'
      (e.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk).source))
  rw [←hj]
  let a := componentAnchor c
  let t := nativeCoordinateDimensionTransport (A.chart j.val) (A.componentChartDimension a j)
  have hraw : DifferentiableOn ℂ (t ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' t.source) :=
    coordinate_dimensionTransport_differentiableOn (A.chart i) (A.chart j.val)
      (A.componentChartDimension a j) (A.holomorphic i j.val)
  apply (hraw.mono ?_).congr ?_
  · intro z hz
    change z∈(A.chart i).target ∧
      (actualComponentHomeomorph A).symm ((A.chart i).symm z)∈
        Sigma.mk c '' (A.componentChart a j).source at hz
    obtain ⟨p,hp,hpeq⟩ := hz.2
    have hval : p.val=(A.chart i).symm z := by
      have h := congrArg (actualComponentHomeomorph A) hpeq
      simpa only [actualComponentHomeomorph_val,Homeomorph.apply_symm_apply] using h
    have hpprime : p.val∈(A.chart j.val).source := by
      simpa only [A.componentChart_source,mem_preimage] using hp
    refine ⟨hz.1,?_⟩
    change (A.chart i).symm z∈t.source
    rw [coordinate_dimensionTransport_source,←hval]
    exact hpprime
  · intro z hz
    change z∈(A.chart i).target ∧
      (actualComponentHomeomorph A).symm ((A.chart i).symm z)∈
        Sigma.mk c '' (A.componentChart a j).source at hz
    obtain ⟨p,_hp,hpeq⟩ := hz.2
    have hval : p.val=(A.chart i).symm z := by
      have h := congrArg (actualComponentHomeomorph A) hpeq
      simpa only [actualComponentHomeomorph_val,Homeomorph.apply_symm_apply] using h
    change ((A.componentChart a j).lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk)
      ((actualComponentHomeomorph A).symm ((A.chart i).symm z))=t ((A.chart i).symm z)
    rw [←hpeq,OpenPartialHomeomorph.lift_openEmbedding_apply]
    change t p.val=t ((A.chart i).symm z)
    rw [hval]

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
