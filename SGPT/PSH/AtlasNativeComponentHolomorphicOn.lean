import SGPT.PSH.AtlasModificationComponentInverse

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

private def onTransportChart {Z : Type*} [TopologicalSpace Z] {d n : ℕ}
    (e : OpenPartialHomeomorph Z (ComplexModel d)) (h : d = n) :
    OpenPartialHomeomorph Z (ComplexModel n) := h ▸ e

private theorem open_restricted_coordinate_contDiffOn {d e n m : ℕ}
    (s : OpenPartialHomeomorph X (ComplexModel d))
    (t : OpenPartialHomeomorph Y (ComplexModel e)) (hs : d = n) (ht : e = m)
    (U : Opens X) (V : Opens Y) (hU : Nonempty U) (hV : Nonempty V)
    (Q : Set X) (f : X → Y) (F : U → V)
    (hF : ∀ p, p.val ∈ Q → (F p : Y) = f p)
    (hcoord : ContDiffOn ℂ ∞ (t ∘ f ∘ s.symm)
      (s.target ∩ s.symm ⁻¹' (Q ∩ f ⁻¹' t.source))) :
    ContDiffOn ℂ ∞
      (((onTransportChart t ht).subtypeRestr hV) ∘ F ∘
        ((onTransportChart s hs).subtypeRestr hU).symm)
      (((onTransportChart s hs).subtypeRestr hU).target ∩
        ((onTransportChart s hs).subtypeRestr hU).symm ⁻¹'
          ((Subtype.val ⁻¹' Q) ∩
            F ⁻¹' ((onTransportChart t ht).subtypeRestr hV).source)) := by
  subst n
  subst m
  change ContDiffOn ℂ ∞ ((t.subtypeRestr hV) ∘ F ∘ (s.subtypeRestr hU).symm)
    ((s.subtypeRestr hU).target ∩ (s.subtypeRestr hU).symm ⁻¹'
      ((Subtype.val ⁻¹' Q) ∩ F ⁻¹' (t.subtypeRestr hV).source))
  have hsub : (s.subtypeRestr hU).target ∩ (s.subtypeRestr hU).symm ⁻¹'
      ((Subtype.val ⁻¹' Q) ∩ F ⁻¹' (t.subtypeRestr hV).source) ⊆
      s.target ∩ s.symm ⁻¹' (Q ∩ f ⁻¹' t.source) := by
    intro z hz
    have hval := s.subtypeRestr_symm_apply hU hz.1
    change ((s.subtypeRestr hU).symm z).val = s.symm z at hval
    refine ⟨s.subtypeRestr_target_subset hU hz.1, ?_, ?_⟩
    · rw [← hval]
      exact hz.2.1
    · have hzT := hz.2.2
      simp only [mem_preimage, OpenPartialHomeomorph.subtypeRestr_source] at hzT
      rw [hF _ hz.2.1, hval] at hzT
      exact hzT
  apply (hcoord.mono hsub).congr
  intro z hz
  have hval := s.subtypeRestr_symm_apply hU hz.1
  change ((s.subtypeRestr hU).symm z).val = s.symm z at hval
  change t (F ((s.subtypeRestr hU).symm z)).val = t (f (s.symm z))
  rw [hF _ hz.2.1, hval]

/-- An honest generic commuting-function dictionary on ORIGINAL open Q.
The function between SAME actual component subtypes need agree with the
original map only on Q; both native dimensions are internally derived. -/
theorem IsHolomorphicOn.component_restriction_contMDiffOn
    {f : X → Y} {Q : Set X} (hf : A.IsHolomorphicOn B f Q) (hQ : IsOpen Q)
    (x : X) (y : Y) (F : A.componentOpen x → B.componentOpen y)
    (hF : ∀ p, p.val ∈ Q → (F p : Y) = f p) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    letI := B.componentChartedSpace y
    letI := B.componentIsManifold y
    ContMDiffOn 𝓘(ℂ, ComplexModel (A.pointDimension x))
      𝓘(ℂ, ComplexModel (B.pointDimension y)) ∞ F (Subtype.val ⁻¹' Q) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  let := B.componentChartedSpace y
  let := B.componentIsManifold y
  have hcont : ContinuousOn (fun p : A.componentOpen x => (F p).val)
      (Subtype.val ⁻¹' Q) :=
    (hf.1.comp continuous_subtype_val.continuousOn (fun _ hp => hp)).congr hF
  apply contMDiffOn_iff.mpr
  refine ⟨(Topology.IsInducing.continuousOn_iff Topology.IsInducing.subtypeVal).mpr hcont, ?_⟩
  intro p q
  let i := Classical.choose (A.componentChart_cover x p)
  let j := Classical.choose (B.componentChart_cover y q)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
    Set.inter_univ, Function.comp_id, Function.id_comp]
  change ContDiffOn ℂ ∞
    ((B.componentChart y j) ∘ F ∘ (A.componentChart x i).symm)
    ((A.componentChart x i).target ∩ (A.componentChart x i).symm ⁻¹'
      ((Subtype.val ⁻¹' Q) ∩ F ⁻¹' (B.componentChart y j).source))
  apply open_restricted_coordinate_contDiffOn (A.chart i.val) (B.chart j.val)
    (A.componentChartDimension x i) (B.componentChartDimension y j)
    (A.componentOpen x) (B.componentOpen y) (A.componentNonempty x) (B.componentNonempty y)
    Q f F hF
  exact contDiffOn_of_differentiableOn_complex (hf.2 i.val j.val)
    ((A.chart i.val).symm.isOpen_inter_preimage
      (hf.1.isOpen_inter_preimage hQ (B.chart j.val).open_source))

/-- ORIGINAL modification data internally construct the actual native inverse,
its smoothness on the ENTIRE complement, and both SAME component identities.
The generic commuting-function hypothesis above is discharged internally. -/
theorem IsAtlasAnalyticModification.exists_native_component_inverse
    [T2Space Y] [ParacompactSpace Y]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    letI := B.componentChartedSpace (f x)
    letI := B.componentIsManifold (f x)
    ∃ (E : Set X) (S : Set Y), A.HasAnalyticChartEquations E ∧ interior E = ∅ ∧
      B.HasAnalyticChartEquations S ∧ interior S = ∅ ∧
      ∃ e : OpenPartialHomeomorph X Y,
        e.source = Eᶜ ∧ e.target = Sᶜ ∧ (∀ z, e z = f z) ∧
        B.IsHolomorphicOn A e.symm Sᶜ ∧
        MapsTo e.symm (connectedComponent (f x) ∩ Sᶜ) (connectedComponent x) ∧
        ∃ g : B.componentOpen (f x) → A.componentOpen x,
          ContMDiffOn 𝓘(ℂ, ComplexModel (B.pointDimension (f x)))
            𝓘(ℂ, ComplexModel (A.pointDimension x)) ∞ g (Subtype.val ⁻¹' Sᶜ) ∧
          (∀ p, p.val ∉ S → (g p).val = e.symm p.val) ∧
          (∀ p, p.val ∉ S → hf.1.componentMap x (g p) = p) ∧
          ∀ p, p.val ∉ E → g (hf.1.componentMap x p) = p := by
  classical
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  let := B.componentChartedSpace (f x)
  let := B.componentIsManifold (f x)
  obtain ⟨E, S, hE, hEi, hS, hSi, e, heS, heT, heval, hs, hmap⟩ :=
    hf.exists_offExceptional_inverse_component x
  let g : B.componentOpen (f x) → A.componentOpen x := fun p =>
    if hp : p.val ∉ S then ⟨e.symm p.val, hmap ⟨p.property, hp⟩⟩
    else ⟨x, mem_connectedComponent⟩
  have hgval (p : B.componentOpen (f x)) (hp : p.val ∉ S) :
      (g p).val = e.symm p.val := by
    dsimp only [g]
    rw [dif_pos hp]
  refine ⟨E, S, hE, hEi, hS, hSi, e, heS, heT, heval, hs, hmap, g,
    hs.component_restriction_contMDiffOn (hS.isClosed B).isOpen_compl
      (f x) x g hgval, hgval, ?_, ?_⟩
  · intro p hp
    apply Subtype.ext
    change f (g p).val = p.val
    rw [hgval p hp]
    calc
      f (e.symm p.val) = e (e.symm p.val) := (heval _).symm
      _ = p.val := e.right_inv (heT.symm ▸ hp)
  · intro p hp
    have hsource : p.val ∈ e.source := heS.symm ▸ hp
    have hfp : (hf.1.componentMap x p).val ∉ S := by
      have h := e.map_source hsource
      rwa [heval, heT] at h
    apply Subtype.ext
    rw [hgval _ hfp]
    change e.symm (f p.val) = p.val
    rw [← heval p.val]
    exact e.left_inv hsource

end SGPT.PSH.VariableComplexAtlas
