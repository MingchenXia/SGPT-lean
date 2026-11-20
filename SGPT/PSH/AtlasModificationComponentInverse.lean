import SGPT.PSH.AtlasModificationComponentDimension
import SGPT.PSH.VariableComponentAnalytic
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- ORIGINAL proper analytic sets do not disconnect the SAME actual component.
The existing native geometry applies to internally derived component structures. -/
theorem HasAnalyticChartEquations.isPreconnected_component_compl
    [T2Space Y] [ParacompactSpace Y] {S : Set Y}
    (hS : B.HasAnalyticChartEquations S) (hSi : interior S = ∅) (y : Y) :
    IsPreconnected ((Subtype.val ⁻¹' S : Set (B.componentOpen y))ᶜ) := by
  let := B.componentChartedSpace y
  let := B.componentComplexManifold_of_paracompact y
  let : ConnectedSpace (B.componentOpen y) :=
    Subtype.connectedSpace (isConnected_connectedComponent (x := y))
  have hT := hS.componentAnalytic y
  have hTne : (Subtype.val ⁻¹' S : Set (B.componentOpen y)) ≠ univ := by
    intro heq
    have hdense : Dense Sᶜ := interior_eq_empty_iff_dense_compl.mp hSi
    obtain ⟨b, hbS, hbC⟩ := hdense.exists_mem_open (B.isOpen_component y)
      ⟨y, mem_connectedComponent⟩
    have hb : (⟨b, hbC⟩ : B.componentOpen y) ∈ (Subtype.val ⁻¹' S : Set _) := by
      rw [heq]
      trivial
    exact hbS hb
  exact SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected.isPreconnected_compl hT hTne

/-- The ORIGINAL modification internally supplies an inverse preserving the
ENTIRE actual target component complement, not just one chosen inverse open. -/
theorem IsAtlasAnalyticModification.exists_offExceptional_inverse_component
    [T2Space Y] [ParacompactSpace Y]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) (x : X) :
    ∃ (E : Set X) (S : Set Y), A.HasAnalyticChartEquations E ∧ interior E = ∅ ∧
      B.HasAnalyticChartEquations S ∧ interior S = ∅ ∧
      ∃ e : OpenPartialHomeomorph X Y,
        e.source = Eᶜ ∧ e.target = Sᶜ ∧ (∀ z, e z = f z) ∧
        B.IsHolomorphicOn A e.symm Sᶜ ∧
        MapsTo e.symm (connectedComponent (f x) ∩ Sᶜ) (connectedComponent x) := by
  obtain ⟨E, S, hE, hEi, hS, hSi, e, heS, heT, heval, hs⟩ :=
    hf.exists_offExceptional_openPartialHomeomorph
  refine ⟨E, S, hE, hEi, hS, hSi, e, heS, heT, heval, hs, ?_⟩
  have hdense : Dense Eᶜ := interior_eq_empty_iff_dense_compl.mp hEi
  obtain ⟨a, haE, haC⟩ := hdense.exists_mem_open (A.isOpen_component x)
    ⟨x, mem_connectedComponent⟩
  have hasource : a ∈ e.source := heS.symm ▸ haE
  have haS : f a ∈ Sᶜ := by
    have h := e.map_source hasource
    rwa [heval, heT] at h
  let D := B.componentOpen (f x)
  let T : Set D := (Subtype.val ⁻¹' S)ᶜ
  let G : D → X := fun p => e.symm p.val
  have hcont : ContinuousOn G T := hs.1.comp continuous_subtype_val.continuousOn
    (fun _ hp => hp)
  have hpre : IsPreconnected (G '' T) :=
    (hS.isPreconnected_component_compl hSi (f x)).image G hcont
  have haimage : a ∈ G '' T := by
    refine ⟨⟨f a, hf.1.1.mapsTo_connectedComponent x haC⟩, haS, ?_⟩
    change e.symm (f a) = a
    rw [← heval a]
    exact e.left_inv hasource
  have hsub := hpre.subset_connectedComponent haimage
  intro y hy
  have hmem : e.symm y ∈ G '' T := ⟨⟨y, hy.1⟩, hy.2, rfl⟩
  have hcomp := hsub hmem
  rwa [← connectedComponent_eq haC] at hcomp

end SGPT.PSH.VariableComplexAtlas
