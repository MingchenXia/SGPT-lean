import SGPT.PSH.AtlasNativeComponentMap
import SGPT.PSH.AtlasAnalyticModificationPullback
import SGPT.PSH.ChartNullTransport

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- ORIGINAL modification geometry internally constructs the actual open
partial homeomorphism on the SAME original analytic complements. The
forward function is literally f, with its actual all-chart inverse. -/
theorem IsAtlasAnalyticModification.exists_offExceptional_openPartialHomeomorph
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) :
    ∃ (E : Set X) (S : Set Y), A.HasAnalyticChartEquations E ∧ interior E = ∅ ∧
      B.HasAnalyticChartEquations S ∧ interior S = ∅ ∧
      ∃ e : OpenPartialHomeomorph X Y,
        e.source = Eᶜ ∧ e.target = Sᶜ ∧ (∀ x, e x = f x) ∧
        B.IsHolomorphicOn A e.symm Sᶜ := by
  obtain ⟨_hf, _hp, E, S, s, hE, hEi, hS, hSi, hpre, hs, hright, hleft⟩ := hf
  let e : OpenPartialHomeomorph X Y := {
    toFun := f
    invFun := s
    source := Eᶜ
    target := Sᶜ
    map_source' := by
      intro x hx hfx
      apply hx
      change x ∈ f ⁻¹' S at hfx
      rwa [hpre] at hfx
    map_target' := by
      intro y hy hsy
      have hfs : f (s y) ∈ S := by
        change s y ∈ f ⁻¹' S
        rw [hpre]
        exact hsy
      rw [hright y hy] at hfs
      exact hy hfs
    left_inv' := hleft
    right_inv' := hright
    open_source := (hE.isClosed A).isOpen_compl
    open_target := (hS.isClosed B).isOpen_compl
    continuousOn_toFun := _hf.1.continuousOn
    continuousOn_invFun := hs.1 }
  exact ⟨E, S, hE, hEi, hS, hSi, e, rfl, rfl, (fun _ => rfl), hs⟩

/-- Actual off-exceptional inverse geometry and internally proved overlap
dimension equality match ORIGINAL component dimensions even at exceptional
points. No uniform model or dimension-equality premise is supplied. -/
theorem IsAtlasAnalyticModification.componentDimension_eq
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) (x : X) :
    A.pointDimension x = B.pointDimension (f x) := by
  obtain ⟨E, S, _hE, hEi, _hS, _hSi, e, heS, heT, heval, hs⟩ :=
    hf.exists_offExceptional_openPartialHomeomorph
  have hdense : Dense Eᶜ := interior_eq_empty_iff_dense_compl.mp hEi
  obtain ⟨a, haE, haC⟩ := hdense.exists_mem_open (A.isOpen_component x)
    ⟨x, mem_connectedComponent⟩
  obtain ⟨i, hai⟩ := A.cover a
  obtain ⟨j, haj⟩ := B.cover (f a)
  let ψ := ((A.chart i).symm.trans e).trans (B.chart j)
  have hdom : ψ.source ⊆ (A.chart i).target ∩
      (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source) := by
    intro z hz
    change (z ∈ (A.chart i).target ∧ (A.chart i).symm z ∈ e.source) ∧
      e ((A.chart i).symm z) ∈ (B.chart j).source at hz
    refine ⟨hz.1.1, ?_⟩
    change f ((A.chart i).symm z) ∈ (B.chart j).source
    simpa only [heval] using hz.2
  have hψ : DifferentiableOn ℂ ψ ψ.source := by
    change DifferentiableOn ℂ
      (fun z ↦ (B.chart j) (e ((A.chart i).symm z))) ψ.source
    simpa only [heval, atlasCoordinateMap] using (hf.1.2 i j).mono hdom
  have htarget : ψ.target ⊆ (B.chart j).target ∩
      (B.chart j).symm ⁻¹' (Sᶜ ∩ e.symm ⁻¹' (A.chart i).source) := by
    intro z hz
    change z ∈ (B.chart j).target ∧ (B.chart j).symm z ∈
      (e.target ∩ e.symm ⁻¹' (A.chart i).source) at hz
    exact ⟨hz.1, heT ▸ hz.2⟩
  have hψinv : DifferentiableOn ℂ ψ.symm ψ.target := by
    change DifferentiableOn ℂ
      (fun z ↦ (A.chart i) (e.symm ((B.chart j).symm z))) ψ.target
    exact (hs.2 j i).mono htarget
  have haψ : (A.chart i) a ∈ ψ.source := by
    change ((A.chart i) a ∈ (A.chart i).target ∧
      (A.chart i).symm ((A.chart i) a) ∈ e.source) ∧
      e ((A.chart i).symm ((A.chart i) a)) ∈ (B.chart j).source
    rw [(A.chart i).left_inv hai, heS, heval]
    exact ⟨⟨(A.chart i).map_source hai, haE⟩, haj⟩
  have hij : A.dimension i = B.dimension j :=
    SGPT.PSH.model_dimension_eq_of_holomorphic_openPartial ψ hψ hψinv ⟨_, haψ⟩
  calc
    A.pointDimension x = A.pointDimension a :=
      (A.pointDimension_eq_on_connectedComponent x haC).symm
    _ = A.dimension i := A.pointDimension_eq_chart a i hai
    _ = B.dimension j := hij
    _ = B.pointDimension (f a) := (B.pointDimension_eq_chart (f a) j haj).symm
    _ = B.pointDimension (f x) := B.pointDimension_eq_on_connectedComponent (f x)
      (hf.1.1.mapsTo_connectedComponent x haC)

end SGPT.PSH.VariableComplexAtlas
