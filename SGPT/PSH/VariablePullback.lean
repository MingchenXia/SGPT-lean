import SGPT.PSH.VariableAtlas

/-!
# The source holomorphic pullback dichotomy on actual complex atlases

Coordinate differentiability concerns the actual coordinate map on its actual
open domain. The analytic conclusion is derived from singular germ pullback
and the already checked component-to-local nondegeneracy producer.
-/

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)

/-- An actual continuous map with holomorphic actual chart representatives.
The continuity condition is geometric, independent of any PSH conclusion. -/
def IsHolomorphic (f : X → Y) : Prop :=
  Continuous f ∧ ∀ i : A.Index, ∀ j : B.Index,
    DifferentiableOn ℂ (fun z ↦ B.chart j (f ((A.chart i).symm z)))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source))

variable {A B}

/-- A genuine local connected source witness gives a non-bottom point in
the actual original connected component, even for arbitrary component count. -/
theorem IsPSH.exists_component_ne_bot {w : X → EReal} (hw : A.IsPSH w) (x : X) :
    ∃ y ∈ connectedComponent x, w y ≠ ⊥ := by
  obtain ⟨i, hi, V, hV, hc, hVe, hxV, hwV⟩ := hw x
  obtain ⟨z, hz, hn⟩ := hwV.nontrivial
  have hcimage : IsConnected ((A.chart i).symm '' V) :=
    hc.image _ ((A.chart i).continuousOn_symm.mono hVe)
  have hximage : x ∈ (A.chart i).symm '' V := by
    exact ⟨A.chart i x, hxV, (A.chart i).left_inv hi⟩
  exact ⟨(A.chart i).symm z,
    hcimage.subset_connectedComponent hximage ⟨z, hz, rfl⟩, hn⟩

/-- The singular germ producer gives every actual source coordinate germ
of the pullback. Source and target chart dimensions are independently concrete. -/
theorem IsPSH.chart_comp_holomorphic {w : Y → EReal} {f : X → Y}
    (hw : B.IsPSH w) (hf : A.IsHolomorphic B f) (i : A.Index) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn (A.coordinate (w ∘ f) i)
      (A.chart i).target := by
  intro z hz
  obtain ⟨j, hj⟩ := B.cover (f ((A.chart i).symm z))
  let U := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source)
  have hU : IsOpen U :=
    (A.chart i).symm.isOpen_inter_preimage ((B.chart j).open_source.preimage hf.1)
  have hzU : z ∈ U := ⟨hz, hj⟩
  have hp := SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicAt_comp_holomorphic
    hU (hf.2 i j) hzU (hw.chartPlurisubharmonic j _ ((B.chart j).map_source hj))
  apply hp.congr
  filter_upwards [hU.mem_nhds hzU] with y hy
  change w ((B.chart j).symm (B.chart j (f ((A.chart i).symm y)))) =
    w (f ((A.chart i).symm y))
  exact congrArg w ((B.chart j).left_inv hy.2)

/-- The exact component qualification is both necessary and sufficient.
No local nondegeneracy or integrability certificate is assumed. -/
theorem IsPSH.comp_holomorphic_iff_component_nonbot {w : Y → EReal} {f : X → Y}
    (hw : B.IsPSH w) (hf : A.IsHolomorphic B f) :
    A.IsPSH (w ∘ f) ↔ ∀ x : X, ∃ y ∈ connectedComponent x, w (f y) ≠ ⊥ := by
  constructor
  · intro hp x
    exact hp.exists_component_ne_bot x
  · intro hn
    have hcharts := hw.chart_comp_holomorphic hf
    apply psh_iff_chart_and_nondegenerate.mpr
    refine ⟨hcharts, locallyNondegenerate_of_component_nonbot_of_local_coordinate_psh ?_ hn⟩
    intro x
    obtain ⟨i, hi⟩ := A.cover x
    exact ⟨A.dimension i, A.chart i, hi, hcharts i⟩

/-- SGPT `prop:pullbackpsh`: the actual global source alternatives. -/
theorem psh_comp_holomorphic_or_component_bot {w : Y → EReal} {f : X → Y}
    (hw : B.IsPSH w) (hf : A.IsHolomorphic B f) :
    A.IsPSH (w ∘ f) ∨ ∃ x : X, ∀ y ∈ connectedComponent x, w (f y) = ⊥ := by
  classical
  by_cases hn : ∀ x : X, ∃ y ∈ connectedComponent x, w (f y) ≠ ⊥
  · exact Or.inl ((hw.comp_holomorphic_iff_component_nonbot hf).mpr hn)
  · right
    push Not at hn
    exact hn

/-- The two source alternatives are disjoint, including on empty manifolds. -/
theorem not_psh_and_component_bot {w : X → EReal} :
    ¬ (A.IsPSH w ∧ ∃ x : X, ∀ y ∈ connectedComponent x, w y = ⊥) := by
  rintro ⟨hw, x, hx⟩
  obtain ⟨y, hy, hn⟩ := hw.exists_component_ne_bot x
  exact hn (hx y hy)

end SGPT.PSH.VariableComplexAtlas
