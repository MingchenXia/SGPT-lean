import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.PSH.VariablePullback
import SGPT.PSH.VariableNativeComponent

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual original scalar holomorphy pulls back through any actual
holomorphic map, on every chart's own independently dimensional domain. -/
theorem ChartHolomorphicOn.comp_holomorphic {g : Y → ℂ} {F : X → Y} {U : Set Y}
    (hg : B.ChartHolomorphicOn g U) (hU : IsOpen U) (hF : A.IsHolomorphic B F) :
    A.ChartHolomorphicOn (g ∘ F) (F ⁻¹' U) := by
  intro i z hz
  obtain ⟨j, hj⟩ := B.cover (F ((A.chart i).symm z))
  let W := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (F ⁻¹' (B.chart j).source)
  let H := fun t => B.chart j (F ((A.chart i).symm t))
  have hW : IsOpen W := (A.chart i).symm.isOpen_inter_preimage
    ((B.chart j).open_source.preimage hF.1)
  have hzW : z ∈ W := ⟨hz.1, hj⟩
  let D := (B.chart j).target ∩ (B.chart j).symm ⁻¹' U
  have hD : IsOpen D := (B.chart j).isOpen_inter_preimage_symm hU
  have hzD : H z ∈ D := by
    refine ⟨(B.chart j).map_source hj, ?_⟩
    change (B.chart j).symm (B.chart j (F ((A.chart i).symm z))) ∈ U
    simpa only [mem_preimage, (B.chart j).left_inv hj] using hz.2
  have hG : DifferentiableAt ℂ (g ∘ (B.chart j).symm) (H z) :=
    (hg j).differentiableAt (hD.mem_nhds hzD)
  have hH : DifferentiableAt ℂ H z :=
    (hF.2 i j).differentiableAt (hW.mem_nhds hzW)
  have hc := hG.comp z hH
  have heq : ((g ∘ (B.chart j).symm) ∘ H) =ᶠ[𝓝 z]
      ((g ∘ F) ∘ (A.chart i).symm) := by
    filter_upwards [hW.mem_nhds hzW] with t ht
    change g ((B.chart j).symm (B.chart j (F ((A.chart i).symm t)))) =
      g (F ((A.chart i).symm t))
    exact congrArg g ((B.chart j).left_inv ht.2)
  exact (hc.congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- A given actual local presentation produces ONE connected original
pullback neighborhood with the SAME coefficient, pulled generators, bounded
remainder and numerical bound. No original source nondegeneracy is assumed. -/
theorem pullback_connected_rational_presentation
    {u : Y → EReal} {F : X → Y} (hF : A.IsHolomorphic B F)
    {x : X} {U : Set Y} (hU : IsOpen U) (hx : F x ∈ U)
    {c : ℚ} {N : ℕ} {g : Fin N → Y → ℂ} {b : Y → ℝ} {C : ℝ}
    (hg : ∀ j, B.ChartHolomorphicOn (g j) U)
    (hb : ∀ y ∈ U, |b y| ≤ C)
    (heq : EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog g y + (b y : EReal)) U) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ x ∈ V ∧ V ⊆ F ⁻¹' U ∧
      (∀ j, A.ChartHolomorphicOn (g j ∘ F) V) ∧
      (∀ y ∈ V, |(b ∘ F) y| ≤ C) ∧
      EqOn (u ∘ F) (fun y => ((c : ℝ) : EReal) *
        generatorLog (fun j => g j ∘ F) y + ((b ∘ F) y : EReal)) V := by
  let : LocallyConnectedSpace X := A.locallyConnectedSpace_of_variableAtlas
  obtain ⟨V, ⟨hV, hxV, hconn⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
      ((hU.preimage hF.1).mem_nhds hx)
  refine ⟨V, hV, hconn, hxV, hVU, ?_, ?_, ?_⟩
  · intro j i
    exact ((hg j).comp_holomorphic hU hF i).mono (fun z hz => ⟨hz.1, hVU hz.2⟩)
  · intro y hy
    exact hb (F y) (hVU hy)
  · intro y hy
    exact heq (hVU hy)

/-- The genuine original presentation pulls back at every source point,
retaining all rational, connectedness, boundedness and exact pole fields. -/
theorem HasRationalAnalyticPresentationAt.comp_holomorphic
    {u : Y → EReal} {F : X → Y} {x : X}
    (hu : B.HasRationalAnalyticPresentationAt u (F x)) (hF : A.IsHolomorphic B F) :
    A.HasRationalAnalyticPresentationAt (u ∘ F) x := by
  obtain ⟨c, N, g, b, C, U, hc, hC, hU, _hconn, hx, hg, hb, heq⟩ := hu
  obtain ⟨V, hV, hconn, hxV, _hVU, hgV, hbV, heqV⟩ :=
    pullback_connected_rational_presentation hF hU hx hg hb heq
  exact ⟨c, N, fun j => g j ∘ F, b ∘ F, C, V,
    hc, hC, hV, hconn, hxV, hgV, hbV, heqV⟩

/-- Arbitrary original holomorphic maps preserve the actual intrinsic
rational presentation predicate, independently of QPSH/nondegeneracy. -/
theorem HasRationalAnalyticType.comp_atlasHolomorphic {u : Y → EReal} {F : X → Y}
    (hu : B.HasRationalAnalyticType u) (hF : A.IsHolomorphic B F) :
    A.HasRationalAnalyticType (u ∘ F) :=
  fun x => (hu (F x)).comp_holomorphic hF

end SGPT.PSH.VariableComplexAtlas
