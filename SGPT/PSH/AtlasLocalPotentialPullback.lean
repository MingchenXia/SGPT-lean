import SGPT.PSH.AtlasHolomorphicTensorPullback

/-! # Pullback of actual smooth functions and original local potentials -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Smoothness is proved in every actual source chart using a valid target
chart on a neighborhood, with no shared dimension or background premise. -/
theorem ChartSmoothOn.comp_holomorphic {g : Y → ℝ} {U : Set Y}
    (hU : IsOpen U) (hg : B.ChartSmoothOn g U) {f : X → Y}
    (hf : A.IsHolomorphic B f) : A.ChartSmoothOn (g ∘ f) (f ⁻¹' U) := by
  intro i z hz
  obtain ⟨j, hj⟩ := B.cover (f ((A.chart i).symm z))
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' ((B.chart j).source ∩ U))
  let V := (B.chart j).target ∩ (B.chart j).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm
    (((B.chart j).open_source.inter hU).preimage hf.1)
  have hzD : z ∈ D := ⟨hz.1, hj, hz.2⟩
  have hF : ContDiffOn ℂ ∞ (atlasCoordinateMap A B f i j) D :=
    (atlasCoordinateMap_contDiffOn hf i j).mono (fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hFV : MapsTo (atlasCoordinateMap A B f i j) D V := by
    intro y hy
    refine ⟨(B.chart j).map_source hy.2.1, ?_⟩
    change (B.chart j).symm ((B.chart j) (f ((A.chart i).symm y))) ∈ U
    rw [(B.chart j).left_inv hy.2.1]
    exact hy.2.2
  have hc := (hg j).comp (hF.restrict_scalars ℝ) hFV
  have heq : (g ∘ (B.chart j).symm) ∘ atlasCoordinateMap A B f i j =ᶠ[𝓝 z]
      (g ∘ f) ∘ (A.chart i).symm := by
    filter_upwards [hD.mem_nhds hzD] with y hy
    change g ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y)))) =
      g (f ((A.chart i).symm y))
    rw [(B.chart j).left_inv hy.2.1]
  exact ((hc.contDiffAt (hD.mem_nhds hzD)).congr_of_eventuallyEq heq.symm).contDiffWithinAt

/-- The actual local potential pulls back as the original scalar function,
and the whole two-form equality holds in every original source chart. -/
theorem IsAtlasLocalPotential.comp_holomorphic {θ : AtlasClosedRealOneOneForm B}
    {U : Set Y} {g : Y → ℝ} (hg : B.IsAtlasLocalPotential θ U g)
    {f : X → Y} (hf : A.IsHolomorphic B f) :
    A.IsAtlasLocalPotential (θ.holomorphicPullback hf) (f ⁻¹' U) (g ∘ f) := by
  refine ⟨hg.1.preimage hf.1, hg.2.1.comp_holomorphic hg.1 hf, ?_⟩
  intro i z hz
  obtain ⟨j, hj⟩ := B.cover (f ((A.chart i).symm z))
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' ((B.chart j).source ∩ U))
  let V := (B.chart j).target ∩ (B.chart j).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm
    (((B.chart j).open_source.inter hg.1).preimage hf.1)
  have hV : IsOpen V := (B.chart j).isOpen_inter_preimage_symm hg.1
  have hzD : z ∈ D := ⟨hz.1, hj, hz.2⟩
  have hzj : z ∈ atlasCoordinateDomain A B f i j := ⟨hz.1, hj⟩
  have hF : ContDiffOn ℂ ∞ (atlasCoordinateMap A B f i j) D :=
    (atlasCoordinateMap_contDiffOn hf i j).mono (fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hFV : MapsTo (atlasCoordinateMap A B f i j) D V := by
    intro y hy
    refine ⟨(B.chart j).map_source hy.2.1, ?_⟩
    change (B.chart j).symm ((B.chart j) (f ((A.chart i).symm y))) ∈ U
    rw [(B.chart j).left_inv hy.2.1]
    exact hy.2.2
  have heq : (g ∘ f) ∘ (A.chart i).symm =ᶠ[𝓝 z]
      (fun y => (g ∘ (B.chart j).symm) (atlasCoordinateMap A B f i j y)) := by
    filter_upwards [hD.mem_nhds hzD] with y hy
    change g (f ((A.chart i).symm y)) =
      g ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y))))
    rw [(B.chart j).left_inv hy.2.1]
  rw [smoothDDC_congr heq,
    HolomorphicDDC.smoothDDC_comp hD hV hF (hg.2.1 j) hFV hzD,
    hg.2.2 j (hFV hzD), θ.holomorphicPullback_coeff hf i j hzj]

end SGPT.PSH.VariableComplexAtlas
