import SGPT.PSH.AtlasComponentBiholomorphism
import SGPT.PSH.SigmaNativeNefGluing

/-! Genuine scalar smooth-potential gluing on the ACTUAL original manifold,
including all varying component dimensions and the actual inverse readback. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
variable (A : VariableComplexAtlas X)

local instance originalSmoothFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c

local instance originalSmoothFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c

/-- Every actual smooth native component family GLUES to ONE globally
original-chart-smooth real function with EXACT value on EVERY original point.
No finite catalog, common bound/dimension or supplied global smoothness. -/
theorem original_exists_smooth_component_gluing
    (h : ∀ c : ConnectedComponents X,actualComponentPoint A c → ℝ)
    (hh : ∀ c,ChartSmooth (n := actualComponentDimension A c) (h c)) :
    ∃ H : X → ℝ,A.ChartSmoothOn H univ ∧
      ∀ c (p : actualComponentPoint A c),H p.val=h c p := by
  let sigmah : ((c : ConnectedComponents X) × actualComponentPoint A c) → ℝ := fun p => h p.1 p.2
  let H : X → ℝ := sigmah ∘ (actualComponentHomeomorph A).symm
  have hs : (actualComponentSigmaAtlas A).ChartSmoothOn sigmah univ :=
    sigma_glued_real_chartSmooth h hh
  refine ⟨H,?_,?_⟩
  · simpa only [preimage_univ] using hs.comp_holomorphic isOpen_univ
      (actualComponentHomeomorph_inverse_isHolomorphic A)
  · intro c p
    change sigmah ((actualComponentHomeomorph A).symm p.val)=h c p
    rw [actualComponentHomeomorph_inverse_of_mem A c p.val p.property]

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
