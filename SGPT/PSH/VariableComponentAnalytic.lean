import SGPT.PSH.VariableComponentCountability
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

private def analyticTransportChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem analyticEquations_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (Z : Set X)
    (hEq : ∀ z ∈ e.target,
      ∃ W : Set (ComplexModel d), IsOpen W ∧ z ∈ W ∧ W ⊆ e.target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel d → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, e.symm y ∈ Z ↔ ∀ j, g j y = 0) :
    ∀ z ∈ ((analyticTransportChart e hd).subtypeRestr hU).target,
      ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧
        W ⊆ ((analyticTransportChart e hd).subtypeRestr hU).target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, (((analyticTransportChart e hd).subtypeRestr hU).symm y).val ∈ Z ↔
              ∀ j, g j y = 0 := by
  subst n
  intro z hz
  change z ∈ (e.subtypeRestr hU).target at hz
  obtain ⟨W, hW, hzW, _hWt, N, g, hg, hzero⟩ :=
    hEq z (e.subtypeRestr_target_subset hU hz)
  refine ⟨W ∩ (e.subtypeRestr hU).target,
    hW.inter (e.subtypeRestr hU).open_target, ⟨hzW, hz⟩,
    inter_subset_right, N, g, fun j ↦ (hg j).mono inter_subset_left, ?_⟩
  intro y hy
  have heq := e.subtypeRestr_symm_apply hU hy.2
  change ((e.subtypeRestr hU).symm y).val = e.symm y at heq
  change ((e.subtypeRestr hU).symm y).val ∈ Z ↔ ∀ j, g j y = 0
  rw [heq]
  exact hzero y hy.1

variable {A}

/-- Original finite holomorphic equations on the entire actual restricted target. -/
theorem HasAnalyticChartEquations.componentChartEquations {Z : Set X}
    (hZ : A.HasAnalyticChartEquations Z) (x : X) (i : A.ComponentChartIndex x) :
    ∀ z ∈ (A.componentChart x i).target,
      ∃ W : Set (ComplexModel (A.pointDimension x)), IsOpen W ∧ z ∈ W ∧
        W ⊆ (A.componentChart x i).target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel (A.pointDimension x) → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, ((A.componentChart x i).symm y).val ∈ Z ↔ ∀ j, g j y = 0 := by
  exact analyticEquations_subtypeRestr_cast (A.chart i.val) (A.componentChartDimension x i)
    (A.componentOpen x) (A.componentNonempty x) Z (hZ i.val)

/-- The literal original carrier is native analytic on the same component subtype. -/
theorem HasAnalyticChartEquations.componentAnalytic [T2Space X] [ParacompactSpace X]
    {Z : Set X} (hZ : A.HasAnalyticChartEquations Z) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    IsComplexAnalyticSubset (n := A.pointDimension x)
      (Subtype.val ⁻¹' Z : Set (A.componentOpen x)) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro p
  let i := Classical.choose (A.componentChart_cover x p)
  have hp : p ∈ (A.componentChart x i).source :=
    Classical.choose_spec (A.componentChart_cover x p)
  have he : (complexChartAt (n := A.pointDimension x) p).val = A.componentChart x i := rfl
  obtain ⟨W, hW, hzW, hWt, N, g, hg, hzero⟩ :=
    hZ.componentChartEquations x i _ ((A.componentChart x i).map_source hp)
  refine ⟨{
    generatorCount := N
    generator := g
    coordinateNeighborhood := W
    isOpen_coordinateNeighborhood := hW
    center_mem_coordinateNeighborhood := by rw [he]; exact hzW
    coordinateNeighborhood_subset_target := by rw [he]; exact hWt
    generator_holomorphic := hg
    zeroLocus := ?_ }⟩
  intro q hq hqW
  rw [he] at hq hqW ⊢
  have hz := hzero ((A.componentChart x i) q) hqW
  simpa only [mem_preimage, (A.componentChart x i).left_inv hq] using hz

end SGPT.PSH.VariableComplexAtlas
