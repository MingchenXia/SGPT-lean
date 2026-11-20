import SGPT.PSH.VariableComponentAnalytic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Literal original finite-equation analytic irreducibility, with no native certificate. -/
def HasIrreducibleAnalyticChartEquations (F : Set X) : Prop :=
  A.HasAnalyticChartEquations F ∧ F.Nonempty ∧
    ∀ B C : Set X, A.HasAnalyticChartEquations B → A.HasAnalyticChartEquations C →
      B ⊆ F → C ⊆ F → F = B ∪ C → F = B ∨ F = C

variable {A}

/-- The actual two finite equation families present the literal intersection. -/
theorem HasAnalyticChartEquations.inter {F G : Set X}
    (hF : A.HasAnalyticChartEquations F) (hG : A.HasAnalyticChartEquations G) :
    A.HasAnalyticChartEquations (F ∩ G) := by
  intro i z hz
  obtain ⟨U, hU, hzU, hUt, N, f, hf, hFzero⟩ := hF i z hz
  obtain ⟨V, hV, hzV, hVt, M, g, hg, hGzero⟩ := hG i z hz
  refine ⟨U ∩ V, hU.inter hV, ⟨hzU, hzV⟩, inter_subset_left.trans hUt,
    N + M, Fin.addCases f g, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa using (hf a).mono inter_subset_left
    · simpa using (hg b).mono inter_subset_right
  · intro y hy
    rw [mem_inter_iff, hFzero y hy.1, hGzero y hy.2, Fin.forall_fin_add]
    simp

/-- Actual clopen chart cuts have empty or constant-one finite holomorphic equations. -/
theorem hasAnalyticChartEquations_of_isClopen {F : Set X} (hF : IsClopen F) :
    A.HasAnalyticChartEquations F := by
  classical
  intro i z hz
  by_cases hcenter : (A.chart i).symm z ∈ F
  · refine ⟨(A.chart i).target ∩ (A.chart i).symm ⁻¹' F,
      (A.chart i).isOpen_inter_preimage_symm hF.isOpen, ⟨hz, hcenter⟩,
      inter_subset_left, 0, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_⟩
    intro y hy
    exact ⟨fun _ j => Fin.elim0 j, fun _ => hy.2⟩
  · refine ⟨(A.chart i).target ∩ (A.chart i).symm ⁻¹' Fᶜ,
      (A.chart i).isOpen_inter_preimage_symm hF.isClosed.isOpen_compl,
      ⟨hz, hcenter⟩, inter_subset_left, 1, (fun _ _ => (1 : ℂ)),
      (fun _ => differentiableOn_const _), ?_⟩
    intro y hy
    constructor
    · intro hmem
      exact (hy.2 hmem).elim
    · intro hzero
      exact (one_ne_zero (hzero 0)).elim

/-- Original analytic irreducibility forces the entire carrier into its actual component. -/
theorem HasIrreducibleAnalyticChartEquations.subset_connectedComponent {F : Set X}
    (hF : A.HasIrreducibleAnalyticChartEquations F) {x : X} (hx : x ∈ F) :
    F ⊆ connectedComponent x := by
  let C := connectedComponent x
  have hC : IsClopen C := ⟨isClosed_connectedComponent, (A.componentOpen x).isOpen⟩
  have hFC := hF.1.inter (hasAnalyticChartEquations_of_isClopen (A := A) hC)
  have hFCc := hF.1.inter (hasAnalyticChartEquations_of_isClopen (A := A) hC.compl)
  have hsplit : F = (F ∩ C) ∪ (F ∩ Cᶜ) := by
    ext y
    simp only [mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  rcases hF.2.2 (F ∩ C) (F ∩ Cᶜ) hFC hFCc inter_subset_left inter_subset_left hsplit with
    hleft | hright
  · intro y hy
    exact ((hleft ▸ hy : y ∈ F ∩ C)).2
  · have hxc : x ∈ C := mem_connectedComponent
    exact False.elim (((hright ▸ hx : x ∈ F ∩ Cᶜ)).2 hxc)

end SGPT.PSH.VariableComplexAtlas
