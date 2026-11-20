import SGPT.PSH.VariableNativeComponent
import SGPT.PSH.Components

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- The actual restricted original chart, paired with its specified native atlas membership. -/
def componentComplexChart (x : X) (i : A.ComponentChartIndex x) :
    letI := A.componentChartedSpace x
    ComplexChart (A.pointDimension x) (A.componentOpen x) := by
  letI := A.componentChartedSpace x
  exact ⟨A.componentChart x i, ⟨i, rfl⟩⟩

theorem componentComplexChart_val (x : X) (i : A.ComponentChartIndex x) :
    letI := A.componentChartedSpace x
    (A.componentComplexChart x i).val = A.componentChart x i := rfl

/-- The internally produced complex smooth structure supplies maximal-atlas membership. -/
theorem componentChart_mem_maximalAtlas (x : X) (i : A.ComponentChartIndex x) :
    letI := A.componentChartedSpace x
    A.componentChart x i ∈
      (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel (A.pointDimension x)))).maximalAtlas
        (A.componentOpen x) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  exact (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel (A.pointDimension x)))).subset_maximalAtlas
    ⟨i, rfl⟩

private def transportChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem pshWitness_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (u : X → EReal) (p : U)
    (V : Set (ComplexModel d)) (hV : IsOpen V) (hc : IsConnected V)
    (hVe : V ⊆ e.target ∩ e.symm ⁻¹' U) (hpV : e p.val ∈ V)
    (hu : PSHOn (u ∘ e.symm) V) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ IsConnected W ∧
      W ⊆ ((transportChart e hd).subtypeRestr hU).target ∧
      ((transportChart e hd).subtypeRestr hU) p ∈ W ∧
      PSHOn ((u ∘ Subtype.val) ∘ ((transportChart e hd).subtypeRestr hU).symm) W := by
  subst n
  refine ⟨V, hV, hc, ?_, hpV, ?_⟩
  · simpa only [transportChart, OpenPartialHomeomorph.subtypeRestr_def,
      OpenPartialHomeomorph.trans_target, Opens.openPartialHomeomorphSubtypeCoe_target]
      using hVe
  · have heq : EqOn (u ∘ e.symm) ((u ∘ Subtype.val) ∘ (e.subtypeRestr hU).symm) V := by
      intro z hz
      have hzT : z ∈ (e.subtypeRestr hU).target := by
        simpa only [OpenPartialHomeomorph.subtypeRestr_def,
          OpenPartialHomeomorph.trans_target, Opens.openPartialHomeomorphSubtypeCoe_target]
          using hVe hz
      exact congrArg u (e.subtypeRestr_symm_apply hU hzT).symm
    obtain ⟨z, hz, hn⟩ := hu.nontrivial
    exact ⟨hu.disc.congr heq, z, hz, by
      change ((u ∘ Subtype.val) ∘ (e.subtypeRestr hU).symm) z ≠ ⊥
      rwa [← heq hz]⟩

variable {A}

/-- Original source PSH restricts to the same actual component with its native atlas. -/
theorem IsPSH.componentManifoldPSH {u : X → EReal} (hu : A.IsPSH u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    ManifoldPSH (n := A.pointDimension x) (fun p : A.componentOpen x ↦ u p.val) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  have hlocal : A.IsPSHOn u (A.componentOpen x) :=
    (isPSHOn_univ_iff.mpr hu).mono_open isOpen_univ (A.componentOpen x).isOpen
      (subset_univ _)
  intro p
  obtain ⟨i, hi, V, hV, hc, hVe, hpV, hpsh⟩ := hlocal p.val p.property
  let j : A.ComponentChartIndex x := ⟨i, ⟨p.val, hi, p.property⟩⟩
  obtain ⟨W, hW, hconn, hWe, hpW, huW⟩ :=
    pshWitness_subtypeRestr_cast (A.chart i) (A.componentChartDimension x j)
      (A.componentOpen x) (A.componentNonempty x) u p V hV hc hVe hpV hpsh
  refine ⟨A.componentComplexChart x j, ?_, W, hW, hconn, hWe, hpW, huW⟩
  change p ∈ (A.componentChart x j).source
  rw [A.componentChart_source x j]
  exact hi

/-- Every specified native component chart has the genuine original coordinate PSH germ. -/
theorem IsPSH.componentChartPlurisubharmonic {u : X → EReal} (hu : A.IsPSH u)
    (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    ∀ e : ComplexChart (A.pointDimension x) (A.componentOpen x),
      SGPT.Foundations.Analysis.PlurisubharmonicOn
        (chartFunction (fun p : A.componentOpen x ↦ u p.val) e) e.val.target := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  exact fun e ↦ (hu.componentManifoldPSH x).chartPlurisubharmonic e

end SGPT.PSH.VariableComplexAtlas
