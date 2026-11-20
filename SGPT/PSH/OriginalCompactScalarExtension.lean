import SGPT.PSH.OriginalGlobalOneZeroForms
import SGPT.PSH.SmoothVariableBetaTests

/-! Actual zero extension of compact scalar chart tests to the ORIGINAL
Hausdorff manifold; all-chart smoothness and physical coordinate readback. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Genuine original function: actual compact chart test, zero off its source. -/
def originalCompactScalarExtension (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ)) : X → ℝ := by
  classical
  exact fun x => if x∈(A.chart i).source then g (A.chart i x) else 0

/-- Exact physical value in the original chart, including zero-dimensional charts. -/
theorem originalCompactScalarExtension_coordinate (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ))
    {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    originalCompactScalarExtension A i g ((A.chart i).symm z)=g z := by
  simp [originalCompactScalarExtension,(A.chart i).map_target hz,(A.chart i).right_inv hz]

/-- The geometric support carrier is an ACTUAL compact subset of the chart
source; Hausdorffness proves it closed rather than assuming a support flag. -/
theorem originalCompactScalarExtension_geometric_compact (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ)) :
    IsCompact ((A.chart i).symm '' tsupport g) ∧
      (A.chart i).symm '' tsupport g ⊆ (A.chart i).source := by
  constructor
  · exact g.hasCompactSupport.image_of_continuousOn
      ((A.chart i).continuousOn_symm.mono g.tsupport_subset)
  · rintro x ⟨z,hz,rfl⟩
    exact (A.chart i).map_target (g.tsupport_subset hz)

/-- Actual zero off that compact geometric support carrier. -/
theorem originalCompactScalarExtension_zero_off (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ)) {x : X}
    (hx : x∉(A.chart i).symm '' tsupport g) : originalCompactScalarExtension A i g x=0 := by
  by_cases hxs : x∈(A.chart i).source
  · rw [originalCompactScalarExtension,if_pos hxs]
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    exact ⟨A.chart i x,h,(A.chart i).left_inv hxs⟩
  · simp [originalCompactScalarExtension,hxs]

/-- All ORIGINAL chart smoothness is PRODUCED by genuine holomorphic overlap
composition near the support and actual local zero off its closed carrier.
No native manifold, global countability, compactness or output premise. -/
theorem originalCompactScalarExtension_smooth [T2Space X] (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ)) :
    OriginalRealSmooth A (originalCompactScalarExtension A i g) := by
  intro j z hz
  let F := (A.chart j).symm.trans (A.chart i)
  by_cases hx : (A.chart j).symm z∈(A.chart i).source
  · have hzF : z∈F.source := ⟨hz,hx⟩
    have heq : (originalCompactScalarExtension A i g ∘ (A.chart j).symm)=ᶠ[𝓝 z] g ∘ F := by
      filter_upwards [F.open_source.mem_nhds hzF] with y hy
      have hyi : (A.chart j).symm y∈(A.chart i).source := hy.2
      simp only [Function.comp_apply,originalCompactScalarExtension,if_pos hyi]
      rfl
    have hgs : ContDiffAt ℝ ∞ (g ∘ F) z :=
      g.contDiff.contDiffAt.comp z (atlasTransition_contDiffAt_real hzF)
    exact (hgs.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hc := originalCompactScalarExtension_geometric_compact A i g
    have hxK : (A.chart j).symm z∉(A.chart i).symm '' tsupport g := fun h => hx (hc.2 h)
    have hAj : ContinuousAt (A.chart j).symm z :=
      (A.chart j).continuousOn_symm.continuousAt ((A.chart j).open_target.mem_nhds hz)
    have hpre : ∀ᶠ y in 𝓝 z,(A.chart j).symm y∉(A.chart i).symm '' tsupport g :=
      hAj.preimage_mem_nhds (hc.1.isClosed.isOpen_compl.mem_nhds hxK)
    have heq : (originalCompactScalarExtension A i g ∘ (A.chart j).symm)=ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hpre] with y hy
      exact originalCompactScalarExtension_zero_off A i g hy
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Entire own-chart coordinate functions agree on an ACTUAL neighborhood. -/
theorem originalCompactScalarExtension_coordinate_eventually (i : A.Index)
    (g : 𝓓(⟨(A.chart i).target,(A.chart i).open_target⟩,ℝ))
    {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    (originalCompactScalarExtension A i g ∘ (A.chart i).symm)=ᶠ[𝓝 z] g := by
  filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
  exact originalCompactScalarExtension_coordinate A i g hy

end SGPT.PSH.ComplexCurrentDraft
