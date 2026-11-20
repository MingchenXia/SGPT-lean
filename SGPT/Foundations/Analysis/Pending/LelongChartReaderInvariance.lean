import SGPT.Foundations.Analysis.Pending.LelongNumberComparison

set_option autoImplicit false

/-! # Genuine holomorphic-chart and continuous-real-germ invariance of Lelong readers -/

open Set Filter Asymptotics
open scoped Topology ENNReal NNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance

open FirstPass FirstPass.NonKahlerLocus LelongNumberComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V]

omit [IsComplexManifold n M] [IsComplexManifold n V] in
private theorem lelongNumber_le_comp_of_eventually_ne {f : V → M} {z : V}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f z)
    (hne : ∀ᶠ z' in 𝓝[≠] z, f z' ≠ f z) {u : M → EReal} :
    lelongNumber (n := n) u (f z) ≤ lelongNumber (n := n) (fun z' => u (f z')) z := by
  set y := f z
  set d := complexChartAt (n := n) y
  set e := complexChartAt (n := n) z
  have hze : z ∈ e.val.source := mem_complexChartAt_source z
  have hyd : y ∈ d.val.source := mem_complexChartAt_source y
  set F : ComplexModel n → ComplexModel n := fun w => d.val (f (e.val.symm w))
  have hFd : DifferentiableAt ℂ F (e.val z) := by
    have h := hf.differentiableWithinAt_writtenInExtChartAt
    simp only [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at h
    exact h
  obtain ⟨c, hc, hcw⟩ := hFd.hasFDerivAt.isBigO_sub.exists_pos
  have hlip : ∀ᶠ z' in 𝓝 z, ‖d.val (f z') - d.val y‖ ≤ c * ‖e.val z' - e.val z‖ := by
    have h1 := (e.val.continuousAt hze).eventually hcw.bound
    filter_upwards [h1, e.val.open_source.mem_nhds hze] with z' hz' hz'e
    simpa [F, e.val.left_inv hz'e, e.val.left_inv hze] using hz'
  have hfc : ContinuousAt f z := hf.continuousAt
  unfold lelongNumber
  refine iSup₂_le fun γ hγC => ?_
  obtain ⟨C, hC⟩ := hγC
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp
  have hγpos : (0 : ℝ) < γ := by
    have := (pos_iff_ne_zero (a := γ)).mpr hγ0
    exact_mod_cast this
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ z' in 𝓝[≠] z,
      u (f z') ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) z).val z' - (complexChartAt (n := n) z).val z‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ ⟨C + γ * Real.log c, ?_⟩ le_rfl
  have hC' : ∀ᶠ z' in 𝓝 z, f z' ≠ y → u (f z') ≤ ((γ * Real.log
      ‖d.val (f z') - d.val y‖ + C : ℝ) : EReal) :=
    hfc.eventually (eventually_nhdsWithin_iff.mp hC)
  have hsrc : ∀ᶠ z' in 𝓝 z, f z' ∈ d.val.source :=
    hfc.eventually (d.val.open_source.mem_nhds hyd)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hC',
    eventually_nhdsWithin_of_eventually_nhds hsrc,
    eventually_nhdsWithin_of_eventually_nhds hlip,
    eventually_nhdsWithin_of_eventually_nhds (e.val.open_source.mem_nhds hze), hne]
    with z' h1 h2 h3 h4 h5
  have hz'z : z' ≠ z := fun h => h5 (congrArg f h)
  have hnz : 0 < ‖e.val z' - e.val z‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hz'z (e.val.injOn h4 hze h)
  have hny : 0 < ‖d.val (f z') - d.val y‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => h5 (d.val.injOn h2 hyd h)
  refine (h1 h5).trans (EReal.coe_le_coe_iff.mpr ?_)
  have hlog : Real.log ‖d.val (f z') - d.val y‖ ≤ Real.log c + Real.log ‖e.val z' - e.val z‖ := by
    rw [← Real.log_mul hc.ne' hnz.ne']
    exact Real.log_le_log hny h3
  nlinarith [hlog, hγpos]

/-- Actual holomorphic atlas charts preserve the literal logarithmic reader
for arbitrary extended-real functions; their local injectivity is supplied internally. -/
theorem lelongNumber_chartFunction_eq {u : M → EReal} (e : ComplexChart n M)
    {x : M} (hx : x ∈ e.val.source) :
    lelongNumber (n := n) (chartFunction u e) (e.val x) = lelongNumber (n := n) u x := by
  have ht : e.val x ∈ e.val.target := e.val.map_source hx
  have hsymm : ∀ᶠ w in 𝓝[≠] (e.val x), e.val.symm w ≠ e.val.symm (e.val x) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [e.val.open_target.mem_nhds ht] with w hw hne
    exact fun h => hne (e.val.symm.injOn hw ht h)
  have hchart : ∀ᶠ y in 𝓝[≠] x, e.val y ≠ e.val x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [e.val.open_source.mem_nhds hx] with y hy hne
    exact fun h => hne (e.val.injOn hy hx h)
  have h₁ := lelongNumber_le_comp_of_eventually_ne
    (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property ht) hsymm (u := u)
  have h₂ := lelongNumber_le_comp_of_eventually_ne
    (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hx) hchart
      (u := chartFunction u e)
  have hgerm : (fun y => chartFunction u e (e.val y)) =ᶠ[𝓝 x] u := by
    filter_upwards [e.val.open_source.mem_nhds hx] with y hy
    change u (e.val.symm (e.val y)) = u y
    rw [e.val.left_inv hy]
  refine le_antisymm ?_ ?_
  · rwa [lelongNumber_congr hgerm] at h₂
  · change lelongNumber (n := n) u x ≤
      lelongNumber (n := n) (fun z => u (e.val.symm z)) (e.val x)
    simpa only [e.val.left_inv hx] using h₁

omit [IsComplexManifold n M] in
/-- A finite real correction continuous at the actual point preserves the
literal logarithmic reader, including all extended values. -/
theorem lelongNumber_add_continuous_eq {u : M → EReal} {h : M → ℝ} {x : M}
    (hh : ContinuousAt h x) :
    lelongNumber (n := n) (fun y => u y + (h y : EReal)) x = lelongNumber (n := n) u x := by
  refine le_antisymm (lelongNumber_add_le hh) ?_
  have hrev := KahlerCurrentMax.lelongNumber_sub_le (n := n)
    (u := fun y => u y + (h y : EReal)) hh
  simpa only [EReal.add_sub_cancel_right] using hrev

end
end SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
