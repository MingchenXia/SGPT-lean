import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse

set_option autoImplicit false

/-! # Raw Lelong covariance from an actual unramified holomorphic map

The genuine local inverse supplies both punctured avoidance conditions.
No center-pole implication is imposed on the arbitrary raw weight.
Reference: Demailly, CADG, coordinate invariance; direct logarithmic-exponent adaptation.
-/

open Set Filter Asymptotics
open scoped Topology ENNReal NNReal Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawUnramifiedLelongCovariance

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences LelongNumberComparison

noncomputable section

section PuncturedTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]

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

end PuncturedTransport

/-- The actual inverse-function theorem supplies both punctured avoidance
facts, so arbitrary raw readers are literally equal without a center-pole premise. -/
theorem lelongNumber_comp_eq_of_not_exceptional {n : ℕ}
    {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {z : Z} (hz : z ∉ exceptionalLocus n g) {u : Y → EReal} :
    lelongNumber (n := n) (fun z' => u (g z')) z = lelongNumber (n := n) u (g z) := by
  obtain ⟨V, s, hV, hgzV, hsz, hgs, hss, hnear⟩ :=
    HolomorphicLocalInverse.exists_localInverse hg hz
  have hneG : ∀ᶠ z' in 𝓝[≠] z, g z' ≠ g z := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hnear] with z' hz' hne
    intro heq
    apply hne
    exact hz'.symm.trans ((congrArg s heq).trans hsz)
  have hneS : ∀ᶠ y in 𝓝[≠] (g z), s y ≠ s (g z) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hV.mem_nhds hgzV] with y hy hne
    intro heq
    apply hne
    exact (hgs y hy).symm.trans ((congrArg g heq).trans (hgs (g z) hgzV))
  have h₁ := lelongNumber_le_comp_of_eventually_ne
    ((hg z).mdifferentiableAt (by simp)) hneG (u := u)
  have h₂ := lelongNumber_le_comp_of_eventually_ne
    ((hss (g z) hgzV).mdifferentiableAt (by simp)) hneS (u := fun z' => u (g z'))
  rw [hsz] at h₂
  have heq : (fun y => u (g (s y))) =ᶠ[𝓝 (g z)] u := by
    filter_upwards [hV.mem_nhds hgzV] with y hy
    exact congrArg u (hgs y hy)
  exact le_antisymm (h₂.trans_eq (lelongNumber_congr heq)) h₁

end
end SGPT.Foundations.Analysis.Pending.RawUnramifiedLelongCovariance
