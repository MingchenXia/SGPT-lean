import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties

set_option autoImplicit false

/-! # Literal Lelong readers in arbitrary local holomorphic coordinates

Actual differentiated inverses supply punctured-point avoidance in both
directions, so no pole or regularity assumption is required on the raw weight.
The coordinate-log coefficient is then returned at every point of its actual
hyperplane, not only at the center of the standard chart.
Reference: Demailly, CADG, coordinate invariance; supplementary raw-reader
adaptation of the logarithmic-exponent definition.
-/

open Set Filter Asymptotics
open scoped Topology ENNReal NNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance

open FirstPass FirstPass.NonKahlerLocus LelongNumberComparison

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

/-- Every point in the actual source of a local holomorphic inverse has
literal raw-reader covariance, including infinite values and dimension zero. -/
theorem lelongNumber_comp_inv_eq {n : ℕ} {p x : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (hx : x ∈ Φ.source)
    {u : ComplexModel n → EReal} :
    lelongNumber (n := n) (fun z => u (Φ.invFun z)) (Φ.toFun x) =
      lelongNumber (n := n) u x := by
  have hq : Φ.toFun x ∈ Φ.target := Φ.mapsTo_toFun hx
  have hto := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hx)
  have hinv := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)
  have hneTo : ∀ᶠ z in 𝓝[≠] x, Φ.toFun z ≠ Φ.toFun x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Φ.isOpen_source.mem_nhds hx] with z hz hne
    intro heq
    apply hne
    change z = x
    simpa only [Φ.left_inv z hz, Φ.left_inv x hx] using congrArg Φ.invFun heq
  have hneInv : ∀ᶠ z in 𝓝[≠] (Φ.toFun x), Φ.invFun z ≠ Φ.invFun (Φ.toFun x) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Φ.isOpen_target.mem_nhds hq] with z hz hne
    intro heq
    apply hne
    change z = Φ.toFun x
    simpa only [Φ.right_inv z hz, Φ.right_inv (Φ.toFun x) hq] using congrArg Φ.toFun heq
  have h₁ := lelongNumber_le_comp_of_eventually_ne hinv.mdifferentiableAt hneInv (u := u)
  have h₂ := lelongNumber_le_comp_of_eventually_ne hto.mdifferentiableAt hneTo
    (u := fun z => u (Φ.invFun z))
  have hgerm : (fun z => u (Φ.invFun (Φ.toFun z))) =ᶠ[𝓝 x] u :=
    (show ∀ᶠ z in 𝓝 x, z ∈ Φ.source from Φ.isOpen_source.mem_nhds hx).mono
      fun z hz => congrArg u (Φ.left_inv z hz)
  refine le_antisymm ?_ ?_
  · rwa [lelongNumber_congr hgerm] at h₂
  · simpa only [Φ.left_inv x hx] using h₁

/-- At every point of its genuine coordinate hyperplane, the literal
coordinate logarithm has coefficient one; no pointwise Lelong certificate is assumed. -/
theorem lelongNumber_coordinate_log_eq_one_of_eq_zero {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z j‖)) x = 1 := by
  let Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z + x
    invFun := fun z => z - x
    toFun_holomorphic := differentiable_id.add_const x |>.differentiableOn
    invFun_holomorphic := differentiable_id.sub_const x |>.differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => add_sub_cancel_right z x
    right_inv := fun z _ => sub_add_cancel z x }
  have h := lelongNumber_comp_inv_eq Φ (mem_univ (0 : ComplexModel n))
    (u := fun z => ENNReal.log (ENNReal.ofReal ‖z j‖))
  have heq : (fun z => ENNReal.log (ENNReal.ofReal ‖(Φ.invFun z) j‖)) =
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z j‖)) := by
    funext z
    simp only [Φ, PiLp.sub_apply, hx, sub_zero]
  rw [heq] at h
  simpa only [Φ, zero_add,
    CoordinateLogarithmLelongNormalization.lelongNumber_coordinate_log_eq_one] using h

end
end SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
