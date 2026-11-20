import SGPT.Foundations.Analysis.Pending.DolbeaultLemma
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl
import SGPT.PSH.SiuL2Local

/-!
# Smooth representatives of scalar weak `∂̄` solutions

This is the regularity bridge needed when constructing holomorphic frames on
the fixed coordinate balls in Siu's uniform-generation argument.  The weak
solution is an actual locally integrable scalar function.  Smoothness is an
output: local smooth Dolbeault primitives are subtracted, Weyl's lemma gives
holomorphic remainders, and the resulting representatives agree on overlaps.

Blueprint: `siu-uniform-generation.tex`, node `siu-uniform:dbar-primitive`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.PSH.GlobalL2

variable {n : ℕ}

/-- A locally integrable weak solution of a smooth closed scalar `∂̄` equation
has a smooth representative satisfying the same equation pointwise. -/
theorem exists_smoothRepresentative_of_weakDbarEq
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (α : Fin n → ComplexModel n → ℂ) (hα : ∀ j, ContDiffOn ℝ ∞ (α j) U)
    (hclosed : IsDbarClosedOn α U)
    {u : ComplexModel n → ℂ} (hu : LocallyIntegrableOn u U)
    (hweak : WeakDbarEq U u α) :
    ∃ v : ComplexModel n → ℂ, ContDiffOn ℝ ∞ v U ∧
      (∀ j, ∀ x ∈ U, dbarDir (coordVec j) v x = α j x) ∧
      ∀ᵐ x ∂(volume.restrict U), u x = v x := by
  have hlocal : ∀ x ∈ U, ∃ W : Set (ComplexModel n),
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ v : ComplexModel n → ℂ,
        ContDiffOn ℝ ∞ v W ∧
        (∀ j, ∀ y ∈ W, dbarDir (coordVec j) v y = α j y) ∧
        ∀ᵐ y ∂(volume.restrict W), u y = v y := by
    intro x hx
    obtain ⟨W, hWo, hxW, hWU, f, hf, hfα⟩ := exists_dbar_primitive hU α hα hclosed hx
    have huW : LocallyIntegrableOn u W := hu.mono_set hWU
    have hfW : LocallyIntegrableOn f W :=
      hf.continuous.continuousOn.locallyIntegrableOn hWo.measurableSet
    have hdiff : LocallyIntegrableOn (fun y => u y - f y) W := huW.sub hfW
    have hcoord : ∀ h, IsTestFunctionOn W h → ∀ j,
        ∫ y, (u y - f y) * dbarDir (coordVec j) h y = 0 := by
      intro h hh j
      have hdc : Continuous (dbarDir (coordVec j) h) :=
        continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
      have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
      have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
      have hiu := integrable_mul_of_locallyIntegrableOn huW hdc hdcs hdts
      have hif := integrable_mul_of_locallyIntegrableOn hfW hdc hdcs hdts
      have hueq := hweak h ⟨hh.1, hh.2.1, hh.2.2.trans hWU⟩ j
      have hfeq := weakDbarEq_of_contDiffOn hWo
        (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn h hh j
      have heq : (∫ y, α j y * h y) = ∫ y, dbarDir (coordVec j) f y * h y := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ W
          · change α j y * h y = dbarDir (basisVec j) f y * h y
            rw [hfα j y hy]
          · have hz : h y = 0 := image_eq_zero_of_notMem_tsupport
              (fun hys => hy (hh.2.2 hys))
            simp only [hz, mul_zero]
      simp only [sub_mul]
      rw [integral_sub hiu hif, hueq, hfeq, heq, sub_self]
    obtain ⟨H, hH, hHae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hWo hdiff
      (integral_mul_dbarDir_eq_zero_of_coord hdiff hcoord)
    refine ⟨W, hWo, hxW, hWU, fun y => f y + H y,
      hf.contDiffOn.add (contDiffOn_real_of_differentiableOn_complex hH hWo), ?_, ?_⟩
    · intro j y hy
      have hHd : DifferentiableAt ℂ H y := hH.differentiableAt (hWo.mem_nhds hy)
      rw [dbarDir_add (hf.differentiable (by simp) y) (hHd.restrictScalars ℝ),
        hfα j y hy, dbarDir_eq_zero_of_differentiableAt hHd, add_zero]
    · filter_upwards [hHae] with y hy
      exact sub_eq_iff_eq_add.mp hy |>.trans (add_comm _ _)
  choose! W hWo hxW hWU v₀ hv₀ hveq hvae using hlocal
  have hagree : ∀ x ∈ U, ∀ y ∈ U, EqOn (v₀ x) (v₀ y) (W x ∩ W y) := by
    intro x hx y hy
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ ((hWo x hx).inter (hWo y hy))
      ((hv₀ x hx).continuousOn.mono inter_subset_left)
      ((hv₀ y hy).continuousOn.mono inter_subset_right)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (hvae x hx),
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hvae y hy)] with z hz1 hz2
    rw [← hz1, hz2]
  let v : ComplexModel n → ℂ := fun x => v₀ x x
  have hveq_local : ∀ x ∈ U, EqOn v (v₀ x) (W x) := by
    intro x hx y hy
    have hyU := hWU x hx hy
    exact hagree y hyU x hx ⟨hxW y hyU, hy⟩
  have hvevent : ∀ x ∈ U, v =ᶠ[𝓝 x] v₀ x := fun x hx =>
    eventually_of_mem ((hWo x hx).mem_nhds (hxW x hx)) (hveq_local x hx)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro x hx
    exact (((hv₀ x hx).contDiffAt ((hWo x hx).mem_nhds (hxW x hx))).congr_of_eventuallyEq
      (hvevent x hx)).contDiffWithinAt
  · intro j x hx
    rw [dbarDir_congr (hvevent x hx)]
    exact hveq x hx j x (hxW x hx)
  · obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : U => W x) fun x => hWo x x.2
    have hUeq : U = ⋃ x ∈ T, W x := by
      rw [hTU]
      ext y
      simp only [mem_iUnion]
      exact ⟨fun hy => ⟨⟨y, hy⟩, hxW y hy⟩, fun ⟨x, hx⟩ => hWU x x.2 hx⟩
    rw [hUeq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hvae x x.2, ae_restrict_mem (hWo x x.2).measurableSet] with y h1 h2
    rw [h1, hveq_local x x.2 h2]

/-- Classical closedness of a smooth scalar `(0,1)`-form implies the exact weak
closedness hypothesis consumed by the existing Hörmander solver. -/
theorem weakDbarClosed_of_isDbarClosedOn
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (α : Fin n → ComplexModel n → ℂ) (hα : ∀ j, ContDiffOn ℝ ∞ (α j) U)
    (hclosed : IsDbarClosedOn α U) : WeakDbarClosed U α := by
  intro h hh j k
  have hloc : ∀ i, LocallyIntegrableOn (α i) U := fun i =>
    (hα i).continuousOn.locallyIntegrableOn hU.measurableSet
  have hi : ∀ i l, Integrable (fun x => α i x * dbarDir (coordVec l) h x) := fun i l =>
    integrable_mul_of_locallyIntegrableOn (hloc i)
      (continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top)))
      (hasCompactSupport_dbarDir hh.2.1) ((tsupport_dbarDir_subset _ h).trans hh.2.2)
  have hj := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hU
    ((hα k).of_le (WithTop.coe_le_coe.mpr le_top))
    (hh.1.of_le (WithTop.coe_le_coe.mpr le_top)) hh.2.1 hh.2.2 (coordVec j)
  have hk := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hU
    ((hα j).of_le (WithTop.coe_le_coe.mpr le_top))
    (hh.1.of_le (WithTop.coe_le_coe.mpr le_top)) hh.2.1 hh.2.2 (coordVec k)
  have heq : (∫ x, dbarDir (coordVec j) (α k) x * h x) =
      ∫ x, dbarDir (coordVec k) (α j) x * h x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · change dbarDir (basisVec j) (α k) x * h x =
          dbarDir (basisVec k) (α j) x * h x
        rw [hclosed j k x hx]
      · have hz : h x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxs => hx (hh.2.2 hxs))
        simp only [hz, mul_zero]
  rw [integral_sub (hi k j) (hi j k), hj, hk, heq, sub_self]

/-- A smooth closed scalar `(0,1)`-form on a ball has a smooth primitive on
every strictly smaller ball.  The weak primitive is produced by the existing
Hörmander theorem; its smoothness follows from the preceding local
Dolbeault/Weyl representative theorem. -/
theorem exists_smooth_dbar_primitive_on_ball
    (c : ComplexModel n) {r R : ℝ} (_hr : 0 < r) (hrR : r < R)
    (α : Fin n → ComplexModel n → ℂ)
    (hα : ∀ j, ContDiffOn ℝ ∞ (α j) (ball c R))
    (hclosed : IsDbarClosedOn α (ball c R)) :
    ∃ v : ComplexModel n → ℂ, ContDiffOn ℝ ∞ v (ball c r) ∧
      ∀ j, ∀ x ∈ ball c r, dbarDir (coordVec j) v x = α j x := by
  let R' : ℝ := (r + R) / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hR'R : R' < R := by dsimp [R']; linarith
  have hcl : closedBall c R' ⊆ ball c R := closedBall_subset_ball hR'R
  obtain ⟨D, U, l₁, l₂, hDo, -, hDcl, -, hKU, hUD, hl₁, hl₂, hl, -, hest⟩ :=
    hormanderL2Estimate n (ball c R') isOpen_ball (convex_ball _ _) (isBounded_ball)
      (closedBall c r) (isCompact_closedBall _ _) (closedBall_subset_ball hrR') 1 one_pos
  have hDball : D ⊆ ball c R' := subset_closure.trans hDcl
  have hDclosed : D ⊆ closedBall c R' := hDball.trans ball_subset_closedBall
  have hDR : D ⊆ ball c R := hDclosed.trans hcl
  have hrD : ball c r ⊆ D := ball_subset_closedBall.trans (hKU.trans hUD)
  have hDfinite : volume D ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall c R').measure_ne_top (measure_mono hDclosed)
  have hαD : ∀ j, ContDiffOn ℝ ∞ (α j) D := fun j => (hα j).mono hDR
  have hclosedD : IsDbarClosedOn α D := fun i j x hx => hclosed i j x (hDR hx)
  have hnormc : Continuous (fun z : ComplexModel n => ‖z‖ ^ 2) := continuous_norm.pow 2
  have weighted_integrable (q : ComplexModel n → ℝ)
      (hqc : ContinuousOn q (closedBall c R')) (hq0 : ∀ z, 0 ≤ q z)
      (l : ComplexModel n → ℝ) (hlc : ContinuousOn l D) (hl0 : ∀ z ∈ D, 0 ≤ l z) :
      Integrable (fun z => q z * Real.exp (-(‖z‖ ^ 2 + l z))) (volume.restrict D) := by
    have hqi : Integrable q (volume.restrict D) :=
      hqc.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
        hDo.measurableSet hDclosed hDfinite
    refine hqi.mono' (((hqc.mono hDclosed).mul
      (hnormc.continuousOn.add hlc).neg.rexp).aestronglyMeasurable hDo.measurableSet) ?_
    refine (ae_restrict_iff' hDo.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 z) (Real.exp_pos _).le)]
    calc q z * Real.exp (-(‖z‖ ^ 2 + l z)) ≤ q z * 1 := by
          apply mul_le_mul_of_nonneg_left _ (hq0 z)
          rw [Real.exp_le_one_iff]
          linarith [sq_nonneg ‖z‖, hl0 z hz]
      _ = q z := mul_one _
  have hαmem : ∀ j, MemLp (α j) 2 (weightedVolume D fun z => ‖z‖ ^ 2 + l₂ z) := by
    intro j
    have hαc := (hα j).continuousOn.mono hcl
    rw [memLp_weightedVolume_iff (w := fun z => ‖z‖ ^ 2 + l₂ z)
      ((hnormc.continuousOn.add hl₂).aemeasurable hDo.measurableSet)
      ((hαD j).continuousOn.aestronglyMeasurable hDo.measurableSet)]
    exact weighted_integrable (fun z => ‖α j z‖ ^ 2) (hαc.norm.pow 2)
      (fun z => sq_nonneg _) l₂ hl₂ (fun z hz => (hl z hz).1.trans (hl z hz).2)
  let g : ComplexModel n → ℝ := fun z => ∑ j, ‖α j z‖ ^ 2
  have hg0 : ∀ z, 0 ≤ g z := fun z => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hgc : ContinuousOn g (closedBall c R') := by
    apply continuousOn_finsetSum
    intro j _
    exact ((hα j).continuousOn.mono hcl).norm.pow 2
  have hmajor : ∀ z ∈ D, ∀ ξ : Fin n → ℂ,
      ‖∑ j, conj (ξ j) * α j z‖ ^ 2 ≤
        g z * leviForm (fun z : ComplexModel n => ‖z‖ ^ 2) z (∑ j, ξ j • coordVec j) := by
    intro z _ ξ
    rw [leviForm_norm_sq]
    simpa only [g, mul_comm] using norm_sum_conj_mul_sq_le ξ (fun j => α j z)
  obtain ⟨⟨u, humem, hueq, -⟩, -⟩ := hest (fun z => ‖z‖ ^ 2)
    (contDiff_norm_sq ℝ).contDiffOn (fun z _ ξ => by rw [leviForm_norm_sq]; positivity)
    α hαmem (weakDbarClosed_of_isDbarClosedOn hDo α hαD hclosedD)
    g (fun z _ => hg0 z) hmajor
    (weighted_integrable g hgc hg0 l₁ hl₁ (fun z hz => (hl z hz).1))
  have huloc : LocallyIntegrableOn u D :=
    locallyIntegrableOn_of_memLp_weightedVolume hDo (hnormc.continuousOn.add hl₁) humem
  obtain ⟨v, hv, hvα, -⟩ :=
    exists_smoothRepresentative_of_weakDbarEq hDo α hαD hclosedD huloc hueq
  exact ⟨v, hv.mono hrD, fun j x hx => hvα j x (hrD hx)⟩

end SGPT.Bergman.SiuUniformGeneration
