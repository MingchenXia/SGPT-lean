import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.Pending.ThetaPshCollarGluing
import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

set_option autoImplicit false

noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff Classical

namespace SGPT.PSH.LocalCompactExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open FlatComplexTorus GlobalPotentialTransforms

/-- Actual shifted quadratics are potentials of the scaled flat form in
every original auxiliary chart. The full ddC identity is produced internally. -/
theorem quadratic_flat_potential {n : ℕ} (e : ComplexChart n (Torus n))
    (p : ComplexModel n) (a b : ℝ) :
    IsSmoothLocalPotential ((a / Real.pi) • (flatKahlerBackground n).form).val
      e e.val.target (fun z => a * ‖z - p‖ ^ 2 + b) := by
  have hnorm : ContDiffOn ℝ ∞ (fun z : ComplexModel n => ‖z - p‖ ^ 2) e.val.target :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hscaled : ContDiffOn ℝ ∞ (fun z : ComplexModel n => a * ‖z - p‖ ^ 2)
      e.val.target := by
    simpa only [smul_eq_mul] using hnorm.const_smul a
  refine ⟨e.val.open_target, Subset.rfl, hscaled.add contDiffOn_const, ?_⟩
  intro z hz
  rw [smoothDDC_add e.val.open_target hscaled contDiffOn_const hz,
    GlobalPotentialTransforms.smoothDDC_const, add_zero]
  have hddc : smoothDDC (fun y : ComplexModel n => a * ‖y - p‖ ^ 2) z =
      a • smoothDDC (fun y : ComplexModel n => ‖y - p‖ ^ 2) z := by
    simpa only [smul_eq_mul] using smoothDDC_smul e.val.open_target hnorm a hz
  rw [hddc, LocalBedfordTaylorCollar.smoothDDC_norm_sub_sq, smul_smul,
    ClosedRealOneOneForm.coeff_smul]
  simp only [div_eq_mul_inv]
  rfl

/-- The same actual quadratic collar globalizes every upper-bounded local
PSH function after a prescribed finite truncation. Its scale and bound depend
only on the original radius, upper bound and truncation, not on the function. -/
theorem exists_compact_flat_extension {n : ℕ}
    (e : ComplexChart n (Torus n)) (p : ComplexModel n)
    {r C L : ℝ} (hr : 0 < r)
    (hchart : closedBall p (3 * r) ⊆ e.val.target)
    {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u (ball p (3 * r)))
    (hC : ∀ z ∈ ball p (3 * r), u z ≤ (C : EReal)) :
    let B : ℝ := max C L
    let a : ℝ := (B - L + 2) / (3 * r ^ 2)
    let b : ℝ := L - 1 - a * r ^ 2
    ∃ (ha : 0 < a / Real.pi) (w : Torus n → EReal),
      IsThetaPshPotential (KahlerBackground.smul ha (flatKahlerBackground n)).form.val w ∧
      (∀ x, 0 ≤ w x ∧ w x ≤ ((max (B - b) 0 : ℝ) : EReal)) ∧
      ∀ z ∈ ball p r,
        w (e.val.symm z) + ((a * ‖z - p‖ ^ 2 + b : ℝ) : EReal) = max (u z) (L : EReal) := by
  dsimp only
  let B : ℝ := max C L
  let a : ℝ := (B - L + 2) / (3 * r ^ 2)
  let b : ℝ := L - 1 - a * r ^ 2
  let q : ComplexModel n → ℝ := fun z => a * ‖z - p‖ ^ 2 + b
  have hBL : L ≤ B := le_max_right _ _
  have hBC : C ≤ B := le_max_left _ _
  have ha : 0 < a := div_pos (by dsimp only [B]; linarith [le_max_right C L]) (by positivity)
  have hscale : 0 < a / Real.pi := div_pos ha Real.pi_pos
  let Ω := KahlerBackground.smul hscale (flatKahlerBackground n)
  have hpot : IsSmoothLocalPotential Ω.form.val e e.val.target q := by
    simpa only [Ω, KahlerBackground.smul_form] using quadratic_flat_potential e p a b
  have haeq : a * (3 * r ^ 2) = B - L + 2 := by
    dsimp only [a]
    exact div_mul_cancel₀ _ (by positivity)
  have hqlo (z : ComplexModel n) : b ≤ q z := by
    dsimp only [q]
    nlinarith [sq_nonneg ‖z - p‖]
  have hqinner {z : ComplexModel n} (hz : z ∈ ball p r) : q z ≤ L - 1 := by
    have hn : ‖z - p‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
    have hs : ‖z - p‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (z - p)]
    dsimp only [q, b]
    nlinarith
  have hqouter {z : ComplexModel n} (hz : z ∉ ball p (2 * r)) : B ≤ q z := by
    have hn : 2 * r ≤ ‖z - p‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hz
    have hs : (2 * r) ^ 2 ≤ ‖z - p‖ ^ 2 := by nlinarith [norm_nonneg (z - p)]
    dsimp only [q, b]
    nlinarith
  let U : Set (Torus n) := e.val.source ∩ e.val ⁻¹' ball p (3 * r)
  let U' : Set (Torus n) := e.val.symm '' ball p (2 * r)
  let f : Torus n → EReal := fun x => max (u (e.val x)) (L : EReal) - (q (e.val x) : EReal)
  have hU : IsOpen U := e.val.isOpen_inter_preimage isOpen_ball
  have hsmall : closedBall p (2 * r) ⊆ e.val.target := by
    intro z hz
    apply hchart
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (by linarith))
  have hclosed : IsClosed (e.val.symm '' closedBall p (2 * r)) :=
    ((isCompact_closedBall p (2 * r)).image_of_continuousOn
      (e.val.continuousOn_symm.mono hsmall)).isClosed
  have hclosure : closure U' ⊆ U := by
    have hsub : U' ⊆ e.val.symm '' closedBall p (2 * r) := image_mono ball_subset_closedBall
    intro x hx
    obtain ⟨z, hz, rfl⟩ := closure_minimal hsub hclosed hx
    refine ⟨e.val.map_target (hsmall hz), ?_⟩
    rw [mem_preimage, e.val.right_inv (hsmall hz)]
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith))
  have htrunc : PlurisubharmonicOn (fun z => max (u z) (L : EReal)) (ball p (3 * r)) :=
    hu.max (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)
  have hf : ThetaPlurisubharmonicOn Ω.form.val f U := by
    intro d z hz hxU
    have hx : d.val.symm z ∈ e.val.source := hxU.1
    have hez : e.val (d.val.symm z) ∈ ball p (3 * r) := hxU.2
    let V : Set (ComplexModel n) := ball p (3 * r)
    have hVtarget : V ⊆ e.val.target := ball_subset_closedBall.trans hchart
    have hpotV : IsSmoothLocalPotential Ω.form.val e V q := hpot.mono isOpen_ball hVtarget
    have hc : PlurisubharmonicOn (fun y => chartFunction f e y + (q y : EReal)) V := by
      intro y hy
      refine (htrunc y hy).congr ?_
      filter_upwards [isOpen_ball.mem_nhds hy] with t ht
      change max (u t) (L : EReal) =
        (max (u (e.val (e.val.symm t))) (L : EReal) - (q (e.val (e.val.symm t)) : EReal)) + (q t : EReal)
      rw [e.val.right_inv (hVtarget ht)]
      exact EReal.sub_add_cancel.symm
    obtain ⟨W, ρ, hpW, hρ, hcW⟩ := OpensRestriction.exists_witness_of_chart d e
      (d.val.map_target hz) hx hez hpotV hc
    rw [d.val.right_inv hz] at hpW
    exact ⟨W, ρ, hpW, hρ, hcW⟩
  have hcollar : ∀ x ∈ U \ U', f x ≤ (0 : EReal) := by
    intro x hx
    have hznot : e.val x ∉ ball p (2 * r) := by
      intro hz
      apply hx.2
      exact ⟨e.val x, hz, e.val.left_inv hx.1.1⟩
    have huB : max (u (e.val x)) (L : EReal) ≤ (B : EReal) := by
      exact max_le ((hC _ hx.1.2).trans (by exact_mod_cast hBC)) (by exact_mod_cast hBL)
    exact (EReal.sub_nonpos).mpr (huB.trans (by exact_mod_cast hqouter hznot))
  let w : Torus n → EReal := gluedMax U f (fun _ => 0)
  have hw : IsThetaPshPotential Ω.form.val w :=
    QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax hU hclosure hcollar hf
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr Ω.isSemipositive)
  refine ⟨hscale, w, hw, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · rw [show w x = max (f x) 0 from gluedMax_eq_max hx]
      refine ⟨le_max_right _ _, max_le ?_ (by exact_mod_cast le_max_right (B - b) 0)⟩
      have hux : max (u (e.val x)) (L : EReal) ≤ (B : EReal) :=
        max_le ((hC _ hx.2).trans (by exact_mod_cast hBC)) (by exact_mod_cast hBL)
      have hdiff : f x ≤ ((B - b : ℝ) : EReal) := by
        calc
          _ ≤ (B : EReal) - (b : EReal) := EReal.sub_le_sub hux (by exact_mod_cast hqlo (e.val x))
          _ = _ := (EReal.coe_sub _ _).symm
      exact hdiff.trans (by exact_mod_cast le_max_left (B - b) 0)
    · simp only [w, gluedMax, hx, ↓reduceIte]
      exact ⟨le_rfl, by exact_mod_cast le_max_right (B - b) 0⟩
  · intro z hz
    have hzt : z ∈ e.val.target := hchart (mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by linarith)))
    have hzu : e.val.symm z ∈ U := by
      refine ⟨e.val.map_target hzt, ?_⟩
      rw [mem_preimage, e.val.right_inv hzt]
      exact mem_ball.mpr ((mem_ball.mp hz).trans (by linarith))
    have hfpos : 0 ≤ f (e.val.symm z) := by
      change 0 ≤ max (u (e.val (e.val.symm z))) (L : EReal) - (q (e.val (e.val.symm z)) : EReal)
      rw [e.val.right_inv hzt]
      apply (EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _))
        (Or.inr (EReal.coe_ne_bot _))).mpr
      exact (show (q z : EReal) ≤ (L : EReal) by
        exact_mod_cast (hqinner hz).trans (by linarith : L - 1 ≤ L)).trans (le_max_right _ _)
    change gluedMax U f (fun _ => 0) (e.val.symm z) + (q z : EReal) = _
    rw [gluedMax_eq_max hzu, max_eq_left hfpos]
    change (max (u (e.val (e.val.symm z))) (L : EReal) - (q (e.val (e.val.symm z)) : EReal)) + (q z : EReal) = _
    rw [e.val.right_inv hzt]
    exact EReal.sub_add_cancel

end SGPT.PSH.LocalCompactExtension
