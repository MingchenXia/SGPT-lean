import SGPT.PSH.HermitianQuadratic
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-!
# Freezing a smooth one-one background with arbitrarily small error

For each positive `ε`, continuity bounds a smooth background by the constant
form obtained from its value at the centre plus `ε/2` times the flat form.
The constant form has an actual smooth local `ddᶜ` potential. Its Hessian
lies between the original background and that background plus `ε` times
the flat form. This is the sharp local correction in FPT, Section 14.8;
the original background is not assumed closed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianFreezing

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents

variable {n : ℕ}

/-- A smooth real `(1,1)` background has genuine local smooth corrections
whose Hessian error is arbitrarily small in every complex tangent direction. -/
theorem exists_local_approximate_potential
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → RealForm n 2) (ha : ContDiffOn ℝ ∞ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) {z : ComplexModel n} (hz : z ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (W : Set (ComplexModel n)) (q : ComplexModel n → ℝ),
      z ∈ W ∧ IsOpen W ∧ W ⊆ U ∧ ContDiffOn ℝ ∞ q W ∧
      ∀ x ∈ W, ∀ v : ComplexModel n,
        a x ![v, Complex.I • v] ≤ smoothDDC q x ![v, Complex.I • v] ∧
        smoothDDC q x ![v, Complex.I • v] ≤
          a x ![v, Complex.I • v] + ε * ‖v‖ ^ 2 := by
  have hc : ContinuousAt (fun x => ‖a x - a z‖) z :=
    ((ha.continuousOn.continuousAt (hU.mem_nhds hz)).sub continuousAt_const).norm
  have hn : ∀ᶠ x in 𝓝 z, ‖a x - a z‖ < ε / 2 :=
    hc.eventually (isOpen_Iio.mem_nhds (by simpa using half_pos hε))
  have hnear : {x | x ∈ U ∧ ‖a x - a z‖ < ε / 2} ∈ 𝓝 z :=
    (show ∀ᶠ x in 𝓝 z, x ∈ U from hU.mem_nhds hz).and hn
  obtain ⟨V, hVsub, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  let γ : RealForm n 2 := a z + (ε / 2) • kahlerForm n
  have hγ : IsOneOne γ := by
    intro v w
    simp only [γ, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [h11 z hz v w, isSemipositiveOneOne_kahlerForm.1 v w]
  have hclosed : ∀ x ∈ V, extDeriv (fun _ : ComplexModel n => γ) x = 0 := by
    intro x _
    change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
      (fderiv ℝ (fun _ : ComplexModel n => γ) x) = 0
    rw [fderiv_const_apply, map_zero]
  obtain ⟨W, q, hzW, hW, hWV, hq, hddc⟩ :=
    LocalPotentials.exists_smooth_local_ddc_potential hV (fun _ => γ)
      contDiffOn_const hclosed (fun _ _ => hγ) hzV
  refine ⟨W, q, hzW, hW, fun x hx => (hVsub (hWV hx)).1, hq, ?_⟩
  intro x hx v
  have hnorm : ‖a x - a z‖ ≤ ε / 2 := (hVsub (hWV hx)).2.le
  have hop := (a x - a z).le_opNorm ![v, Complex.I • v]
  rw [Fin.prod_univ_two] at hop
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul,
    Complex.norm_I, one_mul, Real.norm_eq_abs] at hop
  have hbound : |(a x - a z) ![v, Complex.I • v]| ≤ (ε / 2) * ‖v‖ ^ 2 := by
    have hi : |(a x - a z) ![v, Complex.I • v]| ≤ ‖a x - a z‖ * ‖v‖ ^ 2 := by
      nlinarith [hop]
    exact hi.trans (mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖))
  have hbounds := abs_le.mp hbound
  simp only [ContinuousAlternatingMap.sub_apply] at hbounds
  rw [hddc hx]
  change a x ![v, Complex.I • v] ≤
      a z ![v, Complex.I • v] + (ε / 2) * kahlerForm n ![v, Complex.I • v] ∧
    a z ![v, Complex.I • v] + (ε / 2) * kahlerForm n ![v, Complex.I • v] ≤
      a x ![v, Complex.I • v] + ε * ‖v‖ ^ 2
  rw [kahlerForm_apply_I]
  constructor <;> linarith

end SGPT.PSH.HermitianFreezing
