import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.WirtingerCalculus

/-!
# Kähler lowering

Blueprint `claude-twisted-l2:kahler-lowering`.  For a smooth real potential `r` with Levi matrix
`g_{lk} = ∂_l ∂_{k̄} r` and a smooth vector field `W`, the `(0,1)`-form `τ_k = ∑_l g_{lk} W_l`
(`lowerVector`) satisfies

`∂_{j̄} τ_k - ∂_{k̄} τ_j = ∑_l (g_{lk} ∂_{j̄} W_l - g_{lj} ∂_{k̄} W_l)`

because `∂_{j̄} g_{lk} = ∂_{l} ∂_{j̄} ∂_{k̄} r` is symmetric in `(j, k)` (this is `dσ = 0` for
`σ = ddᶜ r`).  Proof of `KahlerLoweringStatement`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.CauchyGreen
  SGPT.Foundations.Analysis.Pending.Hormander

variable {n : ℕ}

theorem contDiffOn_dDir_of_isOpen {D : Set (ComplexModel n)} (hD : IsOpen D)
    {f : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f D) (v : ComplexModel n) :
    ContDiffOn ℝ ∞ (dDir v f) D := by
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) D :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hD).mp hf).2
  unfold dDir
  exact ((h1.clm_apply contDiffOn_const).sub
    (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2

theorem contDiffOn_dbarDir_of_isOpen {D : Set (ComplexModel n)} (hD : IsOpen D)
    {f : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f D) (v : ComplexModel n) :
    ContDiffOn ℝ ∞ (dbarDir v f) D := by
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) D :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hD).mp hf).2
  unfold dbarDir
  exact ((h1.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2

theorem dbarDir_finset_sum {ι : Type*} (s : Finset ι) {v x : ComplexModel n}
    {f : ι → ComplexModel n → ℂ} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    dbarDir v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, dbarDir v (f i) x := by
  simp only [dbarDir, fderiv_fun_sum hf, _root_.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

/-- **Kähler lowering** (`claude-twisted-l2:kahler-lowering`). -/
theorem kahlerLoweringStatement : KahlerLoweringStatement n := by
  intro D hD r hr W hW z hz j k
  have hinf2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hR : ContDiffOn ℝ ∞ (fun y => (r y : ℂ)) D :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hr
  have hdR : ∀ l, ContDiffOn ℝ ∞ (dDir (coordVec l) (fun y => (r y : ℂ))) D := fun l =>
    contDiffOn_dDir_of_isOpen hD hR _
  have hg : ∀ l k', DifferentiableAt ℝ
      (dbarDir (coordVec k') (dDir (coordVec l) (fun y => (r y : ℂ)))) z := fun l k' =>
    (((contDiffOn_dbarDir_of_isOpen hD (hdR l) _).contDiffAt (hD.mem_nhds hz)).differentiableAt
      (by simp))
  have hWd : ∀ l, DifferentiableAt ℝ (W l) z := fun l =>
    ((hW l).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hsym : ∀ l, dbarDir (coordVec j)
      (dbarDir (coordVec k) (dDir (coordVec l) (fun y => (r y : ℂ)))) z =
      dbarDir (coordVec k) (dbarDir (coordVec j) (dDir (coordVec l) (fun y => (r y : ℂ)))) z :=
    fun l => dbarDir_dbarDir_comm (((hdR l).contDiffAt (hD.mem_nhds hz)).of_le hinf2)
  have hexp : ∀ a b : Fin n, dbarDir (coordVec a) (lowerVector r W b) z =
      ∑ l, (dbarDir (coordVec a)
          (dbarDir (coordVec b) (dDir (coordVec l) (fun y => (r y : ℂ)))) z * W l z +
        dbarDir (coordVec b) (dDir (coordVec l) (fun y => (r y : ℂ))) z *
          dbarDir (coordVec a) (W l) z) := by
    intro a b
    have : lowerVector r W b = fun y =>
        ∑ l, dbarDir (coordVec b) (dDir (coordVec l) (fun y => (r y : ℂ))) y * W l y := rfl
    rw [this, dbarDir_finset_sum (f := fun l y =>
      dbarDir (coordVec b) (dDir (coordVec l) (fun y => (r y : ℂ))) y * W l y) _
      fun l _ => (hg l b).mul (hWd l)]
    exact Finset.sum_congr rfl fun l _ => dbarDir_mul (hg l b) (hWd l)
  rw [hexp j k, hexp k j, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsym l]
  ring

end SGPT.Trace.TwistedL2
