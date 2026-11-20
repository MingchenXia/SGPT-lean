import SGPT.PSH.SubharmonicStrip

/-! Actual arbitrary-dimensional complex ball maximum principle.
Blueprint: complex-space-maximum-principle.tex. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.SingularMaximum

/-- The genuine one-dimensional strong maximum principle gives the
actual full-dimensional complex ball identity, including dimension zero. -/
theorem discPshOn_eqOn_ball_of_le_of_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (hu : DiscPshOn u U)
    (a : E) {R C : ℝ} (hBU : ball a R ⊆ U)
    (hC : ∀ y ∈ ball a R,u y ≤ (C : EReal)) (ha : u a = (C : EReal)) :
    EqOn u (fun _ => (C : EReal)) (ball a R) := by
  intro b hb
  by_cases hba : b = a
  · simpa [hba] using ha
  have hv : 0 < ‖b-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hba)
  have hbR : ‖b-a‖ < R := by simpa [dist_eq_norm] using hb
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight (b-a)
  have hline := hu.comp_affine L a
  have hball (z : ℂ) (hz : z ∈ ball (0 : ℂ) (R/‖b-a‖)) : a + L z ∈ ball a R := by
    have hn : ‖z‖ < R/‖b-a‖ := by simpa using hz
    have hl : ‖L z‖ < R := by
      change ‖z • (b-a)‖ < R
      rw [norm_smul]
      exact (lt_div_iff₀ hv).mp hn
    simpa [dist_eq_norm] using hl
  have hz : (fun z : ℂ => u (a+L z)) 0 = (C : EReal) := by simpa using ha
  have heq := hline.eqOn_ball_of_le_of_eq (0 : ℂ)
    (fun z hz => hBU (hball z hz)) (fun z hz => hC _ (hball z hz)) hz
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (R/‖b-a‖) := by
    simpa using (lt_div_iff₀ hv).mpr (by simpa using hbR)
  simpa [L] using heq h1

end SGPT.Unibranch.SingularMaximum
