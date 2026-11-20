import SGPT.Unibranch.ComplexPowerSubharmonic

/-! Full actual finite-power disc descent, including locally all-pole branches.
Blueprint: complex-power-disc-criterion.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.RamifiedPower

/-- Genuine finite-power descent of the full ORIGINAL raw disc criterion;
nontriviality is internally split, not an incoming analytic certificate. -/
theorem discPshOn_of_comp_pow {u : ℂ → EReal} (k : ℕ) (hk : 0 < k)
    {R : ℝ} (hR : 0 < R)
    (husc : UpperSemicontinuousOn u (ball (0 : ℂ) (R^k)))
    (hcomp : DiscPshOn (fun z => u (z^k)) (ball (0 : ℂ) R)) :
    DiscPshOn u (ball (0 : ℂ) (R^k)) := by
  by_cases hn : ∃ z ∈ ball (0 : ℂ) R,u (z^k) ≠ ⊥
  · exact (subharmonicOn_of_comp_pow k hk hR husc (SGPT.PSH.subharmonicOn_of_disc hcomp hn)).discPshOn
  · have hbot : ∀ z ∈ ball (0 : ℂ) (R^k),u z = ⊥ := by
      intro z hz
      obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq z hk
      have hwR : w ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        by_contra hnot
        have hp := pow_le_pow_left₀ hR.le (le_of_not_gt hnot) k
        have hzR : ‖z‖ < R^k := mem_ball_zero_iff.mp hz
        rw [← norm_pow,hw] at hp
        exact (not_lt_of_ge hp) hzR
      by_contra hne
      exact hn ⟨w,hwR,by rwa [hw]⟩
    exact (discPshOn_const (⊥ : EReal) bot_ne_top (ball (0 : ℂ) (R^k))).congr
      (fun z hz => (hbot z hz).symm)

end SGPT.Unibranch.RamifiedPower
