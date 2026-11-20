import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

/-!
# Full native divisor currents of actual holomorphic powers

The geometric integration currents are identified using the proved full
Poincaré--Lelong identity and actual locally integrable logarithms.  This uses
the repository's native `ddC log |g|²` convention, without identifying it with
the potential-growth Lelong reader or a differently normalized source current.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentPower

open _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents
  DivisorIntegrationCurrent LelongPoincareDivisor

/-- Every natural power internally supplies its holomorphicity and nonzero
germs, and its entire geometric integration current is the indicated multiple.
No logarithmic integrability or current equality is an input. -/
theorem exists_divisorCurrent_pow {n : ℕ}
    {Ω : Opens (EuclideanSpace ℂ (Fin n))} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (a : ℕ) :
    ∃ (hga : DifferentiableOn ℂ (fun x => g x ^ a) Ω)
      (hga0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ^ a ≠ 0),
      divisorCurrent hga hga0 = (a : ℝ) • divisorCurrent hg hg0 := by
  have hga : DifferentiableOn ℂ (fun x => g x ^ a) Ω := hg.pow a
  have hga0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ^ a ≠ 0 :=
    fun y hy => (hg0 y hy).mono (fun z hz => pow_ne_zero a hz)
  have hL := locallyIntegrableOn_log_normSq Ω.isOpen hg hg0
  have hLa := locallyIntegrableOn_log_normSq Ω.isOpen hga hga0
  have hLC : LocallyIntegrableOn (fun x => (a : ℝ) * Real.log (‖g x‖ ^ 2))
      Ω volume := by
    simpa only [Pi.smul_def, smul_eq_mul] using hL.smul (a : ℝ)
  have hlog : ∀ x, Real.log (‖g x ^ a‖ ^ 2) =
      (a : ℝ) * Real.log (‖g x‖ ^ 2) := by
    intro x
    rw [norm_pow, ← pow_mul, Nat.mul_comm a 2, pow_mul, Real.log_pow]
  have hdist : regularDistribution volume (fun x => Real.log (‖g x ^ a‖ ^ 2)) hLa =
      (a : ℝ) • regularDistribution volume (fun x => Real.log (‖g x‖ ^ 2)) hL := by
    rw [regularDistribution_congr_ae_on hLa hLC (Eventually.of_forall hlog),
      regularDistribution_const_mul (a : ℝ) hL hLC]
  refine ⟨hga, hga0, ?_⟩
  calc
    divisorCurrent hga hga0 =
        ddCLM (regularDistribution volume (fun x => Real.log (‖g x ^ a‖ ^ 2)) hLa) := by
      rw [ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]
    _ = ddCLM ((a : ℝ) •
        regularDistribution volume (fun x => Real.log (‖g x‖ ^ 2)) hL) :=
      congrArg ddCLM hdist
    _ = (a : ℝ) • divisorCurrent hg hg0 := by
      rw [map_smul, ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]

end SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentPower
