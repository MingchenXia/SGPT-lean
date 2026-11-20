import SGPT.NPP.DivisorRadiusMinimum
import SGPT.Foundations.Analysis.Pending.ConvexExhaustion
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Actual quadratic/logarithmic penalties in the divisor-radius minimum

Complete blueprint: `blueprint/src/dnt-big-penalized-radius.tex`, written
before this file. The penalty's PSH property is proved from its actual
formula and convexity; it is not assumed in an output-shaped certificate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

variable {n : ℕ}

/-- The actual numerical penalty in logarithmic radius coordinates. -/
def logRadiusPenalty (K c : ℝ) (p : ComplexModel n × ℂ) : ℝ :=
  K * Real.exp (2 * p.2.re) - c * p.2.re

theorem plurisubharmonicOn_logRadiusPenalty {K : ℝ} (hK : 0 ≤ K) (c : ℝ) :
    PlurisubharmonicOn (fun p : ComplexModel n × ℂ => (logRadiusPenalty K c p : EReal))
      univ := by
  have hconv : ConvexOn ℝ (univ : Set (ComplexModel n × ℂ)) (logRadiusPenalty K c) := by
    refine ⟨convex_univ, fun p _ q _ u v hu hv huv => ?_⟩
    have he := convexOn_exp.2 (mem_univ (2 * p.2.re)) (mem_univ (2 * q.2.re)) hu hv huv
    simp only [smul_eq_mul] at he
    have hearg : u * (2 * p.2.re) + v * (2 * q.2.re) =
        2 * (u * p.2.re + v * q.2.re) := by ring
    rw [hearg] at he
    have hsecond : (u • p + v • q).2.re = u * p.2.re + v * q.2.re := by
      change (u • p.2 + v • q.2).re = u * p.2.re + v * q.2.re
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    simp only [logRadiusPenalty, hsecond, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left he hK]
  have hcont : Continuous (logRadiusPenalty K c (n := n)) := by
    unfold logRadiusPenalty
    fun_prop
  let e := stripModelEquiv n
  have heSMul (r : ℝ) (q : ComplexModel (n + 1)) : e (r • q) = r • e q :=
    (e.toContinuousLinearMap.restrictScalars ℝ).map_smul r q
  have hconvE : ConvexOn ℝ (univ : Set (ComplexModel (n + 1)))
      (fun q => logRadiusPenalty K c (e q)) := by
    refine ⟨convex_univ, fun p _ q _ u v hu hv huv => ?_⟩
    have hc := hconv.2 (mem_univ (e p)) (mem_univ (e q)) hu hv huv
    simpa only [map_add, heSMul] using hc
  have hpE := plurisubharmonicOn_of_convexOn isOpen_univ hconvE
    (hcont.comp e.continuous).continuousOn
  have hback := hpE.comp_continuousLinearMap
    (e.symm : (ComplexModel n × ℂ) →L[ℂ] ComplexModel (n + 1))
  convert hback using 1
  · funext p
    change (logRadiusPenalty K c p : EReal) = (logRadiusPenalty K c (e (e.symm p)) : EReal)
    rw [e.apply_symm_apply]
  · ext p
    simp only [mem_univ, mem_preimage]

/-- The exact penalty value at an actual positive radius. -/
theorem logRadiusPenalty_at_log (K c : ℝ) (z : ComplexModel n) {r : ℝ} (hr : 0 < r) :
    logRadiusPenalty K c (z, ((Real.log r) : ℂ)) = K * r ^ 2 - c * Real.log r := by
  simp only [logRadiusPenalty, Complex.ofReal_re]
  rw [show 2 * Real.log r = Real.log r + Real.log r by ring, Real.exp_add, Real.exp_log hr]
  ring

/-- The actual penalized minimum, with the genuine divisor-radius endpoint. -/
def penalizedDivisorRadiusMinimum (Ψ : ComplexModel n × ℂ → EReal)
    (s : ComplexModel n → ℂ) (δ a K c : ℝ) (z : ComplexModel n) : EReal :=
  ⨅ r : ↥(Ioo (0 : ℝ) (δ * ‖s z‖ ^ a)),
    Ψ (z, ((Real.log (r : ℝ)) : ℂ)) + ((K * (r : ℝ) ^ 2 - c * Real.log (r : ℝ) : ℝ) : EReal)

/-- The joint PSH input is the unpenalized actual family. The actual
quadratic/logarithmic penalty and its varying-radius minimum are produced. -/
theorem plurisubharmonicOn_penalizedDivisorRadiusMinimum {U : Set (ComplexModel n)}
    (hU : IsOpen U) {s : ComplexModel n → ℂ} (hs : DifferentiableOn ℂ s U)
    {δ : ℝ} (hδ : 0 < δ) (a : ℝ) {Ψ : ComplexModel n × ℂ → EReal}
    (hΨ : PlurisubharmonicOn Ψ (divisorRadiusDomain U s δ a))
    (hinv : ∀ z (τ σ : ℂ), τ.re = σ.re → Ψ (z, τ) = Ψ (z, σ))
    {K : ℝ} (hK : 0 ≤ K) (c : ℝ) :
    PlurisubharmonicOn (penalizedDivisorRadiusMinimum Ψ s δ a K c)
      {z | z ∈ U ∧ s z ≠ 0} := by
  let Φ : ComplexModel n × ℂ → EReal := fun p => Ψ p + (logRadiusPenalty K c p : EReal)
  have hΦ : PlurisubharmonicOn Φ (divisorRadiusDomain U s δ a) :=
    hΨ.add ((plurisubharmonicOn_logRadiusPenalty (n := n) hK c).mono (subset_univ _))
  have hinvΦ : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (z, τ) = Φ (z, σ) := by
    intro z τ σ hτσ
    simp only [Φ, logRadiusPenalty, hinv z τ σ hτσ, hτσ]
  have hp := plurisubharmonicOn_divisorRadiusMinimum hU hs hδ a hΦ hinvΦ
  have heq : divisorRadiusMinimum Φ s δ a = penalizedDivisorRadiusMinimum Ψ s δ a K c := by
    funext z
    apply iInf_congr
    intro r
    exact congrArg (fun v : ℝ => Ψ (z, ((Real.log (r : ℝ)) : ℂ)) + (v : EReal))
      (logRadiusPenalty_at_log K c z r.2.1)
  rw [heq] at hp
  exact hp

end SGPT.NPP.DNTBig
