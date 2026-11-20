import SGPT.Foundations.Analysis.Pending.SNCHolomorphicTestMultiplierCriterion
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false

/-! # Actual weighted integrability and a genuine coordinate line unit -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.CoordinateLineUnitMultiplierBound

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

private theorem analyticAt_of_near_differentiable {n : ℕ} {H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z) :
    AnalyticAt ℂ H 0 := by
  obtain ⟨U, hsub, hU, h0⟩ := _root_.mem_nhds_iff.mp hH
  exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU
    (fun z hz => (hsub hz).differentiableWithinAt) h0

private theorem coordinate_order_le_line_unit {n : ℕ} (p : Fin n)
    (a : Fin n → ℕ) {F H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ i : Fin n, z i ^ a i)
    {N : ℕ} {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hline : (fun t : ℂ => F (t • EuclideanSpace.single p (1 : ℂ))) =ᶠ[𝓝 0]
      (fun t => t ^ N * u t)) : a p ≤ N := by
  classical
  let ep : ComplexModel n := EuclideanSpace.single p (1 : ℂ)
  let line : ℂ → ComplexModel n := fun t => t • ep
  have hcont : Continuous line := continuous_id.smul continuous_const
  have hT : Tendsto line (𝓝 0) (𝓝 0) := by
    simpa only [line, zero_smul] using hcont.continuousAt.tendsto (x := (0 : ℂ))
  have hla : AnalyticAt ℂ line 0 := analyticAt_id.smul analyticAt_const
  have hHa : AnalyticAt ℂ H (line 0) := by
    simpa only [line, zero_smul] using analyticAt_of_near_differentiable hH
  have hHla : AnalyticAt ℂ (fun t => H (line t)) 0 :=
    AnalyticAt.comp (g := H) (f := line) hHa hla
  have hprod : ∀ s : Finset (Fin n), AnalyticAt ℂ
      (fun t : ℂ => ∏ i ∈ s, (line t) i ^ a i) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (analyticAt_const (v := (1 : ℂ)))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      have hia : AnalyticAt ℂ (fun t : ℂ => (line t) i) 0 := by
        change AnalyticAt ℂ (fun t : ℂ => t * ep i) 0
        exact analyticAt_id.mul analyticAt_const
      exact (hia.pow (a i)).mul ih
  let R : ℂ → ℂ := fun t => H (line t) *
    ∏ i ∈ (Finset.univ : Finset (Fin n)).erase p, (line t) i ^ a i
  have hRa : AnalyticAt ℂ R 0 := hHla.mul (hprod _)
  have hfactor : ∀ᶠ t in 𝓝 (0 : ℂ), F (line t) = t ^ a p * R t := by
    filter_upwards [hT.eventually heq] with t ht
    rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hcoord : (line t) p = t := by simp [line, ep]
    rw [hcoord]
    dsimp only [R]
    ring
  have hFa : AnalyticAt ℂ (fun t => F (line t)) 0 :=
    ((analyticAt_id.pow N).mul hu).congr hline.symm
  have horder : analyticOrderAt (fun t => F (line t)) 0 = (N : ℕ∞) :=
    hFa.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hu0, by simpa only [Filter.EventuallyEq, line, ep, sub_zero, smul_eq_mul] using hline⟩
  have hlower : (a p : ℕ∞) ≤ analyticOrderAt (fun t => F (line t)) 0 :=
    (natCast_le_analyticOrderAt hFa).mpr ⟨R, hRa,
      by simpa only [sub_zero, smul_eq_mul] using hfactor⟩
  rw [horder, ENat.natCast_le_natCast] at hlower
  exact hlower

/-- The actual finite integral, literal coordinate upper bound and genuine line
unit force the strict threshold; coordinate orders are produced internally. -/
theorem threshold_of_integrability_and_line_unit {n : ℕ} (p : Fin n)
    {ψ : ComplexModel n → EReal} {F : ComplexModel n → ℂ} {c A : ℝ}
    (hA : 0 ≤ A) (hint : MultiplierIntegrableAt ψ c F 0 volume)
    (hupper : ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ψ z ≤ (A : EReal) * logNormSq (z p) + (C : EReal))
    {N : ℕ} {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hline : (fun t : ℂ => F (t • EuclideanSpace.single p (1 : ℂ))) =ᶠ[𝓝 0]
      (fun t => t ^ N * u t)) :
    c * A < (N : ℝ) + 1 := by
  classical
  by_cases hAz : A = 0
  · simp only [hAz, mul_zero]
    positivity
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let ep : ComplexModel n := EuclideanSpace.single p (1 : ℂ)
  have hlinec : Continuous (fun t : ℂ => t • ep) := continuous_id.smul continuous_const
  have hT : Tendsto (fun t : ℂ => t • ep) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using hlinec.continuousAt.tendsto (x := (0 : ℂ))
  have hlinea : AnalyticAt ℂ (fun t : ℂ => F (t • ep)) 0 :=
    ((analyticAt_id.pow N).mul hu).congr hline.symm
  have horder : analyticOrderAt (fun t : ℂ => F (t • ep)) 0 = (N : ℕ∞) :=
    hlinea.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hu0,
      by simpa only [Filter.EventuallyEq, ep, sub_zero, smul_eq_mul] using hline⟩
  have hne : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0 := by
    by_contra hn
    have hz : ∀ᶠ z in 𝓝 (0 : ComplexModel n), F z = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have ht : analyticOrderAt (fun t : ℂ => F (t • ep)) 0 = ⊤ :=
      analyticOrderAt_eq_top.mpr (hT.eventually hz)
    rw [horder] at ht
    exact ENat.natCast_ne_top N ht
  have hintcopy := hint
  obtain ⟨-, U, hU, h0, hhol, -⟩ := hintcopy
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact hhol.differentiableAt (hU.mem_nhds hz)
  obtain ⟨a, H, hH, -, heq, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
  have haN : a p ≤ N := coordinate_order_le_line_unit p a hH heq hu hu0 hline
  let χ : ComplexModel n → EReal := fun z => (A : EReal) * logNormSq (z p)
  have hχ : QuasiPlurisubharmonicAt χ (0 : ComplexModel n) := by
    have hp : PlurisubharmonicAt (fun z : ComplexModel n => logNormSq (z p)) 0 :=
      PlurisubharmonicAt.comp_continuousLinearMap (EuclideanSpace.proj (𝕜 := ℂ) p)
        (plurisubharmonicAt_logNormSq _)
    exact (hp.const_mul hApos).quasiPlurisubharmonicAt
  obtain ⟨C, hC⟩ := hupper
  have hintχ : MultiplierIntegrableAt χ c F 0 volume :=
    multiplierIntegrableAt_of_moreSingularAt hχ ⟨C, hC⟩ hint
  let b : Fin n → ℝ := fun i => if i = p then A else 0
  have hsum (z : ComplexModel n) :
      (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) =
        ((2 * A : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z p‖) := by
    rw [Finset.sum_eq_single p]
    · simp [b]
    · intro i _ hip
      simp [b, hip]
    · simp
  have hw : χ = (fun z : ComplexModel n =>
      (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
        ((0 : ℝ) : EReal)) := by
    funext z
    rw [hsum, EReal.coe_zero, add_zero]
    dsimp only [χ]
    by_cases hz : z p = 0
    · simp only [hz, logNormSq_zero, norm_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
      rw [EReal.coe_mul_bot_of_pos hApos, EReal.coe_mul_bot_of_pos (by linarith : 0 < 2 * A)]
    · rw [logNormSq_of_ne_zero hz, Real.log_pow,
        ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz)]
      rw [← EReal.coe_mul, ← EReal.coe_mul]
      congr 1
      ring
  rw [hw] at hintχ
  have hp := SNCHolomorphicTestMultiplierCriterion.thresholds_of_multiplier_integrable
    a b hH hnot heq (Eventually.of_forall fun _ => continuousAt_const) hintχ p
  have hp' : c * A < (a p : ℝ) + 1 := by simpa only [b, if_true] using hp
  have haNr : (a p : ℝ) ≤ N := by exact_mod_cast haN
  linarith

end
end SGPT.Foundations.Analysis.Pending.CoordinateLineUnitMultiplierBound
