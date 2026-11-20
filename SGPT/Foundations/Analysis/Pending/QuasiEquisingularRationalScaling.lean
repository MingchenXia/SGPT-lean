import SGPT.Foundations.Analysis.Pending.QuasiEquisingularTwoPotentialMaximum
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Actual positive rational scaling of full QEA data -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation

noncomputable section


/-- The original holomorphic family and the actually scaled bounded
remainder give a rational analytic presentation at every pole as well. -/
theorem hasAnalyticSingularityTypeAt_pos_rat_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {x : E} (hu : HasAnalyticSingularityTypeAt u x)
    {r : ℚ} (hr : 0 < r) :
    HasAnalyticSingularityTypeAt (fun y => ((r : ℝ) : EReal) * u y) x := by
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hu
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  refine ⟨r * c, N, f, ?_, hf, (fun y => (r : ℝ) * b y), ?_, ?_⟩
  · simpa only [Rat.cast_mul] using mul_pos hrR hc
  · obtain ⟨C, hC, hbC⟩ := hb
    refine ⟨(r : ℝ) * C, mul_nonneg hrR.le hC, ?_⟩
    filter_upwards [hbC] with y hy
    rw [abs_mul, abs_of_pos hrR]
    exact mul_le_mul_of_nonneg_left hy hrR.le
  · filter_upwards [heq] with y hy
    rw [hy, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hrR.le)
      (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, Rat.cast_mul]


/-- All actual full-QEA fields survive rational positive scaling; the
strict multiplier clauses are transported by exact weighted densities. -/
theorem isQuasiEquisingularApproximation_pos_rat_smul
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε U)
    {r : ℚ} (hr : 0 < r) :
    IsQuasiEquisingularApproximation omega ((r : ℝ) • θ)
      (fun x => ((r : ℝ) : EReal) * u x) (fun j => (r : ℝ) * ε j)
      (fun j x => ((r : ℝ) : EReal) * U j x) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have herror : NonnegativeDecreasesToZero (fun j => (r : ℝ) * ε j) := by
    refine ⟨fun j => mul_nonneg hrR.le (hu.error_nonneg j),
      fun i j hij => mul_le_mul_of_nonneg_left (hu.error_antitone hij) hrR.le, ?_⟩
    simpa only [mul_zero] using hu.error_tendsto.const_mul (r : ℝ)
  refine ⟨RestrictedApproximantComparison.isThetaPshPotential_smul hu.target hrR,
    herror, ?_, ?_, ?_, ?_⟩
  · intro j
    have hform : (r : ℝ) • (θ + ε j • omega.form) =
        (r : ℝ) • θ + ((r : ℝ) * ε j) • omega.form := by module
    simpa only [hform] using
      RestrictedApproximantComparison.isThetaPshPotential_smul (hu.term j) hrR
  · intro j e z hz
    exact hasAnalyticSingularityTypeAt_pos_rat_smul
      (hu.term_hasAnalyticSingularityType j e z hz) hr
  · refine ⟨fun x i j hij => mul_le_mul_of_nonneg_left (hu.term_antitone x hij)
      (EReal.coe_nonneg.mpr hrR.le), fun x => ?_⟩
    exact EReal.Tendsto.const_mul (hu.term_tendsto x)
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  · intro c d hc hcd
    have hd : 0 < d := hc.trans hcd
    filter_upwards [hu.eventually_multiplierIdealIncluded (mul_pos hc hrR)
      (mul_lt_mul_of_pos_right hcd hrR)] with j hj
    intro e z hz f hf hi
    let _ : MeasurableSpace (ComplexModel n) := borel _
    let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    have hiU : MultiplierIntegrableAt (chartFunction (U j) e) (d * (r : ℝ)) f z volume :=
      (PositiveCurrentTraceMultiplier.multiplierIntegrableAt_coe_mul_iff hd hrR).mp hi
    have hiu := hj e z hz f hf hiU
    exact (PositiveCurrentTraceMultiplier.multiplierIntegrableAt_coe_mul_iff hc hrR).mpr hiu

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
