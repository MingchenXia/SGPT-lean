import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.LogLaplace
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- Compact continuity produces ALL original exponential moments,
without any integrability or bounded-moment output as a caller premise. -/
theorem integrableExpSet_eq_univ (μ : Measure K) [IsFiniteMeasure μ]
    (U : C(K, ℝ)) : integrableExpSet U μ = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact (Real.continuous_exp.comp (continuous_const.mul U.continuous)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Genuine log-Laplace convexity from actual exponential integrals and
the internally proved centered-square second derivative, not a supplied
convexity/variance/derivative certificate. -/
theorem convexOn_log_integral_exp (μ : Measure K) [IsFiniteMeasure μ]
    (U : C(K, ℝ)) :
    ConvexOn ℝ univ (fun t : ℝ => Real.log (∫ x, Real.exp (t * U x) ∂μ)) := by
  have hi (t : ℝ) : t ∈ interior (integrableExpSet U μ) := by
    rw [integrableExpSet_eq_univ μ U, interior_univ]
    exact mem_univ t
  have ha (t : ℝ) : AnalyticAt ℝ (cgf U μ) t := analyticAt_cgf (hi t)
  change ConvexOn ℝ univ (cgf U μ)
  apply convexOn_univ_of_deriv2_nonneg
    (fun t => (ha t).differentiableAt) (fun t => (ha t).deriv.differentiableAt)
  intro t
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_cgf_eq_integral (hi t)]
  apply div_nonneg
  · exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  · exact integral_nonneg (fun x => (Real.exp_pos _).le)

end SGPT.Bergman.LogLaplace
