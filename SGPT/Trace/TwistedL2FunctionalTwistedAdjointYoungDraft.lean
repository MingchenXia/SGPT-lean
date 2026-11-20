import SGPT.Trace.TwistedL2FunctionalTwistedYoungDraft
import SGPT.Trace.TwistedL2MainStatement
import SGPT.Foundations.Analysis.Pending.HormanderAPriori
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Foundations.Analysis.Pending.LeviWirtinger

/-!
# Actual local adjoint under the logarithmic twist

Pointwise support for the twisted L² argument. It derives the pointwise change of the actual
`chartTheta` adjoint when the actual local weight is replaced by `p − log a`,
then applies the independent exact Young square. No global BKN estimate or
functional inequality is an input.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2.FunctionalTwistedAdjointYoungDraft

open Set Filter MeasureTheory Bundle Complex
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
open SGPT.Trace.TwistedL2.FunctionalTwistedYoungDraft

variable {n : ℕ}

/-- The actual scalar ∂a contraction with the actual chart vector. -/
def chartTwistDerivative (a : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  ∑ j, dDir (coordVec j) (fun w => (a w : ℂ)) z * h z j

/-- The Wirtinger derivative of log a uses the actual real derivative of a. -/
theorem dDir_ofReal_log {a : ComplexModel n → ℝ} {z : ComplexModel n}
    (ha : DifferentiableAt ℝ a z) (ha0 : 0 < a z) (v : ComplexModel n) :
    dDir v (fun w => (Real.log (a w) : ℂ)) z =
      ((a z)⁻¹ : ℂ) * dDir v (fun w => (a w : ℂ)) z := by
  have hlog := ha.hasFDerivAt.log ha0.ne'
  have hlogd : DifferentiableAt ℝ (fun w => Real.log (a w)) z := hlog.differentiableAt
  have hv := fderiv_ofReal_comp_apply hlogd v
  have hi := fderiv_ofReal_comp_apply hlogd (Complex.I • v)
  have hav := fderiv_ofReal_comp_apply ha v
  have hai := fderiv_ofReal_comp_apply ha (Complex.I • v)
  unfold dDir
  rw [hv, hi, hav, hai, hlog.fderiv]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- The coordinate sum is the genuine (1,0) derivative in the actual
chart-vector direction. -/
theorem chartTwistDerivative_eq_dDir (a : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    chartTwistDerivative a h z = dDir (h z) (fun w => (a w : ℂ)) z := by
  have hv : (∑ j : Fin n, h z j • coordVec j : ComplexModel n) = h z := by
    ext i
    simp [coordVec, Pi.single_apply]
  calc
    _ = ∑ j : Fin n, h z j * dDir (coordVec j) (fun w => (a w : ℂ)) z := by
      unfold chartTwistDerivative
      refine Finset.sum_congr rfl fun j hj => ?_
      ring
    _ = dDir (∑ j : Fin n, h z j • coordVec j) (fun w => (a w : ℂ)) z := by
      simpa only using (dDir_sum_dir Finset.univ (fun j => h z j) coordVec
        (fun w => (a w : ℂ)) z).symm
    _ = _ := by rw [hv]

/-- The squared norm of that actual contraction is exactly `holDerivSq`,
including the normalization factor 1/4 used by twisted curvature. -/
theorem normSq_chartTwistDerivative (a : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (ha : DifferentiableAt ℝ a z) :
    ‖chartTwistDerivative a h z‖ ^ 2 = holDerivSq a z (h z) := by
  rw [chartTwistDerivative_eq_dDir]
  have heq : dDir (h z) (fun w => (a w : ℂ)) z = delC a z (h z) := by
    unfold dDir delC
    rw [fderiv_ofReal_comp_apply ha, fderiv_ofReal_comp_apply ha]
  rw [heq, Complex.sq_norm, normSq_delC]
  rfl

/-- Actual local adjoints before and after the logarithmic twist; the sign is
fixed by the repository's `chartTheta = −Σ δ`. -/
theorem chartTheta_sub_log (p a : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (hp : DifferentiableAt ℝ p z) (ha : DifferentiableAt ℝ a z) (ha0 : 0 < a z) :
    chartTheta (fun w => p w - Real.log (a w)) h z =
      chartTheta p h z - ((a z)⁻¹ : ℂ) * chartTwistDerivative a h z := by
  have hlog : DifferentiableAt ℝ (fun w => Real.log (a w)) z :=
    (ha.hasFDerivAt.log ha0.ne').differentiableAt
  unfold chartTheta chartTwistDerivative
  simp_rw [deltaDir_sub_weight hp hlog, dDir_ofReal_log ha ha0]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Actual chart adjoint after changing the weight satisfies the necessary
pointwise Young bound, with exactly the b⁻¹ error used by twisted curvature. -/
theorem chartTheta_sub_log_young (p a b : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (hp : DifferentiableAt ℝ p z) (ha : DifferentiableAt ℝ a z)
    (ha0 : 0 < a z) (hb0 : 0 < b z) :
    a z * ‖chartTheta (fun w => p w - Real.log (a w)) h z‖ ^ 2 ≤
      (a z + b z) * ‖chartTheta p h z‖ ^ 2 +
        ((a z)⁻¹ + (b z)⁻¹) * ‖chartTwistDerivative a h z‖ ^ 2 := by
  rw [chartTheta_sub_log p a h hp ha ha0]
  simpa only [Complex.ofReal_inv] using
    twistedYoung_le (a z) (b z) ha0 hb0 (chartTheta p h z) (chartTwistDerivative a h z)

/-- The pointwise estimate with the actual twisted-curvature derivative term
and its correct normalization. -/
theorem chartTheta_sub_log_young_curvature (p a b : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) {z : ComplexModel n}
    (hp : DifferentiableAt ℝ p z) (ha : DifferentiableAt ℝ a z)
    (ha0 : 0 < a z) (hb0 : 0 < b z) :
    a z * ‖chartTheta (fun w => p w - Real.log (a w)) h z‖ ^ 2 ≤
      (a z + b z) * ‖chartTheta p h z‖ ^ 2 +
        ((a z)⁻¹ + (b z)⁻¹) * holDerivSq a z (h z) := by
  rw [← normSq_chartTwistDerivative a h ha]
  exact chartTheta_sub_log_young p a b h hp ha ha0 hb0

end SGPT.Trace.TwistedL2.FunctionalTwistedAdjointYoungDraft
