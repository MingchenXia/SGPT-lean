import SGPT.PSH.BookDeepDomination

/-!
The literal quadratic is a bounded psh solution on the
centered ball with zero sphere data and its actual Bedford--Taylor measure is
an explicit positive constant times Lebesgue measure.
This does not give a solution for variable or singular density.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Envelopes.DinewDirichlet

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.PSH.BookDeepDomination
open scoped ENNReal

variable {n : ℕ}

/-- The actual ball domain, without a substitute carrier. -/
def centeredBall (n : ℕ) (r : ℝ) : Opens (ComplexModel n) :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

/-- Zero-boundary quadratic, using the source's Bedford--Taylor normalization. -/
def quadraticDirichlet (c r : ℝ) (z : ComplexModel n) : ℝ :=
  c * ‖z‖ ^ 2 + (-(c * r ^ 2))

/-- It is locally bounded and psh for any positive coefficient. -/
theorem quadraticDirichlet_isLocallyBoundedPshOn {c r : ℝ} (hc : 0 < c) :
    IsLocallyBoundedPshOn (centeredBall n r) (quadraticDirichlet c r) := by
  exact IsLocallyBoundedPshOn.add_const
    (isLocallyBoundedPshOn_mul_normSq (centeredBall n r) hc) (-(c * r ^ 2))

/-- Its values have a uniform finite bound on the whole actual ball. -/
theorem quadraticDirichlet_bounds {c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    {z : ComplexModel n} (hz : z ∈ (centeredBall n r : Set (ComplexModel n))) :
    -(c * r ^ 2) ≤ quadraticDirichlet c r z ∧ quadraticDirichlet c r z ≤ 0 := by
  have hz' : ‖z‖ < r := by
    change z ∈ Metric.ball (0 : ComplexModel n) r at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hsq : ‖z‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg z]
  have hmul : c * ‖z‖ ^ 2 ≤ c * r ^ 2 := mul_le_mul_of_nonneg_left hsq hc
  have hnonneg : 0 ≤ c * ‖z‖ ^ 2 := mul_nonneg hc (sq_nonneg _)
  simp only [quadraticDirichlet]
  constructor <;> linarith

/-- The values on the actual radius-r sphere are literally zero. -/
theorem quadraticDirichlet_eq_zero_on_sphere {c r : ℝ} {z : ComplexModel n}
    (hz : z ∈ Metric.sphere (0 : ComplexModel n) r) : quadraticDirichlet c r z = 0 := by
  have hz' : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  simp only [quadraticDirichlet, hz']
  ring

/-- The exact diagonal Bedford--Taylor measure is produced, not assumed. -/
theorem quadraticDirichlet_isBTLimit {c r : ℝ} (hc : 0 ≤ c) :
    IsBTLimit (centeredBall n r) (fun _ => quadraticDirichlet c r)
      ((ENNReal.ofReal c ^ n * ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n)) •
        volume.restrict (centeredBall n r : Set (ComplexModel n))) := by
  have h := (isBTLimit_mul_normSq (centeredBall n r) hc).add_const_diag (-(c * r ^ 2))
  change IsBTLimit (centeredBall n r)
    (fun _ z => c * ‖z‖ ^ 2 + (-(c * r ^ 2))) _
  exact h

end SGPT.Envelopes.DinewDirichlet
