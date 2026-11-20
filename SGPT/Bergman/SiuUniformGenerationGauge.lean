import SGPT.Bergman.SiuUniformGenerationDbar
import SGPT.Bergman.SiuUniformGenerationSmoothFrame

/-!
# The actual logarithmic scalar `∂̄` form used to make a frame holomorphic

For a smooth nonzero scalar coefficient `f`, the form `f⁻¹ ∂̄f` is smooth,
closed, and unchanged on multiplying by a holomorphic nonzero transition.
These are proved from the scalar functions themselves, with no assumed
curvature, flatness, or desired holomorphic frame.

Blueprint: `siu-uniform-generation.tex`, node `siu-uniform:logarithmic-dbar`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric Complex
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ}

/-- Smoothness of each actual coordinate Wirtinger derivative on an open set. -/
theorem contDiffOn_dbarDir_of_isOpen {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f U) (v : ComplexModel n) :
    ContDiffOn ℝ ∞ (dbarDir v f) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact ((hD.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const 2

/-- The scalar logarithmic `(0,1)`-form, with literal coefficient derivatives. -/
def logarithmicDbar (f : ComplexModel n → ℂ) (j : Fin n) (z : ComplexModel n) : ℂ :=
  (f z)⁻¹ * dbarDir (coordVec j) f z

theorem contDiffOn_logarithmicDbar {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hf0 : ∀ z ∈ U, f z ≠ 0)
    (j : Fin n) : ContDiffOn ℝ ∞ (logarithmicDbar f j) U :=
  (hf.inv hf0).mul (contDiffOn_dbarDir_of_isOpen hU hf (coordVec j))

/-- Closedness follows by differentiating `f α_j = ∂̄_j f`; no branch of a
logarithm or pre-existing primitive is assumed. -/
theorem isDbarClosedOn_logarithmicDbar {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    IsDbarClosedOn (logarithmicDbar f) U := by
  intro i j z hz
  have hfd : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hαd (k : Fin n) : DifferentiableAt ℝ (logarithmicDbar f k) z :=
    ((contDiffOn_logarithmicDbar hU hf hf0 k).contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by simp)
  have hid (k : Fin n) : (fun y => f y * logarithmicDbar f k y)
      =ᶠ[𝓝 z] dbarDir (coordVec k) f := by
    filter_upwards [hU.mem_nhds hz] with y hy
    dsimp [logarithmicDbar]
    rw [← mul_assoc, mul_inv_cancel₀ (hf0 y hy), one_mul]
  have hi := dbarDir_congr (v := coordVec i) (hid j)
  have hj := dbarDir_congr (v := coordVec j) (hid i)
  rw [dbarDir_mul hfd (hαd j)] at hi
  rw [dbarDir_mul hfd (hαd i)] at hj
  have hcomm := dbarDir_dbarDir_comm (u := coordVec i) (v := coordVec j)
    ((hf.contDiffAt (hU.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hcross : dbarDir (coordVec i) f z * logarithmicDbar f j z =
      dbarDir (coordVec j) f z * logarithmicDbar f i z := by
    dsimp [logarithmicDbar]
    ring
  have hmul : f z * dbarDir (coordVec i) (logarithmicDbar f j) z =
      f z * dbarDir (coordVec j) (logarithmicDbar f i) z := by
    linear_combination hi - hj + hcomm - hcross
  exact mul_left_cancel₀ (hf0 z hz) hmul

/-- Actual holomorphic transition factors cancel from the logarithmic form. -/
theorem logarithmicDbar_eq_of_holomorphic_factor
    {f g h : ComplexModel n → ℂ} {z : ComplexModel n}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℂ h z)
    (hfg : f =ᶠ[𝓝 z] fun y => h y * g y) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0)
    (j : Fin n) : logarithmicDbar f j z = logarithmicDbar g j z := by
  have hpoint : f z = h z * g z := hfg.self_of_nhds
  have hh0 : h z ≠ 0 := fun h0 => hf0 (by rw [hpoint, h0, zero_mul])
  have hder := dbarDir_congr (v := coordVec j) hfg
  rw [dbarDir_mul (hh.restrictScalars ℝ) hg,
    dbarDir_eq_zero_of_differentiableAt hh, zero_mul, zero_add] at hder
  dsimp [logarithmicDbar]
  rw [hder, hpoint]
  field_simp

end SGPT.Bergman.SiuUniformGeneration
