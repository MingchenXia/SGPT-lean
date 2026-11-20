import SGPT.PSH.HermitianFrozenCoefficients
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# Actual two-sided frozen corrections on coordinate balls

The upper correction makes every background-relative PSH datum ordinary
PSH. Subtracting the lower correction from an ordinary PSH replacement
produces the local candidate for boundary pasting. The two corrections
agree on the actual boundary and differ by at most the cubic radius error
inside. Their common radius and coefficient are chosen before the centers,
radii and potentials.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorCollar
open scoped Topology ContDiff

variable {n : ℕ}

/-- The normalized Euclidean quadratic centered on the actual ball. -/
def centeredFlatQuadratic (a z : ComplexModel n) : ℝ := Real.pi * ‖z - a‖ ^ 2

theorem contDiff_centeredFlatQuadratic (a : ComplexModel n) :
    ContDiff ℝ ∞ (centeredFlatQuadratic a) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem smoothDDC_centeredFlatQuadratic (a z : ComplexModel n) :
    smoothDDC (centeredFlatQuadratic a) z = kahlerForm n := by
  have hs := smoothDDC_smul (h := fun y : ComplexModel n => ‖y - a‖ ^ 2) isOpen_univ
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
    Real.pi (mem_univ z)
  have he : smoothDDC (centeredFlatQuadratic a) z =
      Real.pi • smoothDDC (fun y => ‖y - a‖ ^ 2) z := by
    change smoothDDC (fun y => Real.pi * ‖y - a‖ ^ 2) z = _
    simpa only [smul_eq_mul] using hs
  rw [he, smoothDDC_norm_sub_sq, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]

/-- The correction dominating the varying background on the frozen ball. -/
def frozenUpperCorrection (h : ComplexModel n → ℝ) (a : ComplexModel n) (δ : ℝ)
    (z : ComplexModel n) : ℝ := h z + δ * centeredFlatQuadratic a z

/-- The dominated correction used to paste the ordinary replacement. -/
def frozenLowerCorrection (h : ComplexModel n → ℝ) (a : ComplexModel n) (δ r : ℝ)
    (z : ComplexModel n) : ℝ := h z - δ * centeredFlatQuadratic a z + 2 * Real.pi * δ * r ^ 2

theorem contDiff_frozenUpperCorrection {h : ComplexModel n → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ComplexModel n) (δ : ℝ) : ContDiff ℝ ∞ (frozenUpperCorrection h a δ) :=
  hh.add (contDiff_const.mul (contDiff_centeredFlatQuadratic a))

theorem contDiff_frozenLowerCorrection {h : ComplexModel n → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ComplexModel n) (δ r : ℝ) : ContDiff ℝ ∞ (frozenLowerCorrection h a δ r) :=
  (hh.sub (contDiff_const.mul (contDiff_centeredFlatQuadratic a))).add contDiff_const

private theorem smoothDDC_upper {h : ComplexModel n → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ComplexModel n) (δ : ℝ) (z : ComplexModel n) :
    smoothDDC (frozenUpperCorrection h a δ) z = smoothDDC h z + δ • kahlerForm n := by
  change smoothDDC (fun y => h y + δ * centeredFlatQuadratic a y) z = _
  rw [smoothDDC_add isOpen_univ hh.contDiffOn
    (contDiff_const.mul (contDiff_centeredFlatQuadratic a)).contDiffOn (mem_univ z)]
  have hs := smoothDDC_smul isOpen_univ (contDiff_centeredFlatQuadratic a).contDiffOn δ (mem_univ z)
  simpa only [smul_eq_mul, smoothDDC_centeredFlatQuadratic] using congrArg (fun T => smoothDDC h z + T) hs

private theorem smoothDDC_lower {h : ComplexModel n → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ComplexModel n) (δ r : ℝ) (z : ComplexModel n) :
    smoothDDC (frozenLowerCorrection h a δ r) z = smoothDDC h z - δ • kahlerForm n := by
  change smoothDDC (fun y => h y - δ * centeredFlatQuadratic a y + 2 * Real.pi * δ * r ^ 2) z = _
  rw [smoothDDC_add isOpen_univ
    (hh.sub (contDiff_const.mul (contDiff_centeredFlatQuadratic a))).contDiffOn
    contDiffOn_const (mem_univ z), GlobalPotentialTransforms.smoothDDC_const, add_zero,
    PositiveClasses.smoothDDC_sub isOpen_univ hh.contDiffOn
      (contDiff_const.mul (contDiff_centeredFlatQuadratic a)).contDiffOn (mem_univ z)]
  have hs := smoothDDC_smul isOpen_univ (contDiff_centeredFlatQuadratic a).contDiffOn δ (mem_univ z)
  simpa only [smul_eq_mul, smoothDDC_centeredFlatQuadratic] using congrArg (fun T => smoothDDC h z - T) hs

/-- A single radius and coefficient give actual global smooth frozen
corrections for every center and every smaller positive radius. The
Hessian inequalities and cubic error are proved for the actual formulas. -/
theorem exists_uniform_frozen_corrections
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (b : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hb : ContDiffOn ℝ ∞ b U)
    (hb₁ : ∀ z ∈ U, IsOneOne (b z)) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ closedBall z₀ (4 * R) ⊆ U ∧
      ∀ a ∈ closedBall z₀ R, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ h : ComplexModel n → ℝ, ContDiff ℝ ∞ h ∧ (∀ z, smoothDDC h z = b a) ∧
          (∀ z ∈ closedBall a (2 * r), ∀ v : ComplexModel n,
            smoothDDC (frozenLowerCorrection h a (C * r) r) z ![v, Complex.I • v] ≤
              b z ![v, Complex.I • v] ∧
            b z ![v, Complex.I • v] ≤
              smoothDDC (frozenUpperCorrection h a (C * r)) z ![v, Complex.I • v]) ∧
          (∀ z ∈ closedBall a r,
            0 ≤ frozenLowerCorrection h a (C * r) r z - frozenUpperCorrection h a (C * r) z ∧
            frozenLowerCorrection h a (C * r) r z - frozenUpperCorrection h a (C * r) z ≤
              2 * Real.pi * C * r ^ 3) ∧
          ∀ z ∈ sphere a r,
            frozenLowerCorrection h a (C * r) r z = frozenUpperCorrection h a (C * r) z := by
  obtain ⟨R, C, hR, hC, hbuffer, herr⟩ :=
    HermitianFrozenCoefficients.exists_uniform_local_line_error hU b hb hz₀
  refine ⟨R, C, hR, hC, hbuffer, ?_⟩
  intro a ha r hr hrR
  have haU : a ∈ U := hbuffer (closedBall_subset_closedBall (by linarith) ha)
  obtain ⟨h, hh, hddc⟩ := HermitianFrozenCoefficients.exists_global_constant_potential (b a) (hb₁ a haU)
  refine ⟨h, hh, hddc, ?_, ?_, ?_⟩
  · intro z hz v
    have he := herr a ha r hr.le hrR z hz v
    rw [abs_le] at he
    rw [smoothDDC_lower hh, smoothDDC_upper hh, hddc]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, kahlerForm_apply_I]
    constructor <;> linarith
  · intro z hz
    have hdist : ‖z - a‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hsq : ‖z - a‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (z - a)]
    have hCr : 0 ≤ C * r := mul_nonneg hC.le hr.le
    dsimp [frozenLowerCorrection, frozenUpperCorrection, centeredFlatQuadratic]
    constructor
    · nlinarith [mul_nonneg hCr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq))]
    · nlinarith [mul_nonneg hCr (mul_nonneg Real.pi_pos.le (sq_nonneg ‖z - a‖))]
  · intro z hz
    have hdist : ‖z - a‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
    simp only [frozenLowerCorrection, frozenUpperCorrection, centeredFlatQuadratic, hdist]
    ring

end SGPT.PSH.HermitianBalayage
