import SGPT.Trace.OptimalProductNormalResidue

/-!
# Exact original parameter mass for the actual normalized normal tau/rho

Ordinary PARAMETER Lebesgue is retained explicitly. Its mass is pi*rho^2;
no implicit product/model or native Hodge normalization is silently changed.
Blueprint: work/sgpt-resume-20261114/bert-e2-scaled-residue/blueprint/bert-e2-scaled-residue.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalScaledNormalResidue
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalNormalResidueKernel
open SGPT.Trace.OptimalProductNormalResidue

theorem residueKernel_original_scaled_normal {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (τ : ℂ) :
    residueKernel ε (τ / (ρ : ℂ)) = ρ ^ 2 * residueKernel (ε * ρ ^ 2) τ := by
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ.ne'
  have hden : ε * ρ ^ 2 + ‖τ‖ ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (mul_pos hε (sq_pos_of_pos hρ)) (sq_nonneg _)).ne'
  unfold residueKernel normalKernel
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_pow]
  field_simp [hρ2, hden]

theorem integral_original_scaled_normal {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    (∫ τ : ℂ, residueKernel ε (τ / (ρ : ℂ))) = Real.pi * ρ ^ 2 := by
  simp_rw [residueKernel_original_scaled_normal hρ hε]
  rw [integral_const_mul, integral_residueKernel (mul_pos hε (sq_pos_of_pos hρ)), mul_comm]

theorem integrable_original_scaled_product_normal {d : ℕ} {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) {χ : ComplexModel d × ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun q : ComplexModel d × ℂ => residueKernel ε (q.2 / (ρ : ℂ)) * χ q)
      ((volume : Measure (ComplexModel d)).prod (volume : Measure ℂ)) := by
  have h := (integrable_product_normal_kernel (mul_pos hε (sq_pos_of_pos hρ)) hχ hχc).const_mul (ρ ^ 2)
  convert h using 1
  funext q
  rw [residueKernel_original_scaled_normal hρ hε]
  ring

theorem tendsto_integral_original_scaled_product_normal {d : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) {χ : ComplexModel d × ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun ε : ℝ => ∫ q : ComplexModel d × ℂ, residueKernel ε (q.2 / (ρ : ℂ)) * χ q
        ∂(volume : Measure (ComplexModel d)).prod (volume : Measure ℂ))
      (𝓝[>] 0) (𝓝 (Real.pi * ρ ^ 2 * ∫ u : ComplexModel d, χ (u, 0))) := by
  have hscale : Tendsto (fun ε : ℝ => ε * ρ ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h0 : Tendsto (fun ε : ℝ => ε * ρ ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa only [id_eq, zero_mul] using ((continuous_id.mul_const (ρ ^ 2)).tendsto (0 : ℝ))
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hε (sq_pos_of_pos hρ)
  have hlim := ((tendsto_integral_product_normal_kernel hχ hχc).comp hscale).const_mul (ρ ^ 2)
  have heq : ρ ^ 2 * (Real.pi * ∫ u : ComplexModel d, χ (u, 0)) =
      Real.pi * ρ ^ 2 * ∫ u : ComplexModel d, χ (u, 0) := by ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply]
  rw [← integral_const_mul]
  congr 1
  funext q
  rw [residueKernel_original_scaled_normal hρ hε]
  ring

end SGPT.Trace.OptimalScaledNormalResidue
