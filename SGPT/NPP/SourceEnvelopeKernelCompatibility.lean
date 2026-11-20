import SGPT.NPP.SourceEnvelopeRadiusMinimum
import SGPT.NPP.ContactRadialSmoothing

/-!
# One actual explicit kernel for source smoothing and obstacle comparison

Complete blueprint: `blueprint/src/dnt-big-source-kernel.tex`, written first.
Actual Haar dilation identifies the explicit mean-comparison kernels with the
scaled actual radial kernel used by the same source-envelope convolution.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ}

/-- Exact dilation of the actual normalized bump, with arbitrary positive
radius, obtained from the actual raw bump and Haar scaling. -/
theorem explicitRadialKernel_radius_dilation {r : ℝ} (hr : 0 < r) (x : ComplexModel n) :
    explicitRadialKernel r hr 0 x =
      (r ^ Module.finrank ℝ (ComplexModel n))⁻¹ * explicitRadialKernel 1 one_pos 0 (r⁻¹ • x) := by
  have hraw (y : ComplexModel n) : explicitRadialRaw r hr 0 y =
      explicitRadialRaw 1 one_pos 0 (r⁻¹ • y) := by
    unfold explicitRadialRaw
    congr 1
    rw [smul_smul]
    congr 1
    simp only [shrinkingBump]
    field_simp
  have hint : (∫ y : ComplexModel n, explicitRadialRaw r hr 0 y) =
      ((r⁻¹) ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
        ∫ y : ComplexModel n, explicitRadialRaw 1 one_pos 0 y := by
    simp_rw [hraw]
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg volume
        (explicitRadialRaw (n := n) 1 one_pos 0) r⁻¹ (hR := inv_nonneg.mpr hr.le))
  rw [explicitRadialKernel, explicitRadialKernel, hraw, hint, inv_pow, inv_inv]
  field_simp

/-- The actual explicit unit kernel satisfies all actual radial-kernel
properties, rather than being assigned an abstract smoothing role. -/
theorem isRadialKernel_explicitUnitKernel :
    IsRadialKernel (explicitRadialKernel (n := n) 1 one_pos 0) := by
  refine ⟨explicitRadialKernel_contDiff 1 one_pos 0,
    explicitRadialKernel_nonneg 1 one_pos 0,
    explicitRadialKernel_integral_one 1 one_pos 0, ?_, ?_⟩
  · rw [explicitRadialKernel_tsupport]
    simp only [Nat.cast_zero, zero_add, div_one, subset_refl]
  · intro a ha x
    exact explicitRadialKernel_unitary 1 one_pos 0 a ha x

/-- Literal identity between the actual scaled radial kernel and the actual
explicit kernel appearing in the weak-obstacle-Hessian mean estimate. -/
theorem scaledKernel_explicitUnitKernel {r : ℝ} (hr : 0 < r) (x : ComplexModel n) :
    scaledKernel (explicitRadialKernel 1 one_pos 0) r x = explicitRadialKernel r hr 0 x :=
  (explicitRadialKernel_radius_dilation hr x).symm

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The same actual source smoothing is the same corrected explicit mean. -/
theorem sourceChartRadialSmoothing_explicitUnitKernel
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (ψ : ComplexModel n → ℝ)
    {r : ℝ} (hr : 0 < r) (y : ComplexModel n) :
    sourceChartRadialSmoothing (explicitRadialKernel 1 one_pos 0) θ g e ψ r y + ψ y =
      ∫ x, (sourceEnvelopeChartPotential θ g e ψ x).toReal *
        explicitRadialKernel r hr 0 (x - y) := by
  simp only [sourceChartRadialSmoothing, sub_add_cancel]
  rw [radialRegularization_eq_translationPairing isRadialKernel_explicitUnitKernel]
  unfold translationPairing
  simp_rw [scaledKernel_explicitUnitKernel hr]

end SGPT.NPP.DNTBig
