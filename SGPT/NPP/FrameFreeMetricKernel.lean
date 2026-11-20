import SGPT.NPP.FrameFreeMetricJet
import SGPT.Foundations.Analysis.Pending.RadialPoissonCertificate
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Actual metric radial kernels and the same source mean without varying frames

Blueprint first: `dnt-big-frame-free-metric-kernel.tex`.
The literal physical-tangent integral has a manufactured positive denominator;
no choice of a varying normalizing frame enters its definition.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.RadialPoissonCertificate
open SGPT.Envelopes SGPT.Analysis.KahlerNormal
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ}

/-- The literal metric radial kernel in physical chart-tangent coordinates. -/
def metricRadialKernel
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z : ComplexModel n) (r : ℝ) (v : ComplexModel n) : ℝ :=
  explicitRadialKernelSqProfile (n := n) 1 one_pos 0
    (Real.pi * g z (r⁻¹ • v) (r⁻¹ • v))

/-- The literal actual polynomial mean in physical tangent coordinates.
Its denominator is proved positive whenever an actual normalizing frame exists. -/
def frameFreeMetricJetMean
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (f : ComplexModel n → ℝ) (z : ComplexModel n) (r : ℝ) : ℝ :=
  (∫ v, f (metricQuadraticJet g z v) * metricRadialKernel g z r v) /
    ∫ v, metricRadialKernel g z r v

/-- The actual metric and squared-radius profile give actual joint smoothness. -/
theorem contDiffOn_metricRadialKernel
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {U : Set (ComplexModel n)} (hg : ContDiffOn ℝ ∞ g U) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ComplexModel n × ComplexModel n =>
      metricRadialKernel g q.1 r q.2) (U ×ˢ univ) := by
  have hbase : ContDiffOn ℝ ∞ (fun q : ComplexModel n × ComplexModel n => g q.1)
      (U ×ˢ univ) := hg.comp contDiffOn_fst (fun q hq => hq.1)
  have hvec : ContDiffOn ℝ ∞ (fun q : ComplexModel n × ComplexModel n => r⁻¹ • q.2)
      (U ×ˢ univ) := contDiffOn_snd.const_smul _
  exact (explicitRadialKernelSqProfile_contDiff (n := n) 1 one_pos 0).comp_contDiffOn
    (((hbase.clm_apply hvec).clm_apply hvec).const_smul Real.pi)

/-- The actual real scaled frame, used only for this fixed-point change of variables. -/
def scaledNormalizingFrame (A : ComplexModel n ≃L[ℂ] ComplexModel n)
    (r : ℝ) (hr : r ≠ 0) : ComplexModel n ≃L[ℝ] ComplexModel n :=
  (LinearEquiv.smulOfNeZero ℝ (ComplexModel n) r hr).toContinuousLinearEquiv.trans
    (A.restrictScalars ℝ)

@[simp] theorem scaledNormalizingFrame_apply
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : r ≠ 0)
    (v : ComplexModel n) : scaledNormalizingFrame A r hr v = A (r • v) := rfl

/-- The literal metric radial kernel becomes the SAME explicit unit kernel
in any actually normalizing frame. -/
theorem metricRadialKernel_normalizing
    (α : ComplexModel n → CoordinateRealTwoForm n) (z : ComplexModel n)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : r ≠ 0)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) (v : ComplexModel n) :
    metricRadialKernel (fun x => TosC11c.twoFormMetric (α x)) z r (A (r • v)) =
      explicitRadialKernel 1 one_pos 0 v := by
  have hv : r⁻¹ • A (r • v) = A v := by
    change r⁻¹ • (A.restrictScalars ℝ) (r • v) = (A.restrictScalars ℝ) v
    rw [(A.restrictScalars ℝ).map_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [metricRadialKernel, hv, TosC11c.twoFormMetric_apply,
    ← A.map_smul Complex.I v, hA, flatForm_apply_I_smul_self]
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  exact (explicitRadialKernel_eq_sqProfile_norm_sq 1 one_pos 0 v).symm

/-- Actual real Haar change of variables for the original invertible linear map. -/
theorem integral_eq_abs_det_mul_integral_comp
    (T : ComplexModel n ≃L[ℝ] ComplexModel n) (f : ComplexModel n → ℝ) :
    (∫ v, f v) = |LinearMap.det T.toLinearEquiv.toLinearMap| * ∫ v, f (T v) := by
  have hdet : LinearMap.det T.toLinearEquiv.toLinearMap ≠ 0 := T.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ComplexModel n)) hdet
  have hcoe : (T.toLinearEquiv.toLinearMap : ComplexModel n → ComplexModel n) = T := by
    funext x
    rfl
  rw [hcoe] at hmap
  have hi := integral_map_equiv (μ := volume) T.toHomeomorph.toMeasurableEquiv f
  change (∫ v, f v ∂Measure.map T volume) = ∫ v, f (T v) at hi
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    abs_inv] at hi
  calc
    (∫ v, f v) = |LinearMap.det T.toLinearEquiv.toLinearMap| *
        (|LinearMap.det T.toLinearEquiv.toLinearMap|⁻¹ * ∫ v, f v) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_mul]
    _ = _ := congrArg (fun a => |LinearMap.det T.toLinearEquiv.toLinearMap| * a) hi

/-- The actual metric kernel has its actual Jacobian mass, with no chosen density input. -/
theorem integral_metricRadialKernel_eq_abs_det
    (α : ComplexModel n → CoordinateRealTwoForm n) (z : ComplexModel n)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : r ≠ 0)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) :
    (∫ v, metricRadialKernel (fun x => TosC11c.twoFormMetric (α x)) z r v) =
      |LinearMap.det (scaledNormalizingFrame A r hr).toLinearEquiv.toLinearMap| := by
  rw [integral_eq_abs_det_mul_integral_comp (scaledNormalizingFrame A r hr)]
  simp_rw [scaledNormalizingFrame_apply, metricRadialKernel_normalizing α z A r hr hA]
  rw [explicitRadialKernel_integral_one, mul_one]

/-- Positivity of the actual denominator follows from its actual invertible Jacobian. -/
theorem integral_metricRadialKernel_pos
    (α : ComplexModel n → CoordinateRealTwoForm n) (z : ComplexModel n)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : r ≠ 0)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) :
    0 < ∫ v, metricRadialKernel (fun x => TosC11c.twoFormMetric (α x)) z r v := by
  rw [integral_metricRadialKernel_eq_abs_det α z A r hr hA]
  exact abs_pos.mpr (scaledNormalizingFrame A r hr).toLinearEquiv.isUnit_det'.ne_zero

/-- Literal equality of the actual physical-tangent mean and its actual
normal-frame integral, from the SAME actual kernel/Jacobian change of variables. -/
theorem frameFreeMetricJetMean_eq_normalizing_integral
    (α : ComplexModel n → CoordinateRealTwoForm n) (z : ComplexModel n)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : r ≠ 0)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) (f : ComplexModel n → ℝ) :
    frameFreeMetricJetMean (fun x => TosC11c.twoFormMetric (α x)) f z r =
      ∫ v, f (metricQuadraticJet (fun x => TosC11c.twoFormMetric (α x)) z (A (r • v))) *
        explicitRadialKernel 1 one_pos 0 v := by
  rw [frameFreeMetricJetMean, integral_eq_abs_det_mul_integral_comp (scaledNormalizingFrame A r hr),
    integral_metricRadialKernel_eq_abs_det α z A r hr hA]
  simp_rw [scaledNormalizingFrame_apply, metricRadialKernel_normalizing α z A r hr hA]
  exact mul_div_cancel_left₀ _ (abs_ne_zero.mpr (scaledNormalizingFrame A r hr).toLinearEquiv.isUnit_det'.ne_zero)

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The literal SAME original source-envelope mean is the actual frame-free
physical-tangent mean, with no varying normalizing frame in the definition. -/
theorem sourceQuadraticMetricJetMean_eq_frameFreeMetricJetMean
    (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ) (hr : 0 < r)
    (hA : ∀ p u, w.form.val.coeff e z ![A p, A u] = flatForm n ![p, u]) :
    sourceQuadraticMetricJetMean w θ g e z hz A r =
      frameFreeMetricJetMean (TosC11c.chartMetric w e)
        (fun v => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
          (e.val.symm v)).toReal) z r := by
  rw [sourceQuadraticMetricJetMean_eq_frameFreeIntegral w θ g e z hz A r hA]
  have H := (frameFreeMetricJetMean_eq_normalizing_integral (w.form.val.coeff e) z A r hr.ne' hA
      (fun v => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
        (e.val.symm v)).toReal)).symm
  have hmetric : (fun x => TosC11c.twoFormMetric (w.form.val.coeff e x)) =
      TosC11c.chartMetric w e := by
    funext x
    rfl
  rw [hmetric] at H
  exact H

end SGPT.NPP.DNTBig
