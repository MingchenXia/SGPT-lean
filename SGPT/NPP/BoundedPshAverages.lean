import SGPT.NPP.JointRadialContinuity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual bounded PSH parameter averages

Complete blueprint: `blueprint/src/dnt-big-bounded-psh-averages.tex`, written
first. This proves the actual Fubini/disc-submean step for finite-measure
averages. It is a general analytic theorem; the actual source smoothing's
continuity is already proved separately, while its local bounded parameter
instantiation remains separate work.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- Actual bounded finite-measure averages preserve PSH once the same actual
average's continuity has been established. The proof derives and interchanges
the actual disc means; no averaged submean certificate is assumed. -/
theorem plurisubharmonicOn_boundedParameterAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E × A → ℝ} (hF : Measurable F)
    (hpsh : ∀ a, PlurisubharmonicOn (fun z => (F (z, a) : EReal)) Ω)
    {M : ℝ} (_hM0 : 0 ≤ M) (hM : ∀ z ∈ Ω, ∀ a, ‖F (z, a)‖ ≤ M)
    (hcont : ContinuousOn (fun z => ∫ a, F (z, a) ∂μ) Ω) :
    PlurisubharmonicOn (fun z => ((∫ a, F (z, a) ∂μ : ℝ) : EReal)) Ω := by
  apply DiscPshOn.plurisubharmonicOn _ hΩ
  refine ⟨fun z _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp_continuousOn hcont).upperSemicontinuousOn, ?_⟩
  intro z v r hr hD C hC
  have hzΩ : z ∈ Ω := hD (center_mem_affineClosedDisc z v hr.le)
  have hcircleΩ : ∀ t : ℝ, z + circleMap 0 r t • v ∈ Ω := fun t =>
    hD (circle_mem_affineClosedDisc z v hr.le t)
  have hcircle : Continuous (fun t : ℝ => ∫ a, F (z + circleMap 0 r t • v, a) ∂μ) :=
    hcont.comp_continuous (by fun_prop) hcircleΩ
  apply (circleDeficit_coe_le_iff z v r C (hcircle.intervalIntegrable _ _)
    (fun t => EReal.coe_le_coe_iff.mp
      (hC _ (circle_mem_affineClosedDisc z v hr.le t)))
    (EReal.coe_le_coe_iff.mp (hC z (center_mem_affineClosedDisc z v hr.le)))).mpr
  have hpi : 0 < 2 * Real.pi := by positivity
  let σ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let _ : IsFiniteMeasure σ := ⟨by
    change (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) univ < ⊤
    simpa using (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) (2 * Real.pi)) < ⊤)⟩
  let J : ℝ → A → ℝ := fun t a => F (z + circleMap 0 r t • v, a)
  have hcurve : Measurable (fun t : ℝ => z + circleMap 0 r t • v) :=
    (by fun_prop : Continuous (fun t : ℝ => z + circleMap 0 r t • v)).measurable
  have hJmeas : Measurable (Function.uncurry J) :=
    hF.comp ((hcurve.comp measurable_fst).prodMk measurable_snd)
  have hJbound : ∀ t a, ‖J t a‖ ≤ M := fun t a => hM _ (hcircleΩ t) a
  have hJint : Integrable (Function.uncurry J) (σ.prod μ) :=
    (integrable_const M : Integrable (fun _ : ℝ × A => M) (σ.prod μ)).mono'
      hJmeas.aestronglyMeasurable (Eventually.of_forall fun p => hJbound p.1 p.2)
  have hmean : ∀ a, F (z, a) ≤
      Real.circleAverage (fun ζ : ℂ => F (z + ζ • v, a)) 0 r := by
    intro a
    have hIa : Integrable (fun t => J t a) σ :=
      (integrable_const M : Integrable (fun _ : ℝ => M) σ).mono'
        (hF.comp (hcurve.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun t => hJbound t a)
    have hinterval : IntervalIntegrable (fun t : ℝ => F (z + circleMap 0 r t • v, a))
        volume 0 (2 * Real.pi) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr hIa
    have hdiscM : ∀ x ∈ affineClosedDisc z v r, (F (x, a) : EReal) ≤ (M : EReal) := by
      intro x hx
      exact EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs] using hM x (hD hx) a))
    exact (circleDeficit_coe_le_iff z v r M hinterval
      (fun t => EReal.coe_le_coe_iff.mp (hdiscM _ (circle_mem_affineClosedDisc z v hr.le t)))
      (EReal.coe_le_coe_iff.mp (hdiscM z (center_mem_affineClosedDisc z v hr.le)))).mp
        ((hpsh a).discPshOn.submean z v r hr hD M hdiscM)
  have hcenterI : Integrable (fun a => F (z, a)) μ :=
    (integrable_const M : Integrable (fun _ : A => M) μ).mono'
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun a => hM z hzΩ a)
  have hmeanI : Integrable
      (fun a => Real.circleAverage (fun ζ : ℂ => F (z + ζ • v, a)) 0 r) μ := by
    simpa only [Real.circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le hpi.le, σ, J, Function.uncurry_apply_pair] using
      hJint.integral_prod_right.const_mul ((2 * Real.pi)⁻¹)
  have hswap : (∫ a, Real.circleAverage (fun ζ : ℂ => F (z + ζ • v, a)) 0 r ∂μ) =
      Real.circleAverage (fun ζ : ℂ => ∫ a, F (z + ζ • v, a) ∂μ) 0 r := by
    simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le hpi.le]
    change (∫ a, (2 * Real.pi)⁻¹ * (∫ t, J t a ∂σ) ∂μ) =
      (2 * Real.pi)⁻¹ * (∫ t, ∫ a, J t a ∂μ ∂σ)
    rw [integral_const_mul]
    congr 1
    exact (integral_integral_swap hJint).symm
  exact (integral_mono hcenterI hmeanI hmean).trans_eq hswap

end SGPT.NPP.DNTBig
