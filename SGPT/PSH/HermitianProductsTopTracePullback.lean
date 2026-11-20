import SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

/-! Top-degree current traces obey the actual inverse-chart measure law.
The ambient inverse need only be holomorphic on its genuine open domain. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open BedfordTaylor StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback LocalBedfordTaylorLocality

variable {n : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n} {T : LocalProductCurrent n B 0}

/-- The trace coefficient has density one relative to its own actual
Riesz trace measure. -/
theorem densityForm_trace_ae {q : ℕ} {U : Opens (ComplexModel n)}
    {R : LocalProductCurrent n U q} (hR : IsPositive R) :
    (fun x => densityForm hR x (kahlerPower n q)) =ᵐ[hR.traceMeasure] fun _ => (1 : ℝ) := by
  obtain ⟨C, _, hC⟩ := exists_abs_densityForm_le hR (kahlerPower n q)
  refine hR.ae_eq_of_forall_integral_eq
    (measurable_densityForm hR (kahlerPower n q)) measurable_const
    ⟨C, hC⟩ ⟨1, by intros; simp⟩ fun φ => ?_
  rw [← apply_eq_integral_densityForm hR, ← hR.integral_traceMeasure]
  simp only [mul_one]

/-- A complex linear change of variables fixes the genuine degree-zero unit. -/
theorem pullSpan_zero_unit (L : ComplexModel n →L[ℂ] ComplexModel n) :
    pullSpan 0 L (kahlerPower n 0) = kahlerPower n 0 := by
  apply Subtype.ext
  ext v
  rfl

/-- A genuine positive top current pulls back by ordinary transport of its
trace measure, with no Jacobian factor in current degree top. -/
theorem traceMeasure_pullback_top (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    (isPositive_pullback h hT).traceMeasure = pbMeasure σ hT := by
  apply eq_of_forall_testFunction_integral_eq
    (isPositive_pullback h hT).traceMeasure_compl (pbMeasure_compl h hT)
    (fun K hK hKA => (isPositive_pullback h hT).traceMeasure_lt_top hK hKA)
    (fun K hK hKA => pbMeasure_lt_top h hT hK hKA)
  intro φ
  rw [(isPositive_pullback h hT).integral_traceMeasure, pullback_apply,
    integral_pbMeasure h hT φ.continuous.aestronglyMeasurable]
  simp_rw [pullSpan_zero_unit]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (densityForm_trace_ae hT)] with x hx
  rw [hx, mul_one]

/-- The literal ambient inverse gives the same measure as its measurable
zero extension: the original trace is carried by the actual chart domain. -/
theorem traceMeasure_pullback_top_eq_map
    (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    (isPositive_pullback h hT).traceMeasure = (hT.traceMeasure.restrict B).map σ := by
  rw [traceMeasure_pullback_top h hT, pbMeasure]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with x hx
  exact onOpen_of_mem hx

end SGPT.PSH.HermitianProducts
