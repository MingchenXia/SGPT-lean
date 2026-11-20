import SGPT.PSH.HermitianProductsTopTracePullback
import SGPT.PSH.HermitianComparisonStrict

/-!
# Literal Borel trace tests of positive currents

The coefficient of the canonical trace form has density one relative to
the genuine Riesz trace measure. Borel multiplication therefore reads as
the ordinary weighted integral, and the actual strict-set weight reads
as a set integral. No weighted-current or measure identity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
open HermitianComparisonCutoff HermitianComparisonStrict
open scoped Distributions Topology

variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- The actual canonical trace coefficient has density one. -/
theorem density_trace_ae {T : LocalProductCurrent n U q} (hT : IsPositive T) :
    hT.density (kahlerPower n q) =ᵐ[hT.traceMeasure] fun _ => (1 : ℝ) :=
  (densityForm_ae hT (kahlerPower n q)).symm.trans (densityForm_trace_ae hT)

/-- Multiplication of the original positive current by a locally bounded
Borel function is ordinary integration against its actual trace measure. -/
theorem mulBorel_trace_apply {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    (φ : 𝓓(U, ℝ)) :
    mulBorel T f (kahlerPower n q) φ = ∫ z, φ z * f z ∂hT.traceMeasure := by
  rw [mulBorel_apply hT hf hfb]
  apply integral_congr_ae
  filter_upwards [density_trace_ae hT] with z hz
  rw [hz, mul_one]

/-- A genuine Borel set gives its literal set integral, without requiring
its indicator to be smooth. -/
theorem mulBorel_indicator_trace_apply {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {E : Set (ComplexModel n)} (hE : MeasurableSet E)
    (φ : 𝓓(U, ℝ)) :
    mulBorel T (E.indicator (fun _ => (1 : ℝ))) (kahlerPower n q) φ =
      ∫ z in E, φ z ∂hT.traceMeasure := by
  have hb : IsLocallyBoundedOn (E.indicator (fun _ => (1 : ℝ))) U := by
    intro K _ _
    refine ⟨1, fun z _ => ?_⟩
    by_cases hz : z ∈ E <;> simp [hz]
  rw [mulBorel_trace_apply hT (measurable_const.indicator hE) hb]
  have heq : (fun z => φ z * E.indicator (fun _ => (1 : ℝ)) z) =
      E.indicator (fun z => φ z) := by
    funext z
    by_cases hz : z ∈ E <;> simp [hz]
  rw [heq, integral_indicator hE]

theorem scalarUnit_eq_kahlerPower_zero :
    (scalarUnit : formSpan n 0) = kahlerPower n 0 := by
  apply Subtype.ext
  rfl

/-- In degree top the comparison module's scalar unit is the canonical
trace form, so its actual Borel test has the same integral readback. -/
theorem mulBorel_scalarUnit_apply {T : LocalProductCurrent n U 0} (hT : IsPositive T)
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    (φ : 𝓓(U, ℝ)) :
    mulBorel T f scalarUnit φ = ∫ z, φ z * f z ∂hT.traceMeasure := by
  rw [scalarUnit_eq_kahlerPower_zero]
  exact mulBorel_trace_apply hT hf hfb φ

/-- Local measurable representatives suffice for the genuine strict set. -/
theorem measurableSet_strict_local {a b : ComplexModel n → ℝ}
    (ha : Measurable ((U : Set (ComplexModel n)).indicator a))
    (hb : Measurable ((U : Set (ComplexModel n)).indicator b)) :
    MeasurableSet ((U : Set (ComplexModel n)) ∩ {z | a z < b z}) := by
  have heq : (U : Set (ComplexModel n)) ∩ {z | a z < b z} =
      (U : Set (ComplexModel n)) ∩ {z |
        (U : Set (ComplexModel n)).indicator a z <
          (U : Set (ComplexModel n)).indicator b z} := by
    ext z
    by_cases hz : z ∈ U <;> simp [hz]
  rw [heq]
  exact U.isOpen.measurableSet.inter (measurableSet_lt ha hb)

/-- The original cutoff limit is exactly the indicator of the actual
strict set, including zero on the coincidence set. -/
theorem unitIndicator_strictIndicator_eq (a b : ComplexModel n → ℝ) :
    (U : Set (ComplexModel n)).indicator (fun z => strictIndicator (b z - a z)) =
      ((U : Set (ComplexModel n)) ∩ {z | a z < b z}).indicator (fun _ => (1 : ℝ)) := by
  funext z
  by_cases hz : z ∈ U
  · by_cases hab : a z < b z
    · simp [hz, hab, strictIndicator]
    · simp [hz, hab, strictIndicator]
  · simp [hz]

/-- The literal strict one-factor weight reads as the original trace
measure on `U ∩ {a < b}`. -/
theorem mulBorel_strictIndicator_scalarUnit_apply
    {T : LocalProductCurrent n U 0} (hT : IsPositive T)
    {a b : ComplexModel n → ℝ}
    (ha : Measurable ((U : Set (ComplexModel n)).indicator a))
    (hb : Measurable ((U : Set (ComplexModel n)).indicator b)) (φ : 𝓓(U, ℝ)) :
    mulBorel T ((U : Set (ComplexModel n)).indicator
      (fun z => strictIndicator (b z - a z))) scalarUnit φ =
      ∫ z in (U : Set (ComplexModel n)) ∩ {z | a z < b z}, φ z ∂hT.traceMeasure := by
  rw [unitIndicator_strictIndicator_eq, scalarUnit_eq_kahlerPower_zero]
  exact mulBorel_indicator_trace_apply hT (measurableSet_strict_local ha hb) φ

/-- Both original positive currents, rather than a signed-current Borel
fallback, give the literal difference of their strict-set trace integrals. -/
theorem mulBorel_strict_difference_scalarUnit_apply
    {A B : LocalProductCurrent n U 0} (hA : IsPositive A) (hB : IsPositive B)
    {a b : ComplexModel n → ℝ}
    (ha : Measurable ((U : Set (ComplexModel n)).indicator a))
    (hb : Measurable ((U : Set (ComplexModel n)).indicator b)) (φ : 𝓓(U, ℝ)) :
    (mulBorel B ((U : Set (ComplexModel n)).indicator
        (fun z => strictIndicator (b z - a z))) -
      mulBorel A ((U : Set (ComplexModel n)).indicator
        (fun z => strictIndicator (b z - a z)))) scalarUnit φ =
      (∫ z in (U : Set (ComplexModel n)) ∩ {z | a z < b z}, φ z ∂hB.traceMeasure) -
        ∫ z in (U : Set (ComplexModel n)) ∩ {z | a z < b z}, φ z ∂hA.traceMeasure := by
  simp only [LinearMap.sub_apply, sub_apply,
    mulBorel_strictIndicator_scalarUnit_apply hA ha hb,
    mulBorel_strictIndicator_scalarUnit_apply hB ha hb]

end SGPT.PSH.HermitianProducts
