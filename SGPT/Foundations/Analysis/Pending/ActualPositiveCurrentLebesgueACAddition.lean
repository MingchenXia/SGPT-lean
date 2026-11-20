import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueUniqueness

set_option autoImplicit false

/-! # Actual carried-current trace and absolutely continuous addition

Natural positive currents produce the trace classes of their parts.
An arbitrary smooth remainder is a separate subsequent application.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality ActualPositiveCurrentLebesgueUniqueness

variable {n q : ℕ} {U : Opens (ComplexModel n)}


/-- The actual positive current carried by a dominated measure has exactly
that measure as its actual trace; no trace identity is supplied. -/
theorem traceMeasure_ofMeasure {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {ν : Measure (ComplexModel n)} (hν : ν ≤ hT.traceMeasure) :
    (isPositive_ofMeasure hT hν).traceMeasure = ν := by
  have hunit : (fun x => densityForm hT x (kahlerPower n q)) =ᵐ[hT.traceMeasure]
      fun _ => (1 : ℝ) := by
    obtain ⟨C, _, hC⟩ := exists_abs_densityForm_le hT (kahlerPower n q)
    refine hT.ae_eq_of_forall_integral_eq
      (measurable_densityForm hT (kahlerPower n q)) measurable_const
      ⟨C, hC⟩ ⟨1, by intros; simp⟩ fun φ => ?_
    rw [← apply_eq_integral_densityForm hT, ← hT.integral_traceMeasure]
    simp only [mul_one]
  apply eq_of_forall_testFunction_integral_eq
    (isPositive_ofMeasure hT hν).traceMeasure_compl
  · exact le_antisymm ((Measure.le_iff'.mp hν _).trans_eq hT.traceMeasure_compl) bot_le
  · exact fun K hK hKU => (isPositive_ofMeasure hT hν).traceMeasure_lt_top hK hKU
  · exact fun K hK hKU => (Measure.le_iff'.mp hν K).trans_lt (hT.traceMeasure_lt_top hK hKU)
  · intro φ
    rw [(isPositive_ofMeasure hT hν).integral_traceMeasure, ofMeasure_apply]
    apply integral_congr_ae
    filter_upwards [(Measure.absolutelyContinuous_of_le hν).ae_le hunit] with x hx
    rw [hx, mul_one]


/-- Both actual positive coefficient parts carry their constructed trace
submeasures and therefore their genuine singular/AC trace classes. -/
theorem part_trace_classes {T : LocalProductCurrent n U q} (hT : IsPositive T) :
    (isPositive_sgPart hT).traceMeasure = sgMeasure hT ∧
      (isPositive_sgPart hT).traceMeasure ⟂ₘ volume ∧
      (isPositive_acPart hT).traceMeasure = acMeasure hT ∧
      (isPositive_acPart hT).traceMeasure ≪ volume := by
  have hs : (isPositive_sgPart hT).traceMeasure = sgMeasure hT :=
    traceMeasure_ofMeasure hT (sgMeasure_le hT)
  have ha : (isPositive_acPart hT).traceMeasure = acMeasure hT :=
    traceMeasure_ofMeasure hT (acMeasure_le hT)
  refine ⟨hs, ?_, ha, ?_⟩
  · rw [hs]
    exact sgMeasure_mutuallySingular hT
  · rw [ha]
    exact acMeasure_absolutelyContinuous hT

/-- Adding an actual positive AC current preserves the complete singular
part and adds that current to the complete AC part. -/
theorem parts_of_add_absolutelyContinuous
    {T B : LocalProductCurrent n U q} (hT : IsPositive T) (hB : IsPositive B)
    (hBa : hB.traceMeasure ≪ volume) :
    sgPart (hT.add hB) = sgPart hT ∧ acPart (hT.add hB) = acPart hT + B := by
  obtain ⟨_, hSs, _, hAa⟩ := part_trace_classes hT
  let hS := isPositive_sgPart hT
  let hA := isPositive_acPart hT
  have hRa : (hA.add hB).traceMeasure ≪ volume := by
    rw [traceMeasure_add hA hB]
    intro E hE
    rw [Measure.add_apply, hAa hE, hBa hE, add_zero]
  have hparts := parts_of_singular_add_absolutelyContinuous hS (hA.add hB) hSs hRa
  have heq : sgPart hT + (acPart hT + B) = T + B := by
    rw [← add_assoc, sgPart_add_acPart]
  simpa only [heq] using hparts

end SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition
