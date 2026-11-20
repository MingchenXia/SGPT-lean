import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Actual finite-measure Portmanteau reader: if the ORIGINAL measures
converge weakly and their mass on an open set tends to zero, their actual
weak limit gives that set zero mass. No probability normalization. -/
theorem finiteMeasure_open_eq_zero_of_mass_tendsto_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {tau : FiniteMeasure X} {nu : ℕ → FiniteMeasure X}
    (hweak : Tendsto nu atTop (𝓝 tau)) {F : Set X} (hF : IsOpen F)
    (hzero : Tendsto (fun j => (nu j : Measure X) F) atTop (𝓝 0)) :
    (tau : Measure X) F = 0 := by
  have hmass : Tendsto (fun j => (nu j : Measure X) univ) atTop
      (𝓝 ((tau : Measure X) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have hsub := ENNReal.Tendsto.sub hmass hzero (Or.inr ENNReal.zero_ne_top)
  have hcomp : Tendsto (fun j => (nu j : Measure X) Fᶜ) atTop
      (𝓝 ((tau : Measure X) univ)) := by
    have heq : (fun j => (nu j : Measure X) Fᶜ) =
        (fun j => (nu j : Measure X) univ - (nu j : Measure X) F) := by
      funext j
      exact measure_compl hF.measurableSet (measure_ne_top _ _)
    rw [heq]
    simpa only [tsub_zero] using hsub
  have hclosed := FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak hF.isClosed_compl
  rw [hcomp.limsup_eq] at hclosed
  have hsum : (tau : Measure X) F + (tau : Measure X) Fᶜ ≤ (tau : Measure X) Fᶜ :=
    (measure_add_measure_compl hF.measurableSet).le.trans hclosed
  apply le_antisymm ?_ zero_le
  apply (ENNReal.add_le_add_iff_right (measure_ne_top (tau : Measure X) Fᶜ)).mp
  simpa only [zero_add] using hsum

end SGPT.Bergman.ContactConcentration
