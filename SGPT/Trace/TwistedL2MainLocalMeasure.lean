import SGPT.Trace.TwistedL2MainLocalCoefficient

/-!
# Local chart-volume transport for the twisted `L²` construction

The restricted pushforward below is a preliminary step toward transporting
actual bundle-correction coefficients into a weighted Euclidean `L²` space.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Restriction to an arbitrary measurable subset of a chart target commutes
with the chart-density pushforward. -/
theorem chartDensity_map_restrict {μ : Measure X} (c : ComplexChart n X)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity μ c ρ)
    {D : Set (ComplexModel n)} (hDm : MeasurableSet D) (hDt : D ⊆ c.val.target) :
    Measure.map c.val ((μ.restrict c.val.source).restrict (c.val ⁻¹' D)) =
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
  have he : AEMeasurable c.val (μ.restrict c.val.source) :=
    c.val.continuousOn.aemeasurable c.val.open_source.measurableSet
  rw [← Measure.restrict_map_of_aemeasurable he hDm, hρ.2.2, restrict_withDensity hDm,
    Measure.restrict_restrict hDm, inter_eq_left.mpr hDt]


omit [IsComplexManifold n X] in
/-- Transporting the positive-density chart measure back by the inverse chart
recovers exactly the manifold measure restricted to the chart over `D`. -/
theorem chartDensity_map_symm_restrict {μ : Measure X} (c : ComplexChart n X)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity μ c ρ)
    {D : Set (ComplexModel n)} (hDm : MeasurableSet D) (hDt : D ⊆ c.val.target) :
    Measure.map c.val.symm ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) =
      (μ.restrict c.val.source).restrict (c.val ⁻¹' D) := by
  let ν : Measure X := (μ.restrict c.val.source).restrict (c.val ⁻¹' D)
  have hpush : Measure.map c.val ν =
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) :=
    chartDensity_map_restrict c hρ hDm hDt
  have he : AEMeasurable c.val ν :=
    (c.val.continuousOn.aemeasurable c.val.open_source.measurableSet).restrict
  have hesymm : AEMeasurable c.val.symm (Measure.map c.val ν) := by
    rw [hpush]
    exact ((c.val.continuousOn_symm.mono hDt).aemeasurable hDm).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hsource : ∀ᵐ x ∂ν, x ∈ c.val.source := by
    exact (ae_restrict_mem c.val.open_source.measurableSet).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hinv : (c.val.symm ∘ c.val) =ᵐ[ν] id :=
    hsource.mono fun x hx => c.val.left_inv hx
  calc
    Measure.map c.val.symm ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) =
        Measure.map c.val.symm (Measure.map c.val ν) := by rw [hpush]
    _ = Measure.map (c.val.symm ∘ c.val) ν := AEMeasurable.map_map_of_aemeasurable hesymm he
    _ = Measure.map id ν := Measure.map_congr hinv
    _ = ν := Measure.map_id

end SGPT.Trace.TwistedL2
