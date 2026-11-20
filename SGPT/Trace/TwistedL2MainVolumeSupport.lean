import SGPT.Trace.TwistedL2MainLocalMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth positive volume has full support

The positivity of the actual chart density transfers positivity of nonempty
Euclidean open sets to the original manifold volume. This supplies the
uniqueness step for gluing continuous local representatives.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

set_option linter.unusedSectionVars false in
/-- A volume with positive chart densities assigns positive measure to every
nonempty open set. -/
theorem smoothPositiveVolume_isOpenPosMeasure {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) : Measure.IsOpenPosMeasure μ := by
  constructor
  intro U hU ⟨x, hx⟩ hzero
  let c := complexChartAt (n := n) x
  have hxs : x ∈ c.val.source := mem_complexChartAt_source x
  obtain ⟨ρ, hρ⟩ := hμ c
  let D := c.val.target ∩ c.val.symm ⁻¹' U
  have hDo : IsOpen D := c.val.isOpen_inter_preimage_symm hU
  have hDm : MeasurableSet D := hDo.measurableSet
  have hDt : D ⊆ c.val.target := inter_subset_left
  have hne : D.Nonempty := by
    refine ⟨c.val x, c.val.map_source hxs, ?_⟩
    simpa only [mem_preimage, c.val.left_inv hxs] using hx
  have hρm : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict D) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρ.1.continuousOn.mono hDt)).aemeasurable hDm
  have hρpos : ∀ᵐ z ∂(volume.restrict D), ENNReal.ofReal (ρ z) ≠ 0 := by
    filter_upwards [ae_restrict_mem hDm] with z hz
    exact (ENNReal.ofReal_pos.mpr (hρ.2.1 z (hDt hz))).ne'
  have hac : volume.restrict D ≪
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) :=
    withDensity_absolutelyContinuous' hρm hρpos
  let ν : Measure X := (μ.restrict c.val.source).restrict (c.val ⁻¹' D)
  have hsub : c.val ⁻¹' D ∩ c.val.source ⊆ U := by
    intro y hy
    have hyU : c.val.symm (c.val y) ∈ U := hy.1.2
    simpa only [c.val.left_inv hy.2] using hyU
  have hzero' : μ (c.val ⁻¹' D ∩ c.val.source) = 0 := measure_mono_null hsub hzero
  have hνzero : ν univ = 0 := by
    dsimp [ν]
    rw [Measure.restrict_restrict' c.val.open_source.measurableSet, Measure.restrict_apply_univ]
    exact hzero'
  have he : AEMeasurable c.val ν :=
    (c.val.continuousOn.aemeasurable c.val.open_source.measurableSet).restrict
  have hpush : Measure.map c.val ν =
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) :=
    chartDensity_map_restrict c hρ hDm hDt
  have hρzero : ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) univ = 0 := by
    rw [← hpush, Measure.map_apply_of_aemeasurable he MeasurableSet.univ]
    simpa using hνzero
  have hlambdaZero := hac hρzero
  rw [Measure.restrict_apply_univ] at hlambdaZero
  exact (hDo.measure_ne_zero volume hne) hlambdaZero

end SGPT.Trace.TwistedL2
