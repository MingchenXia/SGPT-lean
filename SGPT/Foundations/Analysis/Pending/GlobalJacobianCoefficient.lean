import SGPT.Foundations.Analysis.Pending.ActualFlatNormalOrder
import SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalJacobianCoefficient

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps
  HironakaHolomorphicJetRankLoci HolomorphicGermJacobian DivisorialChangeOfVariables
  FixedGermNormalOrder ActualFlatNormalOrder GlobalRelativeJacobianIdeal

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {E : Set Y} {y : Y}

/-- Entire original preferred-generator readback, including an identically zero Jacobian. -/
theorem chartTranslatedJacobian_eq_preferred {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π) (y : Y) :
    chartTranslatedGerm y y (mem_chart_source _ y)
      (chartJacobianFunction (n := m + 1) π y (π y))
      (holomorphicAt_chartJacobianFunction hπ y (π y)
        (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))) =
      preferredJacobianGerm hπ y := by
  apply Subtype.ext
  rw [preferredJacobianGerm, jacobianGerm_source]
  unfold chartTranslatedGerm translatedGerm
  rw [HolGerm.coe_mk]
  apply Germ.coe_eq.mpr
  let e := (complexChartAt (n := m + 1) y).val
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e y) (𝓝 0) (𝓝 (e y)) := by
    simpa only [zero_add] using (continuous_add_const (e y)).tendsto 0
  filter_upwards [ht.eventually (e.open_target.mem_nhds
    (e.map_source (mem_complexChartAt_source y)))] with z hz
  change complexJacobian
    (coordinateMap π (complexChartAt (n := m + 1) y) (complexChartAt (n := m + 1) (π y)))
      (e (e.symm (z + e y))) = complexJacobian (preferredCenteredMap π y) z
  rw [e.right_inv hz]
  unfold preferredCenteredMap complexJacobian
  rw [fderiv_sub_const, fderiv_comp_add_right]

/-- The ENTIRE original ideal has the same actual flat Jacobian order; no numerical identity is input. -/
theorem originalStalkNormalOrder_relativeJacobianIdeal_eq_flat {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DemaillyApproximantDivisorialLelong.DivisorFlattening (m := m) E y) :
    originalStalkNormalOrder Φ (relativeJacobianIdeal (n := m + 1) π) = flatJacobianOrder hπ Φ := by
  let G : Fin 1 → Y → ℂ := fun _ => chartJacobianFunction (n := m + 1) π y (π y)
  have hG : ∀ i, HolomorphicAt (m + 1) (G i) y := fun _ =>
    holomorphicAt_chartJacobianFunction hπ y (π y)
      (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  have hgen : ∀ f, (relativeJacobianIdeal (n := m + 1) π).mem y f ↔
      IsInSpanAt (n := m + 1) (· ∈ range G) y f := by
    intro f
    rw [mem_relativeJacobianIdeal_iff_chart hπ y (π y)
      (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))]
    simp only [G, range_const, mem_singleton_iff]
  rw [originalStalkNormalOrder_eq_generators Φ (relativeJacobianIdeal (n := m + 1) π) G hG hgen]
  change (⨅ _ : Fin 1, functionNormalOrder Φ
    (chartJacobianFunction (n := m + 1) π y (π y))
    (holomorphicAt_chartJacobianFunction hπ y (π y)
      (mem_complexChartAt_source y) (mem_complexChartAt_source (π y)))) = _
  rw [iInf_const]
  unfold functionNormalOrder
  rw [chartTranslatedJacobian_eq_preferred hπ y]
  exact preferredJacobianOrder_eq_flat hπ Φ

/-- The actual internally manufactured effective divisor retains the complete local order dictionary. -/
theorem originalStalkNormalOrder_actualRelativeJacobianDivisor_eq_flat {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DemaillyApproximantDivisorialLelong.DivisorFlattening (m := m) E y) :
    originalStalkNormalOrder Φ (actualRelativeJacobianDivisor hπ).ideal = flatJacobianOrder hπ.1 Φ := by
  rw [actualRelativeJacobianDivisor_ideal_eq]
  exact originalStalkNormalOrder_relativeJacobianIdeal_eq_flat hπ.1 Φ

end SGPT.Foundations.Analysis.Pending.GlobalJacobianCoefficient
