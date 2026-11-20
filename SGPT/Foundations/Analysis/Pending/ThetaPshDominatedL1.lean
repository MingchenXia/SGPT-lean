import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1

/-!
# Dominated chart-local L1 convergence of theta-psh potentials

An almost-everywhere pointwise convergent sequence bounded below by a genuine
theta-psh potential and above by one real constant converges in the canonical
chart-local L1 topology. Poles are removed only on their actual null sets.
This is the dominated convergence step for endpoint Perron stability.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaPshDominatedL1

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An actual theta-psh lower barrier and a real upper bound turn chartwise
almost-everywhere pointwise convergence into canonical chart-local L1 convergence. -/
theorem manifoldL1LocallyTendsto_of_ae_tendsto_of_bounds
    {theta : SmoothRealForm n M 2} {u : ℕ → M → EReal} {v w : M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta (u j))
    (hv : IsThetaPshPotential theta v) (hw : IsThetaPshPotential theta w)
    {C : ℝ} (hC : ∀ j x, u j x ≤ (C : EReal)) (hwu : ∀ j, w ≤ u j)
    (hlim : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun j => chartFunction (u j) e z) atTop (𝓝 (chartFunction v e z))) :
    ManifoldL1LocallyTendsto (n := n) u atTop v := by
  intro e K hK hKe
  let μ : Measure (ComplexModel n) := volume.restrict K
  have : IsFiniteMeasure μ := ⟨by simpa [μ] using hK.measure_lt_top⟩
  have hfinv : ∀ᵐ z ∂μ, chartFunction v e z ≠ ⊤ ∧ chartFunction v e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hv.quasiPshPotential.ae_finite_chart e)
  have hfinw : ∀ᵐ z ∂μ, chartFunction w e z ≠ ⊤ ∧ chartFunction w e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hw.quasiPshPotential.ae_finite_chart e)
  have hfinu : ∀ᵐ z ∂μ, ∀ j,
      chartFunction (u j) e z ≠ ⊤ ∧ chartFunction (u j) e z ≠ ⊥ :=
    ae_all_iff.mpr fun j => ae_restrict_of_ae_restrict_of_subset hKe
      ((hu j).quasiPshPotential.ae_finite_chart e)
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun z => (chartFunction (u j) e z).toReal) μ := fun j =>
    ((hu j).quasiPshPotential.aemeasurable_chart_restrict e hKe).ereal_toReal
      |>.aestronglyMeasurable
  let bound : ComplexModel n → ℝ := fun z => |(chartFunction w e z).toReal| + |C|
  have hint : Integrable bound μ := by
    have hwint : Integrable (fun z => (chartFunction w e z).toReal) μ :=
      hw.quasiPshPotential.integrableOn_chart_toReal e hK hKe
    dsimp [bound]
    exact hwint.abs.add (integrable_const |C|)
  have hbound : ∀ j, ∀ᵐ z ∂μ, ‖(chartFunction (u j) e z).toReal‖ ≤ bound z := by
    intro j
    filter_upwards [hfinw, hfinu] with z hzw hzu
    have hlo : (chartFunction w e z).toReal ≤ (chartFunction (u j) e z).toReal :=
      EReal.toReal_le_toReal (hwu j (e.val.symm z)) hzw.2 (hzu j).1
    have hhi : (chartFunction (u j) e z).toReal ≤ C := by
      change (u j (e.val.symm z)).toReal ≤ C
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal (hC j (e.val.symm z))
        (hzu j).2 (EReal.coe_ne_top C)
    change |(chartFunction (u j) e z).toReal| ≤ _
    apply abs_le.mpr
    constructor
    · dsimp [bound]
      linarith [neg_abs_le (chartFunction w e z).toReal, abs_nonneg C]
    · dsimp [bound]
      linarith [le_abs_self C, abs_nonneg (chartFunction w e z).toReal]
  have hpoint : ∀ᵐ z ∂μ, Tendsto (fun j => (chartFunction (u j) e z).toReal)
      atTop (𝓝 (chartFunction v e z).toReal) := by
    filter_upwards [hfinv, ae_restrict_of_ae_restrict_of_subset hKe (hlim e)] with z hz hzt
    exact (EReal.tendsto_toReal hz.1 hz.2).comp hzt
  have hDCT := tendsto_lintegral_norm_of_dominated_convergence
    hmeas hint.hasFiniteIntegral hbound hpoint
  have hcanonical : ∀ j, chartL1EDistance (u j) v e K =
      ∫⁻ z, ENNReal.ofReal ‖(chartFunction (u j) e z).toReal -
        (chartFunction v e z).toReal‖ ∂μ := by
    intro j
    apply lintegral_congr_ae
    filter_upwards [hfinv, hfinu] with z hzv hzu
    conv_lhs => rw [← EReal.coe_toReal (hzu j).1 (hzu j).2,
      ← EReal.coe_toReal hzv.1 hzv.2, canonicalERealAbsDiff_coe_coe]
    simp only [Real.norm_eq_abs]
  simpa only [hcanonical] using hDCT

end SGPT.Foundations.Analysis.Pending.ThetaPshDominatedL1
