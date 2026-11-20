import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability

open FirstPass ChartwiseGlobalL1

/-- A finite actual chart cover globalizes local integrability for a smooth volume. -/
theorem integrable_of_chartwise_locallyIntegrable {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (f : M → ℝ) (hf : Measurable f)
    (hlocal : ∀ e : ComplexChart n M,
      LocallyIntegrableOn (fun z => f (e.val.symm z)) e.val.target volume) :
    Integrable f μ := by
  classical
  obtain ⟨t, r, _, hr, hcover⟩ := exists_finite_chart_cover (n := n) (M := M)
  let e (x : M) := complexChartAt (n := n) x
  let K (x : M) := Metric.closedBall ((e x).val x) (r x)
  let S (x : M) := (e x).val.source ∩ (e x).val ⁻¹' K x
  let g (x : M) : ℝ≥0∞ := ‖f x‖ₑ
  have hg : Measurable g := hf.enorm
  have hS (x : M) : MeasurableSet (S x) :=
    measurableSet_source_inter_preimage (e x).val Metric.isClosed_closedBall
  have hfinite (x : M) : (∫⁻ y in S x, g y ∂μ) < ⊤ := by
    obtain ⟨ρ, hρs, _, hmap⟩ := hμ (e x)
    have hK : IsCompact (K x) := isCompact_closedBall _ _
    have hKt : K x ⊆ (e x).val.target := hr x
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hρs.continuousOn.mono hKt)
    have hint := (hlocal (e x)).integrableOn_compact_subset hKt hK
    have hfin : (∫⁻ z in K x, g ((e x).val.symm z)) < ⊤ := hint.hasFiniteIntegral
    have hbound : (∫⁻ y in S x, g y ∂μ) ≤
        ENNReal.ofReal B * (∫⁻ z in K x, g ((e x).val.symm z)) := by
      rw [setLIntegral_source_inter_preimage (e x) hρs.continuousOn hmap hK hKt hg]
      calc
        _ ≤ ∫⁻ z in K x, ENNReal.ofReal B * g ((e x).val.symm z) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
          apply mul_le_mul' _ le_rfl
          apply ENNReal.ofReal_le_ofReal
          exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hbound : (∫⁻ y, g y ∂μ) ≤ ∑ x ∈ t, ∫⁻ y in S x, g y ∂μ := by
    calc
      _ ≤ ∫⁻ y, ∑ x ∈ t, (S x).indicator g y ∂μ := by
        apply lintegral_mono
        intro y
        obtain ⟨x, hx, hy⟩ := hcover y
        calc
          g y = (S x).indicator g y := (indicator_of_mem hy g).symm
          _ ≤ ∑ x ∈ t, (S x).indicator g y :=
            Finset.single_le_sum (f := fun x => (S x).indicator g y)
              (fun _ _ => zero_le) hx
      _ = ∑ x ∈ t, ∫⁻ y in S x, g y ∂μ := by
        rw [lintegral_finsetSum t (fun x _ => hg.indicator (hS x))]
        apply Finset.sum_congr rfl
        intro x _
        exact lintegral_indicator (hS x) g
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  exact hbound.trans_lt (ENNReal.sum_lt_top.mpr fun x _ => hfinite x)

/-- The original locally nondegenerate quasi-PSH potential supplies every local integrability input. -/
theorem integrable_toReal_of_genuine_quasiPsh {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    Integrable (fun x => (u x).toReal) μ := by
  apply integrable_of_chartwise_locallyIntegrable μ hμ _
    hu.1.upperSemicontinuous.measurable.ereal_toReal
  exact hu.locallyIntegrableOn_chart_toReal

/-- Genuine theta-PSH potentials are integrable for every smooth positive global volume. -/
theorem integrable_toReal_of_genuine_thetaPsh {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (θ : SmoothRealForm n M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    Integrable (fun x => (u x).toReal) μ :=
  integrable_toReal_of_genuine_quasiPsh μ hμ u hu.quasiPshPotential

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability
