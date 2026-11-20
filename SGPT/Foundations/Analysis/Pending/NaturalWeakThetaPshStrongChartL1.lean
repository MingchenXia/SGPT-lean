import SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshWeightedAbsolute
import SGPT.Foundations.Analysis.PositiveDistributionMeasure

/-!
# Genuine canonical chart-local L1 from original weak theta-PSH reads

The existing compact native test is constructed internally. Pole values
remain in the actual canonical distance; their true almost-everywhere
finite loci alone justify the real weighted upper comparison.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshStrongChartL1

open FirstPass NaturalWeakThetaPshWeightedAbsolute

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Original bounded-family native weak chart convergence is genuine canonical chart-local L1 convergence. -/
theorem manifoldL1LocallyTendsto_of_chart_weak_tests
    {ι : Type*} [Countable ι] {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n) u l v := by
  intro e K hK hKe
  let Ω : Opens (ComplexModel n) := ⟨e.val.target, e.val.open_target⟩
  obtain ⟨φ, hφ, hφK⟩ := exists_nonneg_testFunction_one_le_on_compact (Ω := Ω) hK hKe
  have hAbs := tendsto_native_weighted_abs_of_chart_weak_tests hu hv hlim hC e φ hφ
  have hui (i : ι) : Integrable
      (fun z => φ z * (chartFunction (u i) e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hvi : Integrable (fun z => φ z * (chartFunction v e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hv.quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hFi (i : ι) : Integrable
      (fun z => φ z * ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)) volume :=
    ((hui i).sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (u i) e z).toReal - φ z * (chartFunction v e z).toReal = _
      ring))
  have hWi (i : ι) : Integrable
      (fun z => φ z * |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) volume :=
    (hFi i).abs.congr (Eventually.of_forall (fun z => by
      change |φ z * ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)| = _
      rw [abs_mul, abs_of_nonneg (hφ z)]))
  have hbound (i : ι) : chartL1EDistance (u i) v e K ≤
      ENNReal.ofReal (∫ z, φ z *
        |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume) := by
    rw [chartL1EDistance]
    calc
      (∫⁻ z in K, canonicalERealAbsDiff (chartFunction (u i) e z) (chartFunction v e z) ∂volume)
          = ∫⁻ z in K, ENNReal.ofReal
            |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hKe
          ((hu i).quasiPshPotential.ae_finite_chart e),
          ae_restrict_of_ae_restrict_of_subset hKe (hv.quasiPshPotential.ae_finite_chart e)]
          with z huz hvz
        simpa only [EReal.coe_toReal huz.1 huz.2, EReal.coe_toReal hvz.1 hvz.2] using
          canonicalERealAbsDiff_coe_coe (chartFunction (u i) e z).toReal
            (chartFunction v e z).toReal
      _ ≤ ∫⁻ z in K, ENNReal.ofReal (φ z *
          |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
        exact ENNReal.ofReal_le_ofReal
          (le_mul_of_one_le_left (abs_nonneg _) (hφK z hz))
      _ ≤ ∫⁻ z, ENNReal.ofReal (φ z *
          |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (hWi i)
        (Eventually.of_forall (fun z => mul_nonneg (hφ z) (abs_nonneg _)))).symm
  have hupper : Tendsto (fun i => ENNReal.ofReal (∫ z, φ z *
      |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hAbs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound

end SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshStrongChartL1
