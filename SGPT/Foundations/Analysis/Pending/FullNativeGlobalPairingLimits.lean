import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity
import SGPT.Foundations.Analysis.Pending.SmoothTopFormChartIntegration
import SGPT.Foundations.Analysis.Pending.XiaoGauduchonIntegration

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.FullNativeGlobalPairingLimits

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ProductTestForms
  ChartPartition ActualWeightedGlobalFormChartTests ActualCompactGlobalPairingCalibration
  CanonicalSmoothCurrentDensity CanonicalCurrentFrame ConstantFormProducts
  IntegrationCurrent TopDegreeDensity XiaoChartLocalization GlobalCurrents XiaoComplexProducts XiaoGauduchonIntegration

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Every full chart-test limit passes every global smooth complementary test,
using a finite partition and all its tests produced internally. -/
theorem tendsto_pairing {ι : Type*} {F : Filter ι} {k : CurrentDegree n}
    (T : ι → GlobalCurrent n M k) (S : GlobalCurrent n M k)
    (hlim : ∀ (e : ComplexChart n M)
      (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val)),
      Tendsto (fun i => (T i).inChart e η) F (𝓝 (S.inChart e η)))
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    Tendsto (fun i => pairingLM (T i) γ) F (𝓝 (pairingLM S γ)) := by
  classical
  obtain ⟨r, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin r → ComplexChart n M := fun j => complexChartAt (idx j)
  have htests (j : Fin r) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e j))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e j).val.target.indicator
          (fun y => χ j ((e j).val.symm y) • γ.coeff (e j) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e j) γ (χ j) (hχ j) (hχc j) (hχs j)
    exact ⟨η, hη⟩
  choose η hη using htests
  have hsum (Q : GlobalCurrent n M k) :
      pairingLM Q γ = ∑ j, Q.inChart (e j) (η j) :=
    pairing_eq_sum Q γ r e χ hχ hχc hχs hχ1 η hη
  simp_rw [hsum]
  exact tendsto_finsetSum Finset.univ fun j _ => hlim (e j) (η j)

/-- The complete complementary-degree native pairing of a smooth current is
its actual Kähler-volume wedge integral, with no type restriction on the test. -/
theorem pairing_smoothGlobalCurrent_eq_integral {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (w : PositiveClasses.KahlerBackground (m + 1) M) {k : CurrentDegree (m + 1)}
    (a : SmoothRealForm (m + 1) M k.val)
    (γ : SmoothRealForm (m + 1) M
      (Module.finrank ℝ (ComplexModel (m + 1)) - k.val)) :
    pairingLM (smoothGlobalCurrent (canonicalBasis (m + 1)) a) γ =
      ∫ x, topRatio w.form.val
        (exteriorProductTo
          (by have hk := k.is_lt; rw [← complexModel_real_finrank (m + 1)]; omega)
          a γ) x ∂(kahlerVolume w) := by
  classical
  have hdeg : k.val + (Module.finrank ℝ (ComplexModel (m + 1)) - k.val) =
      2 * (m + 1) := by
    have hk := k.is_lt
    rw [← complexModel_real_finrank (m + 1)]
    omega
  let Φ := exteriorProductTo hdeg a γ
  obtain ⟨r, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m + 1)
      (fun x : M => (⟨(complexChartAt (n := m + 1) x).val.source,
        (complexChartAt (n := m + 1) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin r → ComplexChart (m + 1) M := fun j => complexChartAt (idx j)
  have htests (j : Fin r) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e j))
          (Module.finrank ℝ (ComplexModel (m + 1)) - k.val),
        ∀ z, η z = (e j).val.target.indicator
          (fun y => χ j ((e j).val.symm y) • γ.coeff (e j) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e j) γ (χ j) (hχ j) (hχc j) (hχs j)
    exact ⟨η, hη⟩
  choose η hη using htests
  have hpiece (j : Fin r) :
      (smoothGlobalCurrent (canonicalBasis (m + 1)) a).inChart (e j) (η j) =
        ∫ x, topRatio w.form.val (smulFun (χ j) (hχ j) Φ) x ∂(kahlerVolume w) := by
    rw [smoothGlobalCurrent_apply_eq_integral_topDensity,
      SmoothTopFormChartIntegration.integral_topRatio_smulFun_eq_chart_integral
        w (e j) (χ j) (hχ j) (hχs j)]
    apply integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ (e j).val.target
    · rw [hη j z, indicator_of_mem hz, localizedCoeff, indicator_of_mem hz,
        exteriorProductTo_coeff, wedgeTo_smul_right]
    · rw [hη j z, indicator_of_notMem hz, localizedCoeff, indicator_of_notMem hz,
        wedgeTo_zero_right, topDensity_zero]
  calc
    _ = ∑ j, (smoothGlobalCurrent (canonicalBasis (m + 1)) a).inChart (e j) (η j) :=
      pairing_eq_sum _ γ r e χ hχ hχc hχs hχ1 η hη
    _ = ∑ j, ∫ x, topRatio w.form.val (smulFun (χ j) (hχ j) Φ) x ∂(kahlerVolume w) :=
      Finset.sum_congr rfl fun j _ => hpiece j
    _ = ∫ x, ∑ j, topRatio w.form.val (smulFun (χ j) (hχ j) Φ) x ∂(kahlerVolume w) :=
      (integral_finsetSum _ fun j _ => integrable_topRatio w _).symm
    _ = _ := by
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp_rw [SmoothCurrentTraceMeasure.topRatio_smulFun]
      rw [← Finset.sum_mul, hχ1, one_mul]

end SGPT.Foundations.Analysis.Pending.FullNativeGlobalPairingLimits
