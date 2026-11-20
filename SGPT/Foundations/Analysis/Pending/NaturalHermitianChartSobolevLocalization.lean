import SGPT.Foundations.Analysis.Pending.NaturalHermitianCutoffDifferentialEnergy

/-! # Genuine integrated chart localization into original coefficient Sobolev spaces -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianChartSobolevLocalization

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalHermitianFirstOrderCoefficients NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianMetricCoefficients NaturalHermitianCodifferential
  NaturalHermitianLocalGarding NaturalHermitianWeightedLocalGarding
  NaturalHermitianCutoffDifferentialEnergy NaturalChartCutoffCoefficientTests
  NaturalHermitianFrozenCoefficientSobolev NaturalVectorCoefficientSobolev
  NaturalScalarSobolevBasisGradient NaturalHermitianOrthonormalFormBasis

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (q : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual original smooth differentials give true weighted energy continuity on every original chart target. -/
theorem weightedChartEnergy_original_continuousOn
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (α : SmoothRealForm n M q) : ContinuousOn (weightedChartEnergy w e q (α.coeff e)) e.val.target := by
  have hA := (α.smooth e).continuousOn
  have hd := (α.exteriorDerivative.smooth e).continuousOn
  have hδ := ((coderivativeForm w hw q α).smooth e).continuousOn
  have hAA := ((weightedFormMetric_smooth w hw e q).continuousOn.clm_apply hA).clm_apply hA
  have hdd := ((weightedFormMetric_smooth w hw e (q + 1)).continuousOn.clm_apply hd).clm_apply hd
  have hδδ := ((weightedFormMetric_smooth w hw e (q - 1)).continuousOn.clm_apply hδ).clm_apply hδ
  apply ((hAA.add hdd).add hδδ).congr
  intro x _
  rw [weightedChartEnergy, localCodifferential_eq_original_coeff w hw]
  rfl

/-- Actual compact restriction and genuine local finiteness internally integrate the original form energy. -/
theorem integrable_weightedChartEnergy_original_restrict
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (α : SmoothRealForm n M q) :
    Integrable (weightedChartEnergy w e q (α.coeff e)) (volume.restrict K) :=
  ContinuousOn.integrableOn_compact K.isCompact
    ((weightedChartEnergy_original_continuousOn w hw e q α).mono hK)

/-- Whole native value and both genuine differential fields have their actual three internally integrable energies. -/
theorem integrable_weightedChartEnergy_native
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (η : 𝓓_{K}(ComplexModel n, FormCoefficients n q)) :
    (Integrable (fun x => weightedFormMetric w e q x (η x) (η x)) volume ∧
      Integrable (fun x => weightedFormMetric w e (q + 1) x (extDeriv η x) (extDeriv η x)) volume ∧
      Integrable (fun x => weightedFormMetric w e (q - 1) x
        (localCodifferential w e q η x) (localCodifferential w e q η x)) volume) ∧
    Integrable (weightedChartEnergy w e q η) volume ∧
      (∫ x, weightedChartEnergy w e q η x) =
        (∫ x, weightedFormMetric w e q x (η x) (η x)) +
        (∫ x, weightedFormMetric w e (q + 1) x (extDeriv η x) (extDeriv η x)) +
        (∫ x, weightedFormMetric w e (q - 1) x
          (localCodifferential w e q η x) (localCodifferential w e q η x)) := by
  have hs : tsupport (η : ComplexModel n → FormCoefficients n q) ⊆ e.val.target :=
    η.tsupport_subset.trans hK
  have hA2 : ContDiff ℝ 2 (η : ComplexModel n → FormCoefficients n q) :=
    η.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hdCont : Continuous (extDeriv η) :=
    T.continuous.comp (η.contDiff.continuous_fderiv (by simp))
  have hcD : HasCompactSupport (extDeriv η) :=
    NaturalHermitianFrozenHodgeEnergy.hasCompactSupport_clm T (η.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hsD : tsupport (extDeriv η) ⊆ e.val.target := (tsupport_extDeriv_subset q η).trans hs
  have hδCont := (localCodifferential_contDiff_of_chart_support w hw e q η hA2 hs).continuous
  have hcδ : HasCompactSupport (localCodifferential w e q η) :=
    η.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_localCodifferential_subset w e q η)
  have hsδ : tsupport (localCodifferential w e q η) ⊆ e.val.target :=
    (tsupport_localCodifferential_subset w e q η).trans hs
  have hA := integrable_weighted_chart_energy volume w hw e q η η.continuous η.hasCompactSupport hs
  have hd := integrable_weighted_chart_energy volume w hw e (q + 1) (extDeriv η) hdCont hcD hsD
  have hδ := integrable_weighted_chart_energy volume w hw e (q - 1)
    (localCodifferential w e q η) hδCont hcδ hsδ
  refine ⟨⟨hA, hd, hδ⟩, (hA.add hd).add hδ, ?_⟩
  change (∫ x, weightedFormMetric w e q x (η x) (η x) +
    weightedFormMetric w e (q + 1) x (extDeriv η x) (extDeriv η x) +
    weightedFormMetric w e (q - 1) x (localCodifferential w e q η x) (localCodifferential w e q η x)) = _
  calc
    _ = (∫ x, weightedFormMetric w e q x (η x) (η x) +
      weightedFormMetric w e (q + 1) x (extDeriv η x) (extDeriv η x)) +
      (∫ x, weightedFormMetric w e (q - 1) x
        (localCodifferential w e q η x) (localCodifferential w e q η x)) := integral_add (hA.add hd) hδ
    _ = _ := by rw [integral_add hA hd]

/-- The actual pointwise cutoff bound integrates internally against the same original restricted Haar measure. -/
theorem exists_integrated_weighted_cutoff_control
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
      ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
        (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ C > 0, ∀ (α : SmoothRealForm n M q),
        Integrable (weightedChartEnergy w e q (chartCutoffTest e K (hK.trans hball) φ α)) volume ∧
        Integrable (weightedChartEnergy w e q (α.coeff e)) (volume.restrict K) ∧
        (∫ x, weightedChartEnergy w e q (chartCutoffTest e K (hK.trans hball) φ α) x) ≤
          C * (∫ x, weightedChartEnergy w e q (α.coeff e) x ∂volume.restrict K) := by
  obtain ⟨r, hr, hball, hcontrol⟩ := exists_original_weighted_cutoff_energy_control w hw e q z hz
  refine ⟨r, hr, hball, ?_⟩
  intro K hK φ
  obtain ⟨C, hC, hbound⟩ := hcontrol K hK φ
  refine ⟨C, hC, ?_⟩
  intro α
  let T := chartCutoffTest e K (hK.trans hball) φ α
  have hnative := integrable_weightedChartEnergy_native w hw e q K (hK.trans hball) T
  have hα := integrable_weightedChartEnergy_original_restrict w hw e q K (hK.trans hball) α
  have hindicator : (K : Set (ComplexModel n)).indicator (weightedChartEnergy w e q T) =
      weightedChartEnergy w e q T := by
    funext x
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, (hbound α).2 x hx]
  have hrestrict : (∫ x, weightedChartEnergy w e q T x) =
      ∫ x, weightedChartEnergy w e q T x ∂volume.restrict K := by
    rw [← hindicator, integral_indicator K.isCompact.isClosed.measurableSet]
    rw [hindicator]
  refine ⟨hnative.2.1, hα, ?_⟩
  rw [hrestrict, ← integral_const_mul]
  apply integral_mono_ae hnative.2.1.restrict (hα.const_mul C)
  filter_upwards [ae_restrict_mem K.isCompact.isClosed.measurableSet] with x hx
  exact (hbound α).1 x hx

/-- True weighted Gårding and original finite-coordinate norm control internally bound the literal native frozen-form jet. -/
theorem exists_original_chart_coefficient_jet_bound
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ C > 0, ∀ (α : SmoothRealForm n M q),
          ‖fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q volume K
            (chartCutoffTest e K (hK.trans hball) φ α)‖ ^ 2 ≤
            C * (∫ x, weightedChartEnergy w e q (α.coeff e) x ∂volume.restrict K) := by
  classical
  obtain ⟨b, hb, ho, rG, hrG, CG, hCG, hballG, hG⟩ :=
    exists_original_weighted_local_garding_estimate w hw e z hz q
  obtain ⟨rC, hrC, hballC, hcutoff⟩ := exists_integrated_weighted_cutoff_control w hw e q z hz
  let r := min rG rC
  have hr : 0 < r := lt_min hrG hrC
  have hbrG : Metric.ball z r ⊆ Metric.ball z rG := Metric.ball_subset_ball (min_le_left _ _)
  have hbrC : Metric.ball z r ⊆ Metric.ball z rC := Metric.ball_subset_ball (min_le_right _ _)
  have hball : Metric.ball z r ⊆ e.val.target := hbrG.trans hballG
  let c := metricFormBasis (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q
  have hc : 0 ≤ basisGradientConstant c := basisGradientConstant_nonneg c
  have hcp : 0 < 1 + basisGradientConstant c := by linarith
  refine ⟨b, hb, ho, r, hr, hball, ?_⟩
  intro K hK φ
  obtain ⟨Cφ, hCφ, hφ⟩ := hcutoff K (hK.trans hbrC) φ
  refine ⟨(1 + basisGradientConstant c) * CG * Cφ, mul_pos (mul_pos hcp hCG) hCφ, ?_⟩
  intro α
  let T := chartCutoffTest e K (hK.trans hball) φ α
  have hT2 : ContDiff ℝ 2 (T : ComplexModel n → FormCoefficients n q) :=
    T.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hTG := hG T hT2 T.hasCompactSupport (T.tsupport_subset.trans (hK.trans hbrG))
  have hTE := integrable_weightedChartEnergy_native w hw e q K (hK.trans hball) T
  have hTC := (hφ α).2.2
  have hJ : ‖fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2
      b q volume K T‖ ^ 2 ≤ basisGradientConstant c *
        ((∫ x, ‖T x‖ ^ 2) + ∑ i, ∫ x, ‖fderiv ℝ T x (b i)‖ ^ 2) :=
    nativeVectorCoefficientJet_norm_sq_le K c volume b T
  have hnonneg : 0 ≤ (∫ x, ‖T x‖ ^ 2) + ∑ i, ∫ x, ‖fderiv ℝ T x (b i)‖ ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => sq_nonneg _)
  calc
    _ ≤ basisGradientConstant c *
        ((∫ x, ‖T x‖ ^ 2) + ∑ i, ∫ x, ‖fderiv ℝ T x (b i)‖ ^ 2) := hJ
    _ ≤ (1 + basisGradientConstant c) *
        ((∫ x, ‖T x‖ ^ 2) + ∑ i, ∫ x, ‖fderiv ℝ T x (b i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ ≤ (1 + basisGradientConstant c) *
        (CG * ((∫ x, weightedFormMetric w e q x (T x) (T x)) +
          (∫ x, weightedFormMetric w e (q + 1) x (extDeriv T x) (extDeriv T x)) +
          (∫ x, weightedFormMetric w e (q - 1) x
            (localCodifferential w e q T x) (localCodifferential w e q T x)))) :=
      mul_le_mul_of_nonneg_left hTG.2.2 hcp.le
    _ = (1 + basisGradientConstant c) * (CG * (∫ x, weightedChartEnergy w e q T x)) := by
      rw [hTE.2.2]
    _ ≤ (1 + basisGradientConstant c) * (CG *
        (Cφ * (∫ x, weightedChartEnergy w e q (α.coeff e) x ∂volume.restrict K))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTC hCG.le) hcp.le
    _ = _ := by ring

/-- Genuine fixed-form Rellich and the internally produced jet bound give compact closure of every energy-bounded local coefficient family. -/
theorem exists_original_energy_bounded_local_coefficient_values_precompact
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)) (R : ℝ),
          IsCompact (closure ((fun α : SmoothRealForm n M q => fixedFormValueCLM b q volume K
            (fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q volume K
              (chartCutoffTest e K (hK.trans hball) φ α))) ''
            {α | (∫ x, weightedChartEnergy w e q (α.coeff e) x ∂volume.restrict K) ≤ R})) := by
  classical
  obtain ⟨b, hb, ho, r, hr, hball, hjet⟩ := exists_original_chart_coefficient_jet_bound w hw e q z hz
  refine ⟨b, hb, ho, r, hr, hball, ?_⟩
  intro K hK φ R
  obtain ⟨C, hC, hbound⟩ := hjet K hK φ
  let S := Real.sqrt (C * (max R 0 + 1))
  have hSpos : 0 < C * (max R 0 + 1) := mul_pos hC (by have := le_max_right R 0; linarith)
  have hSn : 0 ≤ S := Real.sqrt_nonneg _
  have hSs : S ^ 2 = C * (max R 0 + 1) := Real.sq_sqrt hSpos.le
  have hcompact := isCompact_fixedFormValue_image_closedBall_closure b q volume K S
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro y ⟨α, hα, rfl⟩
  let J := fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q volume K
    (chartCutoffTest e K (hK.trans hball) φ α)
  refine ⟨J, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hJ : ‖J‖ ^ 2 ≤ C * (max R 0 + 1) := by
    calc
      _ ≤ C * (∫ x, weightedChartEnergy w e q (α.coeff e) x ∂volume.restrict K) := hbound α
      _ ≤ C * R := mul_le_mul_of_nonneg_left hα hC.le
      _ ≤ C * (max R 0 + 1) := mul_le_mul_of_nonneg_left
        (by have := le_max_left R 0; linarith) hC.le
  nlinarith only [hJ, hSs, hSn, norm_nonneg J]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianChartSobolevLocalization
