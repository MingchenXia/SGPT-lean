import SGPT.Foundations.Analysis.Pending.NaturalHermitianChartSobolevLocalization
import SGPT.Foundations.Analysis.Pending.NaturalHermitianGraphEnergy

/-! # Actual original chart localization controlled by the genuine graph norm -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianChartGraphEnergy

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalHermitianFirstOrderCoefficients NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianMetricCoefficients NaturalHermitianCodifferential
  NaturalHermitianLocalGarding NaturalHermitianWeightedLocalGarding
  NaturalHermitianCutoffDifferentialEnergy NaturalChartCutoffCoefficientTests
  NaturalHermitianFrozenCoefficientSobolev NaturalVectorCoefficientSobolev
  NaturalScalarSobolevBasisGradient NaturalHermitianOrthonormalFormBasis
  NaturalHermitianChartSobolevLocalization NaturalHermitianVolumeMeasure NaturalHermitianFormL2
  NaturalHermitianGraphEnergy FirstPass.PositiveClasses NaturalHermitianHodgeStar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
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

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual compact restricted chart density gives the exact original weighted scalar integral. -/
theorem integral_weighted_original_chart_eq_density
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (α : SmoothRealForm n M q) :
    Integrable (fun y => weightedFormMetric w e q y (α.coeff e y) (α.coeff e y)) (volume.restrict K) ∧
    Integrable (fun y => formMetricCoefficients w e y q (α.coeff e y) (α.coeff e y))
      ((chartDensityMeasure w e).restrict K) ∧
    (∫ y, weightedFormMetric w e q y (α.coeff e y) (α.coeff e y) ∂volume.restrict K) =
      ∫ y, formMetricCoefficients w e y q (α.coeff e y) (α.coeff e y)
        ∂(chartDensityMeasure w e).restrict K := by
  let ρ := fun y => ENNReal.ofReal (metricVolumeDensity w e y)
  let f := fun y => formMetricCoefficients w e y q (α.coeff e y) (α.coeff e y)
  let g := fun y => weightedFormMetric w e q y (α.coeff e y) (α.coeff e y)
  have hKm : MeasurableSet (K : Set (ComplexModel n)) := K.isCompact.isClosed.measurableSet
  have hν : (chartDensityMeasure w e).restrict K = (volume.restrict K).withDensity ρ := by
    rw [chartDensityMeasure, restrict_withDensity hKm, Measure.restrict_restrict hKm,
      inter_eq_left.mpr hK]
  have hρ : AEMeasurable ρ (volume.restrict K) :=
    (((metricVolumeDensity_smooth w e).continuousOn.mono hK).aemeasurable hKm).ennreal_ofReal
  have hfin : ∀ᵐ y ∂volume.restrict K, ρ y < (⊤ : ENNReal) :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hread : (fun y => (ρ y).toReal • f y) =ᵐ[volume.restrict K] g := by
    filter_upwards [ae_restrict_mem hKm] with y hy
    simp only [ρ, ENNReal.toReal_ofReal (metricVolumeDensity_positive w hw e y (hK hy)).le,
      smul_eq_mul, f, g, weightedFormMetric_apply]
  have hgi : Integrable g (volume.restrict K) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((((weightedFormMetric_smooth w hw e q).continuousOn.clm_apply
        (α.smooth e).continuousOn).clm_apply (α.smooth e).continuousOn).mono hK)
  have hwi : Integrable (fun y => (ρ y).toReal • f y) (volume.restrict K) := hgi.congr hread.symm
  have hfi : Integrable f ((volume.restrict K).withDensity ρ) :=
    (integrable_withDensity_iff_integrable_smul₀' hρ hfin).mpr hwi
  have he := integral_withDensity_eq_integral_toReal_smul₀ hρ hfin f
  rw [integral_congr_ae hread] at he
  refine ⟨hgi, ?_, ?_⟩
  · simpa only [hν] using hfi
  · simpa only [hν] using he.symm

variable [CompactSpace M]

/-- The genuine original global volume and whole scalar readback internally bound the restricted chart tensor energy. -/
theorem integral_weighted_original_chart_le_integralPair
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (α : SmoothRealForm n M q) :
    (∫ y, weightedFormMetric w e q y (α.coeff e y) (α.coeff e y) ∂volume.restrict K) ≤
      integralPair w hw α α := by
  let μ := hermitianVolumeMeasure w hw
  let ν := chartDensityMeasure w e
  let f := fun y => formMetricCoefficients w e y q (α.coeff e y) (α.coeff e y)
  let p := pointwisePair w α α
  have hmap : Measure.map e.val.symm ν = μ.restrict e.val.source := by
    simpa only [chartVolumeMeasure] using (hermitianVolumeMeasure_restrict_chart w hw e).symm
  have hinverse : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous (volume.restrict e.val.target)
        (fun y => ENNReal.ofReal (metricVolumeDensity w e y)))
  have hpi : Integrable p μ := pointwisePair_integrable w hw α α
  have hpm : AEStronglyMeasurable p (Measure.map e.val.symm ν) := by
    rw [hmap]
    exact hpi.aestronglyMeasurable.restrict
  have hgi : Integrable (p ∘ e.val.symm) ν :=
    (integrable_map_measure hpm hinverse).mp (by rw [hmap]; exact hpi.restrict)
  have htarget : ∀ᵐ y ∂ν, y ∈ e.val.target :=
    (withDensity_absolutelyContinuous (volume.restrict e.val.target)
      (fun y => ENNReal.ofReal (metricVolumeDensity w e y))).ae_le
        (ae_restrict_mem e.val.open_target.measurableSet)
  have hread : (p ∘ e.val.symm) =ᵐ[ν] f := htarget.mono fun y hy =>
    pointwisePair_chart w hw α α e y hy
  have hfi : Integrable f ν := hgi.congr hread
  have hfn : 0 ≤ᵐ[ν] f := by
    filter_upwards [hread] with y hy
    rw [← hy]
    exact pointwisePair_self_nonneg w hw α (e.val.symm y)
  have hνeq : (∫ y, f y ∂ν) = ∫ x, p x ∂μ.restrict e.val.source := by
    calc
      _ = ∫ y, p (e.val.symm y) ∂ν := (integral_congr_ae hread).symm
      _ = ∫ x, p x ∂Measure.map e.val.symm ν := (integral_map hinverse hpm).symm
      _ = _ := by rw [hmap]
  have hρ := integral_weighted_original_chart_eq_density w hw e q K hK α
  calc
    _ = ∫ y, f y ∂ν.restrict K := hρ.2.2
    _ ≤ ∫ y, f y ∂ν := integral_mono_measure Measure.restrict_le_self hfn hfi
    _ = ∫ x, p x ∂μ.restrict e.val.source := hνeq
    _ ≤ ∫ x, p x ∂μ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all μ fun x => pointwisePair_self_nonneg w hw α x) hpi
    _ = _ := rfl

/-- The literal original chart differential energy is bounded by the genuine three-coordinate smooth graph norm. -/
theorem integral_original_chart_energy_le_smoothGraph_norm_sq
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (α : SmoothRealForm n M q) :
    (∫ y, weightedChartEnergy w.form.val e q (α.coeff e) y ∂volume.restrict K) ≤
      ‖smoothGraph w α‖ ^ 2 := by
  let wForm : SmoothRealForm n M 2 := w.form.val
  have hwForm : wForm.IsHermitian := w.isKahler.1
  let δα := coderivativeForm wForm hwForm q α
  have hdcoeff : extDeriv (α.coeff e) = α.exteriorDerivative.coeff e := rfl
  have hδcoeff : localCodifferential wForm e q (α.coeff e) = δα.coeff e := by
    funext y
    exact localCodifferential_eq_original_coeff wForm hwForm e q α y
  have hA := (integral_weighted_original_chart_eq_density wForm hwForm e q K hK α).1
  have hd : Integrable (fun y => weightedFormMetric wForm e (q + 1) y
      (extDeriv (α.coeff e) y) (extDeriv (α.coeff e) y)) (volume.restrict K) := by
    rw [hdcoeff]
    exact (integral_weighted_original_chart_eq_density wForm hwForm e (q + 1) K hK α.exteriorDerivative).1
  have hδ : Integrable (fun y => weightedFormMetric wForm e (q - 1) y
      (localCodifferential wForm e q (α.coeff e) y)
      (localCodifferential wForm e q (α.coeff e) y)) (volume.restrict K) := by
    rw [hδcoeff]
    exact (integral_weighted_original_chart_eq_density wForm hwForm e (q - 1) K hK δα).1
  have hsum := add_le_add
    (add_le_add (integral_weighted_original_chart_le_integralPair wForm hwForm e q K hK α)
      (integral_weighted_original_chart_le_integralPair wForm hwForm e (q + 1) K hK α.exteriorDerivative))
    (integral_weighted_original_chart_le_integralPair wForm hwForm e (q - 1) K hK δα)
  change (∫ y, weightedChartEnergy wForm e q (α.coeff e) y ∂volume.restrict K) ≤ _
  calc
    _ = (∫ y, weightedFormMetric wForm e q y (α.coeff e y) (α.coeff e y) +
        weightedFormMetric wForm e (q + 1) y (extDeriv (α.coeff e) y) (extDeriv (α.coeff e) y)
          ∂volume.restrict K) +
        (∫ y, weightedFormMetric wForm e (q - 1) y
          (localCodifferential wForm e q (α.coeff e) y)
          (localCodifferential wForm e q (α.coeff e) y) ∂volume.restrict K) := integral_add (hA.add hd) hδ
    _ = (∫ y, weightedFormMetric wForm e q y (α.coeff e y) (α.coeff e y) ∂volume.restrict K) +
        (∫ y, weightedFormMetric wForm e (q + 1) y
          (extDeriv (α.coeff e) y) (extDeriv (α.coeff e) y) ∂volume.restrict K) +
        (∫ y, weightedFormMetric wForm e (q - 1) y
          (localCodifferential wForm e q (α.coeff e) y)
          (localCodifferential wForm e q (α.coeff e) y) ∂volume.restrict K) := by
      rw [integral_add hA hd]
    _ ≤ integralPair wForm hwForm α α + integralPair wForm hwForm α.exteriorDerivative α.exteriorDerivative +
        integralPair wForm hwForm δα δα := by
      rw [hdcoeff, hδcoeff]
      exact hsum
    _ = _ := (smoothGraph_norm_sq w α).symm

/-- Internally constructed native chart coefficient jets are genuinely bounded by the actual original smooth graph. -/
theorem exists_original_chart_graph_coefficient_jet_bound
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.form.val.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ C > 0, ∀ (α : SmoothRealForm n M q),
          ‖fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
            (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K (hK.trans hball) φ α)‖ ^ 2 ≤
            C * ‖smoothGraph w α‖ ^ 2 := by
  obtain ⟨b, hb, ho, r, hr, hball, hjet⟩ :=
    exists_original_chart_coefficient_jet_bound w.form.val w.isKahler.1 e q z hz
  refine ⟨b, hb, ho, r, hr, hball, ?_⟩
  intro K hK φ
  obtain ⟨C, hC, hbound⟩ := hjet K hK φ
  refine ⟨C, hC, ?_⟩
  intro α
  exact (hbound α).trans (mul_le_mul_of_nonneg_left
    (integral_original_chart_energy_le_smoothGraph_norm_sq w e q K (hK.trans hball) α) hC.le)

/-- Actual graph-bounded original smooth forms have genuinely precompact native local coefficient values. -/
theorem exists_original_graph_bounded_local_coefficient_values_precompact
    (w : KahlerBackground n M) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.form.val.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
        ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
          (φ : 𝓓_{K}(ComplexModel n, ℝ)) (R : ℝ),
          IsCompact (closure ((fun α : SmoothRealForm n M q => fixedFormValueCLM b q volume K
            (fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
              (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K (hK.trans hball) φ α))) ''
            {α | ‖smoothGraph w α‖ ^ 2 ≤ R})) := by
  classical
  obtain ⟨b, hb, ho, r, hr, hball, hjet⟩ :=
    exists_original_chart_graph_coefficient_jet_bound w e q z hz
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
  let J := fixedFormCoefficientJet (w.form.val.coeff e z) (w.isKahler.1 e z hz).1
    (w.isKahler.1 e z hz).2 b q volume K (chartCutoffTest e K (hK.trans hball) φ α)
  refine ⟨J, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hJ : ‖J‖ ^ 2 ≤ C * (max R 0 + 1) := by
    calc
      _ ≤ C * ‖smoothGraph w α‖ ^ 2 := hbound α
      _ ≤ C * R := mul_le_mul_of_nonneg_left hα hC.le
      _ ≤ C * (max R 0 + 1) := mul_le_mul_of_nonneg_left
        (by have := le_max_left R 0; linarith) hC.le
  nlinarith only [hJ, hSs, hSn, norm_nonneg J]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianChartGraphEnergy
