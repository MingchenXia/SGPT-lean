import SGPT.BBJ.CantorKernelIntegration
import SGPT.BBJ.ProjectiveScalarCurrentCalibration
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
import SGPT.Foundations.Analysis.Pending.FullNativeCurrentTraceMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory TopologicalSpace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
open NaturalThetaPshGeometricCurrent ThetaPotentialPrescribedChartReader
open ProductTestForms ActualCompactGlobalPairingCalibration
open scoped Topology ENNReal Classical Distributions ContDiff ComplexConjugate
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The SAME genuine geometric theta-plus-ddC current of the literal Cantor average. -/
def cantorNativeCurrent : GlobalCurrent 1 P1 (degreeTwo (n := 1) (by norm_num)) :=
  @thetaPotentialCurrent 0 P1 inferInstance projectiveNativeChartedSpace
    projectiveNativeComplexManifold projectiveNativeFSBackground.form.val cantorLogPotential
      isThetaPshPotential_cantorLogPotential

/-- Actual native atlas membership classifies EVERY genuine chart. -/
theorem projectiveNativeChart_exhaustive (f : ComplexChart 1 P1) :
    ∃ j : Bool, f = projectiveNativeChart j := by
  obtain ⟨j,hj⟩ := (mem_projectiveNativeAtlas_iff f.val).mp f.property
  exact ⟨j,Subtype.ext hj⟩

private theorem preferred_chart_target (j : Bool) :
    chartTarget (projectiveNativeChart j) = ⊤ := by
  apply Opens.ext
  change (projectiveModelChart j).target = univ
  simp [projectiveModelChart,projectiveQuotientScalarChart_target]

/-- Canonical coefficients read on the ENTIRE original preferred target. -/
def cantorNativePreferredCoefficients (j : Bool) :
    LocalCurrents.DistributionForm (⊤ : Opens (ComplexModel 1)) 2 :=
  LelongPoincareDivisor.restrictForm
    (cantorNativeCurrent.coefficients (canonicalBasis 1) (projectiveNativeChart j))
    (by rw [preferred_chart_target])

/-- The genuine global current's preferred coefficients equal the already produced local current. -/
theorem cantorNativePreferredCoefficients_eq (j : Bool) :
    cantorNativePreferredCoefficients j =
      projectiveFSCurvatureCurrent+cantorAverageMetricCurrent j := by
  let e := projectiveNativeChart j
  have htarget : chartTarget e = ⊤ := preferred_chart_target j
  have ht : e.val.target = univ := by
    change ((chartTarget e : Opens (ComplexModel 1)) : Set (ComplexModel 1)) = univ
    rw [htarget]; rfl
  have hpot : IsSmoothLocalPotential projectiveNativeFSBackground.form.val e
      (⊤ : Opens (ComplexModel 1)) projectiveFSPotential := by
    refine ⟨isOpen_univ,?_,contDiff_projectiveFSPotential.contDiffOn,fun _ _ => rfl⟩
    simpa only [Opens.coe_top,ht] using (subset_univ (univ : Set (ComplexModel 1)))
  obtain ⟨_,_,hL,hcoeff,_⟩ := @exists_corrected_original_chart_reader
    0 P1 inferInstance projectiveNativeChartedSpace projectiveNativeComplexManifold
      projectiveNativeFSBackground.form.val cantorLogPotential
        isThetaPshPotential_cantorLogPotential e ⊤ projectiveFSPotential hpot
  have hraw := quasiPsh_chart_ae_finite (canonicalBasis 1) (by norm_num)
    cantorLogPotential isThetaPshPotential_cantorLogPotential.quasiPshPotential e
  rw [addHaar_canonicalBasis,htarget] at hraw
  simp only [Opens.coe_top,Measure.restrict_univ] at hraw
  have hρ : LocallyIntegrableOn projectiveFSPotential (⊤ : Opens (ComplexModel 1)) volume :=
    contDiff_projectiveFSPotential.continuous.continuousOn.locallyIntegrableOn MeasurableSet.univ
  have heq : (fun z => (chartFunction cantorLogPotential e z+(projectiveFSPotential z : EReal)).toReal)
      =ᵐ[volume.restrict (⊤ : Opens (ComplexModel 1))]
        (fun z => cantorAverageDensity j z+projectiveFSPotential z) := by
    simp only [Opens.coe_top,Measure.restrict_univ]
    filter_upwards [hraw] with z hz
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),EReal.toReal_coe]
    rfl
  have hsum := regularDistribution_congr_ae_on hL
    ((locallyIntegrable_cantorAverageDensity j).add hρ) heq
  change _ = regularDistribution volume
    (fun z => cantorAverageDensity j z+projectiveFSPotential z) _ at hsum
  rw [ThetaPshChartLimitGluing.regularDistribution_add] at hsum
  change cantorNativePreferredCoefficients j = _ at hcoeff
  rw [hcoeff,hsum]
  have hadd := map_add LelongPoincareDivisor.ddCLM
    (regularDistribution volume (cantorAverageDensity j) (locallyIntegrable_cantorAverageDensity j))
    (regularDistribution volume projectiveFSPotential hρ)
  exact hadd.trans (add_comm _ _)


private theorem preferred_coefficients_apply (j : Bool) (v : Fin 2 → ComplexModel 1)
    (φ : 𝓓(chartTarget (projectiveNativeChart j), ℝ)) :
    cantorNativePreferredCoefficients j v
      (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens (ComplexModel 1)), ℝ)) =
      cantorNativeCurrent.coefficients (canonicalBasis 1) (projectiveNativeChart j) v φ := by
  unfold cantorNativePreferredCoefficients
  rw [LelongPoincareDivisor.restrictForm_apply]
  congr 1
  apply TestFunction.ext
  intro z
  rw [congrFun (testFunction_inclusion_coe
    (show (⊤ : Opens (ComplexModel 1)) ≤ chartTarget (projectiveNativeChart j) by
      rw [preferred_chart_target]) _) z]
  exact congrFun (testFunction_inclusion_coe
    (show chartTarget (projectiveNativeChart j) ≤ (⊤ : Opens (ComplexModel 1)) from le_top) φ) z

/-- Every genuine preferred-chart test reads the SAME already constructed local full current. -/
theorem cantorNativeCurrent_preferred_test (j : Bool)
    (η : LocalCurrents.TestForm (chartTarget (projectiveNativeChart j))
      (Module.finrank ℝ (ComplexModel 1)-2)) :
    cantorNativeCurrent.inChart (projectiveNativeChart j) η =
      (projectiveFSCurvatureCurrent+cantorAverageMetricCurrent j)
        ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I]
        (TestFunction.monoCLM ℝ (LocalCurrents.testCoefficientCLM projectiveCurrentEmptyTuple η) :
          𝓓((⊤ : Opens (ComplexModel 1)), ℝ)) := by
  rw [projective_scalar_current_calibration, ← preferred_coefficients_apply,
    cantorNativePreferredCoefficients_eq]

private lemma probability_integral_norm_difference (ν : Measure P1) [IsProbabilityMeasure ν]
    (f g : C(P1, ℝ)) :
    ‖(∫ x, f x ∂ν)-(∫ x, g x ∂ν)‖ ≤ ‖f-g‖ := by
  have hf : Integrable f ν := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g ν := g.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hf hg]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => f x-g x) (C := ‖f-g‖)
    (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm (f-g) x)
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using h

/-- Genuine smooth density and finite probability bounds determine the actual regular measure. -/
theorem projective_probability_eq_of_chartSmooth_integrals (ν μ : Measure P1)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] [ν.Regular] [μ.Regular]
    (h : ∀ (g : P1 → ℝ), ChartSmooth (n := 1) g →
      (∫ x, g x ∂ν) = ∫ x, g x ∂μ) : ν = μ := by
  have hcont (f : C(P1, ℝ)) : (∫ x, f x ∂ν) = ∫ x, f x ∂μ := by
    apply eq_of_forall_dist_le
    intro ε hε
    have hf : f ∈ (CurrentTraceMeasure.chartSmoothSubalgebra 1 P1).topologicalClosure := by
      rw [CurrentTraceMeasure.chartSmoothSubalgebra_topologicalClosure]
      trivial
    change f ∈ closure (CurrentTraceMeasure.chartSmoothSubalgebra 1 P1 : Set C(P1, ℝ)) at hf
    obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.mp hf (ε/4) (by positivity)
    have hnorm : ‖f-g‖ < ε/4 := by simpa only [dist_eq_norm,norm_sub_rev] using hfg
    have heq := h g (CurrentTraceMeasure.mem_chartSmoothSubalgebra.mp hg)
    have hν := probability_integral_norm_difference ν f g
    have hμ := probability_integral_norm_difference μ g f
    rw [norm_sub_rev g f] at hμ
    rw [dist_eq_norm]
    calc
      _ = ‖((∫ x, f x ∂ν)-(∫ x, g x ∂ν))+
          ((∫ x, g x ∂μ)-(∫ x, f x ∂μ))‖ := by rw [heq]; congr 1; ring
      _ ≤ ‖(∫ x, f x ∂ν)-(∫ x, g x ∂ν)‖+
          ‖(∫ x, g x ∂μ)-(∫ x, f x ∂μ)‖ := norm_add_le _ _
      _ ≤ 2*‖f-g‖ := by linarith
      _ ≤ ε := by linarith
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact hcont f.toContinuousMap

private theorem cantorComplementaryDegree :
    Module.finrank ℝ (ComplexModel 1)-(degreeTwo (n := 1) (by norm_num)).val = 2*0 := by
  change Module.finrank ℝ (ComplexModel 1)-2 = 2*0
  rw [complexModel_real_finrank]

private lemma cast_test_value {a b : ℕ} (h : a = b)
    {U : Opens (ComplexModel 1)} (η : LocalCurrents.TestForm U a) (z : ComplexModel 1) :
    CanonicalComplementaryCurrentTests.castTestDegree h η z =
      ConstantFormProducts.castForm h (η z) := by
  subst b
  rfl

private lemma cast_test_inverse {a b : ℕ} (h : a = b)
    {U : Opens (ComplexModel 1)} (η : LocalCurrents.TestForm U a) :
    CanonicalComplementaryCurrentTests.castTestDegree h.symm
      (CanonicalComplementaryCurrentTests.castTestDegree h η) = η := by
  subst b
  rfl

/-- The SAME actual Cantor current is positive on every genuine full native chart test. -/
theorem cantorNativeCurrent_full_positive
    (e : ComplexChart 1 P1)
    (η : LocalCurrents.TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel 1)-(degreeTwo (n := 1) (by norm_num)).val))
    (hη : ∀ z, z ∈ e.val.target →
      ConstantFormProducts.castForm cantorComplementaryDegree (η z) ∈
        StronglyPositiveForms.spCone 0) :
    0 ≤ cantorNativeCurrent.inChart e η := by
  obtain ⟨j,rfl⟩ := projectiveNativeChart_exhaustive e
  let α := CanonicalComplementaryCurrentTests.castTestDegree cantorComplementaryDegree η
  have hα : ∀ z, α z ∈ StronglyPositiveForms.spCone 0 := by
    intro z
    rw [show α z = ConstantFormProducts.castForm cantorComplementaryDegree (η z) from
      cast_test_value _ _ _]
    apply hη
    change z ∈ (chartTarget (projectiveNativeChart j) : Set (ComplexModel 1))
    rw [preferred_chart_target]; trivial
  have h := @thetaPotentialCurrent_full_positive 0 P1 inferInstance
    projectiveNativeChartedSpace projectiveNativeComplexManifold
      projectiveNativeFSBackground.form.val cantorLogPotential
        isThetaPshPotential_cantorLogPotential (projectiveNativeChart j) α hα
  simpa only [cantorNativeCurrent,α,cast_test_inverse] using h

/-- The actual complementary-degree functional obtained from the SAME global current. -/
def cantorNativeProductCurrent : PositiveProductCurrents.ProductCurrent 1 P1 0 :=
  (pairingLM cantorNativeCurrent).comp
    ((FullNativeCurrentTraceMeasure.castSmoothDegree cantorComplementaryDegree.symm).comp
      (testSpace 1 P1 0).subtype)

private lemma coeff_cast_degree {a b : ℕ} (h : a = b)
    (A : SmoothRealForm 1 P1 a) (e : ComplexChart 1 P1) (z : ComplexModel 1) :
    (FullNativeCurrentTraceMeasure.castSmoothDegree h A).coeff e z =
      ConstantFormProducts.castForm h (A.coeff e z) := by
  subst b
  rfl

/-- Positivity is manufactured from actual full native positivity and finite chart localization. -/
theorem cantorNativeProductCurrent_positive :
    PositiveProductCurrents.IsPositive cantorNativeProductCurrent := by
  intro φ hφ
  change 0 ≤ pairingLM cantorNativeCurrent
    (FullNativeCurrentTraceMeasure.castSmoothDegree cantorComplementaryDegree.symm
      (φ : SmoothRealForm 1 P1 (2*0)))
  apply FullNativeCurrentTraceMeasure.pairing_nonneg_of_full_positive
    cantorComplementaryDegree cantorNativeCurrent cantorNativeCurrent_full_positive
  intro e z hz
  rw [coeff_cast_degree,ConstantFormProducts.castForm_castForm,ConstantFormProducts.castForm_self]
  exact hφ e z hz

/-- The LITERAL existing RMK trace, not a selected measure satisfying a desired equation. -/
def cantorNativeTrace : Measure P1 :=
  CurrentTraceMeasure.traceMeasure projectiveNativeFSBackground
    cantorNativeProductCurrent cantorNativeProductCurrent_positive

instance cantorNativeTrace_regular : cantorNativeTrace.Regular := by
  unfold cantorNativeTrace
  infer_instance

instance cantorNativeTrace_finite : IsFiniteMeasure cantorNativeTrace := by
  unfold cantorNativeTrace
  infer_instance

/-- Exact existing trace reader for every genuinely chart-smooth scalar. -/
theorem integral_cantorNativeTrace_chartSmooth (g : P1 → ℝ) (hg : ChartSmooth (n := 1) g) :
    (∫ x, g x ∂cantorNativeTrace) = cantorNativeProductCurrent
      (CurrentTraceMeasure.smulTest g hg (PositiveProductCurrents.kahlerTest projectiveNativeFSBackground 0)) :=
  CurrentTraceMeasure.integral_traceMeasure_chartSmooth projectiveNativeFSBackground
    cantorNativeProductCurrent cantorNativeProductCurrent_positive g hg

private def cantorScalarForm (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h) :
    SmoothRealForm 1 P1
      (Module.finrank ℝ (ComplexModel 1)-(degreeTwo (n := 1) (by norm_num)).val) :=
  FullNativeCurrentTraceMeasure.castSmoothDegree cantorComplementaryDegree.symm
    (smulFun h hh (formPow projectiveNativeFSBackground.form.val 0))

private theorem cantorScalarForm_coeff (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h)
    (e : ComplexChart 1 P1) (z : ComplexModel 1) :
    (cantorScalarForm h hh).coeff e z projectiveCurrentEmptyTuple = h (e.val.symm z) := by
  rw [cantorScalarForm, coeff_cast_degree, ConstantFormProducts.castForm_apply]
  exact projective_scalar_formPow_zero_coeff _ h hh e z _

private theorem cantor_weighted_scalar_test (j : Bool) (h χ : P1 → ℝ)
    (hh : ChartSmooth (n := 1) h)
    (η : LocalCurrents.TestForm (chartTarget (projectiveNativeChart j))
      (Module.finrank ℝ (ComplexModel 1)-2))
    (hη : ∀ z, η z = (projectiveNativeChart j).val.target.indicator
      (fun y => χ ((projectiveNativeChart j).val.symm y) •
        (cantorScalarForm h hh).coeff (projectiveNativeChart j) y) z)
    (z : ComplexModel 1) :
    (TestFunction.monoCLM ℝ (LocalCurrents.testCoefficientCLM projectiveCurrentEmptyTuple η) :
      𝓓((⊤ : Opens (ComplexModel 1)), ℝ)) z =
        χ ((projectiveNativeChart j).val.symm z)*h ((projectiveNativeChart j).val.symm z) := by
  rw [congrFun (testFunction_inclusion_coe
    (show chartTarget (projectiveNativeChart j) ≤ (⊤ : Opens (ComplexModel 1)) from le_top)
    (LocalCurrents.testCoefficientCLM projectiveCurrentEmptyTuple η)) z]
  change η z projectiveCurrentEmptyTuple = _
  have hz : z ∈ (projectiveNativeChart j).val.target := by
    change z ∈ (chartTarget (projectiveNativeChart j) : Set (ComplexModel 1))
    rw [preferred_chart_target]; trivial
  rw [hη z, indicator_of_mem hz, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, cantorScalarForm_coeff]

private theorem cantor_infinity_weight_zero (χ : P1 → ℝ)
    (hsource : tsupport χ ⊆ (projectiveNativeChart true).val.source)
    (b : ℕ → Bool) (hb : cantorCode b = 0) : χ (projectiveCantorCode b) = 0 := by
  by_contra hne
  have hs := hsource (subset_tsupport χ hne)
  change projectiveCantorCode b ∈ (projectiveModelChart true).source at hs
  rw [projectiveModelChart_source, projectiveQuotientScalarChart_source] at hs
  change projectiveLineHomeomorph.symm
    (projectiveLineHomeomorph ((cantorCode b : ℂ) : OnePoint ℂ)) ∈
      projectiveInfinityChart.source at hs
  rw [Homeomorph.symm_apply_apply, projectiveInfinityChart_source] at hs
  apply hs
  rw [hb]
  rfl

/-- Actual weighted native chart testing is integration over the SAME projective Cantor codes. -/
theorem cantorNativeCurrent_weighted_test (j : Bool) (h χ : P1 → ℝ)
    (hh : ChartSmooth (n := 1) h)
    (hsource : tsupport χ ⊆ (projectiveNativeChart j).val.source)
    (η : LocalCurrents.TestForm (chartTarget (projectiveNativeChart j))
      (Module.finrank ℝ (ComplexModel 1)-2))
    (hη : ∀ z, η z = (projectiveNativeChart j).val.target.indicator
      (fun y => χ ((projectiveNativeChart j).val.symm y) •
        (cantorScalarForm h hh).coeff (projectiveNativeChart j) y) z) :
    cantorNativeCurrent.inChart (projectiveNativeChart j) η =
      ∫ b, χ (projectiveCantorCode b)*h (projectiveCantorCode b) ∂cantorBitProbability := by
  rw [cantorNativeCurrent_preferred_test]
  cases j
  · rw [cantorAverage_full_current_finite_apply]
    apply integral_congr_ae
    refine Eventually.of_forall fun b => ?_
    simp only [projectiveModelEquiv_apply_zero, map_one, one_mul, Complex.I_im, mul_one]
    rw [cantor_weighted_scalar_test false h χ hh η hη]
    change χ ((projectiveModelChart false).symm (projectiveModelEquiv (cantorCode b : ℂ)))*
      h ((projectiveModelChart false).symm (projectiveModelEquiv (cantorCode b : ℂ))) = _
    rw [movingSection_finite_root]
    rfl
  · rw [cantorAverage_full_current_infinity_apply]
    apply integral_congr_ae
    refine Eventually.of_forall fun b => ?_
    dsimp only
    by_cases hb : cantorCode b = 0
    · rw [if_pos hb, cantor_infinity_weight_zero χ hsource b hb, zero_mul]
    · rw [if_neg hb]
      simp only [projectiveModelEquiv_apply_zero, map_one, one_mul, Complex.I_im, mul_one]
      rw [cantor_weighted_scalar_test true h χ hh η hη]
      change χ ((projectiveModelChart true).symm (projectiveModelEquiv ((cantorCode b : ℂ)⁻¹)))*
        h ((projectiveModelChart true).symm (projectiveModelEquiv ((cantorCode b : ℂ)⁻¹))) = _
      rw [movingSection_infinity_root _ hb]
      rfl

/-- The actual full native scalar pairing is the literal Cantor pushforward integral. -/
theorem cantorNativeProductCurrent_smulTest (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h) :
    cantorNativeProductCurrent
      (CurrentTraceMeasure.smulTest h hh (PositiveProductCurrents.kahlerTest projectiveNativeFSBackground 0)) =
        ∫ b, h (projectiveCantorCode b) ∂cantorBitProbability := by
  change pairingLM cantorNativeCurrent (cantorScalarForm h hh) = _
  obtain ⟨m, χ, idx, hχ, -, hsource, hcompact, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := 1)
      (fun j : Bool => (⟨(projectiveNativeChart j).val.source,
        (projectiveNativeChart j).val.open_source⟩ : Opens P1))
      (fun p => by
        obtain ⟨j, hj⟩ := projectiveQuotientScalarChart_cover p
        exact ⟨j, by change p ∈ (projectiveModelChart j).source
                     rwa [projectiveModelChart_source]⟩)
  let e : Fin m → ComplexChart 1 P1 := fun i => projectiveNativeChart (idx i)
  have htests (i : Fin m) :
      ∃ η : LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel 1)-2),
        ∀ z, η z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • (cantorScalarForm h hh).coeff (e i) y) z := by
    obtain ⟨η, hη, -⟩ := ActualWeightedGlobalFormChartTests.exists_testForm
      (e i) (cantorScalarForm h hh) (χ i) (hχ i) (hcompact i) (hsource i)
    exact ⟨η, hη⟩
  choose η hη using htests
  have hi (i : Fin m) :
      Integrable (fun b => χ i (projectiveCantorCode b)*h (projectiveCantorCode b))
        cantorBitProbability :=
    (((CurrentTraceMeasure.chartSmooth_continuous (hχ i)).comp continuous_projectiveCantorCode).mul
      ((CurrentTraceMeasure.chartSmooth_continuous hh).comp continuous_projectiveCantorCode)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [pairing_eq_sum cantorNativeCurrent (cantorScalarForm h hh) m e χ
    hχ hcompact hsource hsum η hη]
  calc
    _ = ∑ i : Fin m, ∫ b, χ i (projectiveCantorCode b)*h (projectiveCantorCode b)
        ∂cantorBitProbability := by
      apply Finset.sum_congr rfl
      intro i _
      exact cantorNativeCurrent_weighted_test (idx i) h (χ i) hh (hsource i) (η i) (hη i)
    _ = ∫ b, ∑ i : Fin m, χ i (projectiveCantorCode b)*h (projectiveCantorCode b)
        ∂cantorBitProbability := (integral_finsetSum _ fun i _ => hi i).symm
    _ = ∫ b, h (projectiveCantorCode b) ∂cantorBitProbability := by
      apply integral_congr_ae
      refine Eventually.of_forall fun b => ?_
      simp only [← Finset.sum_mul, hsum, one_mul]

/-- Every genuine smooth scalar has the SAME integral for the actual trace and Cantor measure. -/
theorem integral_cantorNativeTrace_eq (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h) :
    (∫ p, h p ∂cantorNativeTrace) = ∫ p, h p ∂projectiveCantorProbability := by
  rw [integral_cantorNativeTrace_chartSmooth h hh, cantorNativeProductCurrent_smulTest h hh]
  exact (integral_map continuous_projectiveCantorCode.measurable.aemeasurable
    (CurrentTraceMeasure.chartSmooth_continuous hh).aestronglyMeasurable).symm

/-- The genuine current's actual RMK trace has mass one, derived from its scalar reader. -/
instance cantorNativeTrace_probability : IsProbabilityMeasure cantorNativeTrace where
  measure_univ := by
    have h1 : ChartSmooth (n := 1) (fun _ : P1 => (1 : ℝ)) := fun _ => contDiffOn_const
    have hm := integral_cantorNativeTrace_eq (fun _ => 1) h1
    have hreal : (cantorNativeTrace univ).toReal = 1 := by simpa [Measure.real] using hm
    rw [← ENNReal.ofReal_toReal (measure_ne_top cantorNativeTrace univ), hreal,
      ENNReal.ofReal_one]

/-- The literal native theta-plus-ddC current has precisely the already constructed Cantor trace. -/
theorem cantorNativeTrace_eq_projectiveCantorProbability :
    cantorNativeTrace = projectiveCantorProbability := by
  have : projectiveCantorProbability.Regular := by infer_instance
  exact projective_probability_eq_of_chartSmooth_integrals
    cantorNativeTrace projectiveCantorProbability integral_cantorNativeTrace_eq

/-- Exact support of the genuine current's trace. -/
theorem cantorNativeTrace_support : cantorNativeTrace.support = projectiveCantorSet := by
  rw [cantorNativeTrace_eq_projectiveCantorProbability, projectiveCantorProbability_support]

/-- The actual positive trace is atom-free, with no supplied current/measure certificate. -/
instance cantorNativeTrace_noAtoms : NullSingletonClass cantorNativeTrace := by
  rw [cantorNativeTrace_eq_projectiveCantorProbability]
  infer_instance

/-- The genuine trace support is exactly the literal averaged potential's pole set. -/
theorem cantorNativeTrace_support_eq_poles :
    cantorNativeTrace.support = {p : P1 | cantorLogPotential p = ⊥} := by
  rw [cantorNativeTrace_support]
  ext p
  exact (cantorLogPotential_eq_bot_iff p).symm

end SGPT.BBJ
