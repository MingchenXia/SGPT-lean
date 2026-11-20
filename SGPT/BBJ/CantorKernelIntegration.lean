import SGPT.BBJ.CantorLogPotential
import SGPT.BBJ.CantorProbability
import SGPT.Foundations.Analysis.DeficitIntegrability
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Distributions ContDiff ComplexConjugate

/-- The actual moving kernel at every actual code center, on either original chart. -/
def cantorChartKernel (j : Bool) (q : (ℕ → Bool) × ComplexModel 1) : EReal :=
  movingProjectiveSectionPotential (cantorCode q.1) ((projectiveModelChart j).symm q.2)

/-- The true nonnegative extended deficit retains bottom poles as infinity. -/
def cantorChartDeficit (j : Bool) (q : (ℕ → Bool) × ComplexModel 1) : ℝ≥0∞ :=
  (-cantorChartKernel j q).toENNReal

/-- The real representative is used as a density, never as the definition of a potential. -/
def cantorChartDensity (j : Bool) (q : (ℕ → Bool) × ComplexModel 1) : ℝ :=
  (cantorChartKernel j q).toReal

theorem measurable_cantorChartDeficit (j : Bool) : Measurable (cantorChartDeficit j) := by
  have hm : Measurable (fun q : (ℕ → Bool) × ComplexModel 1 => (cantorCode q.1,q.2)) :=
    (continuous_cantorCode.measurable.comp measurable_fst).prodMk measurable_snd
  have h := (measurable_movingSectionDeficit j).comp hm
  change Measurable (cantorChartDeficit j) at h
  exact h

theorem measurable_cantorChartDensity (j : Bool) : Measurable (cantorChartDensity j) := by
  have hm : Measurable (fun q : (ℕ → Bool) × ComplexModel 1 => (cantorCode q.1,q.2)) :=
    (continuous_cantorCode.measurable.comp measurable_fst).prodMk measurable_snd
  have h := (measurable_movingSectionDensity j).comp hm
  change Measurable (cantorChartDensity j) at h
  exact h

theorem cantorChartKernel_nonpos (j : Bool) (q : (ℕ → Bool) × ComplexModel 1) :
    cantorChartKernel j q ≤ 0 :=
  movingProjectiveSectionPotential_nonpos _ _

/-- The deficit equals the absolute real density only on the genuine nonpole AE set. -/
theorem cantorChartDeficit_ae_norm (j : Bool) (b : ℕ → Bool) :
    (fun z => cantorChartDeficit j (b,z)) =ᵐ[volume]
      (fun z => ENNReal.ofReal |cantorChartDensity j (b,z)|) := by
  have hne := Pending.LelongPoincareDivisor.ae_ne_zero isOpen_univ
    (movingSectionCoefficient_differentiable (cantorCode b) j).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero (cantorCode b) j z)
  simp only [Measure.restrict_univ] at hne
  filter_upwards [hne] with z hz
  have hformula : cantorChartKernel j (b,z) =
      ((Real.log (‖movingSectionCoefficient (cantorCode b) j z‖^2)-
        projectiveFSPotential z-Real.log (1+(cantorCode b)^2) : ℝ) : EReal) := by
    rw [cantorChartKernel,movingProjectiveSectionPotential_chart]
    have he : (if j then 1-(cantorCode b : ℂ)*z 0 else z 0-(cantorCode b : ℂ)) =
        movingSectionCoefficient (cantorCode b) j z := by
      simp [movingSectionCoefficient,projectiveModelEquiv_symm_apply]
    rw [he,logNormSq_of_ne_zero hz,← EReal.coe_sub,← EReal.coe_sub]
  have hn : Real.log (‖movingSectionCoefficient (cantorCode b) j z‖^2)-
      projectiveFSPotential z-Real.log (1+(cantorCode b)^2) ≤ 0 := by
    have h := cantorChartKernel_nonpos j (b,z)
    rwa [hformula,← EReal.coe_zero,EReal.coe_le_coe_iff] at h
  simp only [cantorChartDeficit,cantorChartDensity,hformula,← EReal.coe_neg,EReal.toReal_coe,
    abs_of_nonpos hn]
  rw [EReal.toENNReal,if_neg (EReal.coe_ne_top _),EReal.toReal_coe]

/-- Uniform compact spatial L1 manufactures the finite actual product deficit. -/
theorem cantorChartDeficit_lintegral_prod_lt_top (j : Bool) (K : Set (ComplexModel 1))
    (hK : IsCompact K) :
    (∫⁻ q, cantorChartDeficit j q ∂cantorBitProbability.prod (volume.restrict K)) < ⊤ := by
  obtain ⟨B,hB,huniform⟩ := movingSectionDensity_uniform_compact_L1 K hK
  have hbound (b : ℕ → Bool) :
      (∫⁻ z in K, cantorChartDeficit j (b,z)) ≤ ENNReal.ofReal B := by
    obtain ⟨hi,hle⟩ := huniform (cantorCode b) (cantorCode_nonneg b) (cantorCode_lt_half b).le j
    have hae := ae_restrict_of_ae (cantorChartDeficit_ae_norm j b) (s := K)
    rw [lintegral_congr_ae hae]
    have he := ofReal_integral_eq_lintegral_ofReal hi.norm
      (Eventually.of_forall fun z => norm_nonneg (movingSectionDensity (cantorCode b) j z))
    simp only [Real.norm_eq_abs] at he
    change (∫⁻ z in K, ENNReal.ofReal |movingSectionDensity (cantorCode b) j z|) ≤ _
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hle
  rw [lintegral_prod _ (measurable_cantorChartDeficit j).aemeasurable]
  calc
    _ ≤ ∫⁻ _ : ℕ → Bool, ENNReal.ofReal B ∂cantorBitProbability := lintegral_mono hbound
    _ = ENNReal.ofReal B := by rw [lintegral_const,measure_univ,mul_one]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Joint finiteness and product real L1 are outputs of the genuine finite-deficit theorem. -/
theorem cantorChartKernel_ae_finite_integrable (j : Bool) (K : Set (ComplexModel 1))
    (hK : IsCompact K) :
    (∀ᵐ q ∂cantorBitProbability.prod (volume.restrict K),
      cantorChartKernel j q ≠ ⊤ ∧ cantorChartKernel j q ≠ ⊥) ∧
    Integrable (cantorChartDensity j) (cantorBitProbability.prod (volume.restrict K)) ∧
    ((fun q => ((cantorChartDensity j q : ℝ) : EReal)) =ᵐ[cantorBitProbability.prod (volume.restrict K)]
      cantorChartKernel j) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hd : AEMeasurable (cantorChartDeficit j)
      (cantorBitProbability.prod (volume.restrict K)) := (measurable_cantorChartDeficit j).aemeasurable
  change AEMeasurable (fun q => (-cantorChartKernel j q).toENNReal)
    (cantorBitProbability.prod (volume.restrict K)) at hd
  have hI := cantorChartDeficit_lintegral_prod_lt_top j K hK
  change (∫⁻ q, (-cantorChartKernel j q).toENNReal ∂cantorBitProbability.prod (volume.restrict K)) < ⊤ at hI
  exact ae_finite_and_integrable_of_lintegral_deficit_lt_top
    (u := cantorChartKernel j) (C := 0) (Eventually.of_forall (cantorChartKernel_nonpos j))
    (by simpa only [EReal.coe_zero,zero_sub] using hd)
    (by simpa only [EReal.coe_zero,zero_sub] using hI)

/-- The literal actual potential's real representative in an original chart. -/
def cantorAverageDensity (j : Bool) (z : ComplexModel 1) : ℝ :=
  (cantorLogPotential ((projectiveModelChart j).symm z)).toReal

/-- Finite actual deficit is manufactured at spatial-almost-every parameter fiber. -/
theorem cantorLogIntegral_chart_ae_lt_top (j : Bool) (K : Set (ComplexModel 1))
    (hK : IsCompact K) :
    ∀ᵐ z ∂volume.restrict K, cantorLogIntegral ((projectiveModelChart j).symm z) < ⊤ := by
  have hI := cantorChartDeficit_lintegral_prod_lt_top j K hK
  rw [lintegral_prod_symm _ (measurable_cantorChartDeficit j).aemeasurable] at hI
  have hm := (measurable_cantorChartDeficit j).lintegral_prod_left'
    (μ := cantorBitProbability)
  have h := ae_lt_top' (μ := volume.restrict K) hm.aemeasurable hI.ne
  change ∀ᵐ z ∂volume.restrict K, cantorLogIntegral ((projectiveModelChart j).symm z) < ⊤ at h
  exact h

/-- A pointwise readback is legal ONLY when the original nonnegative integral is finite. -/
theorem cantorAverageDensity_eq_integral_of_lt_top (j : Bool) (z : ComplexModel 1)
    (hG : cantorLogIntegral ((projectiveModelChart j).symm z) < ⊤) :
    cantorAverageDensity j z = ∫ b, cantorChartDensity j (b,z) ∂cantorBitProbability := by
  let p := (projectiveModelChart j).symm z
  have hm := measurable_cantorLogDeficit p
  have hd : AEMeasurable (fun b : ℕ → Bool =>
      ((0 : EReal)-cantorChartKernel j (b,z)).toENNReal) cantorBitProbability := by
    simpa only [EReal.coe_zero,zero_sub,cantorLogDeficit,cantorChartKernel,p] using hm.aemeasurable
  have hI : (∫⁻ b : ℕ → Bool, ((0 : EReal)-cantorChartKernel j (b,z)).toENNReal
      ∂cantorBitProbability) < ⊤ := by
    simpa only [cantorLogIntegral,cantorLogDeficit,cantorChartKernel,EReal.coe_zero,zero_sub,p] using hG
  have he := ae_toReal_eq_const_sub_deficit_of_lintegral_lt_top
    (C := 0) (u := fun b : ℕ → Bool => cantorChartKernel j (b,z))
    (Eventually.of_forall fun b => cantorChartKernel_nonpos j (b,z)) hd hI
  have he' : (fun b : ℕ → Bool => cantorChartDensity j (b,z)) =ᵐ[cantorBitProbability]
      (fun b => -(cantorLogDeficit b p).toReal) := by
    simpa only [EReal.coe_zero,zero_sub,cantorChartDensity,cantorLogDeficit,cantorChartKernel,p] using he
  rw [integral_congr_ae he',integral_neg,
    integral_toReal hm.aemeasurable (ae_lt_top' hm.aemeasurable hG.ne)]
  simp only [cantorAverageDensity,cantorLogPotential,EReal.toReal_neg_eq,EReal.toReal_coe_ennreal,p,cantorLogIntegral]

/-- The actual spatial-AE readback and parameter fiber L1, not a polewise real formula. -/
theorem cantorAverageDensity_ae_integral (j : Bool) (K : Set (ComplexModel 1))
    (hK : IsCompact K) :
    (∀ᵐ z ∂volume.restrict K, Integrable (fun b => cantorChartDensity j (b,z)) cantorBitProbability) ∧
    (cantorAverageDensity j =ᵐ[volume.restrict K]
      fun z => ∫ b, cantorChartDensity j (b,z) ∂cantorBitProbability) ∧
    Integrable (fun z => ∫ b, cantorChartDensity j (b,z) ∂cantorBitProbability) (volume.restrict K) := by
  have hi := (cantorChartKernel_ae_finite_integrable j K hK).2.1
  refine ⟨hi.prod_left_ae,?_,hi.integral_prod_right⟩
  filter_upwards [cantorLogIntegral_chart_ae_lt_top j K hK] with z hz
  exact cantorAverageDensity_eq_integral_of_lt_top j z hz

/-- Genuine native QPSH of the actual potential supplies local L1 on the whole chart. -/
theorem locallyIntegrable_cantorAverageDensity (j : Bool) :
    LocallyIntegrableOn (cantorAverageDensity j)
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume := by
  have ht : (projectiveModelChart j).target = univ := by
    simp [projectiveModelChart,projectiveQuotientScalarChart_target]
  have h := locallyIntegrableOn_cantorLogPotential_chart (projectiveNativeChart j)
  change LocallyIntegrableOn (cantorAverageDensity j) (projectiveModelChart j).target volume at h
  rw [ht] at h
  exact h

/-- Compact spatial support manufactures WHOLE-product L1, without global L1 of H. -/
theorem integrable_cantorChart_compact_test (j : Bool) (η : ComplexModel 1 → ℝ)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    Integrable (fun q : (ℕ → Bool) × ComplexModel 1 => η q.2*cantorChartDensity j q)
      (cantorBitProbability.prod volume) := by
  let K := tsupport η
  have hK : IsCompact K := hηc
  have hi := (cantorChartKernel_ae_finite_integrable j K hK).2.1
  obtain ⟨M,hM⟩ := hη.bounded_above_of_compact_support hηc
  have hm : AEStronglyMeasurable (fun q : (ℕ → Bool) × ComplexModel 1 => η q.2)
      (cantorBitProbability.prod (volume.restrict K)) :=
    (hη.measurable.comp measurable_snd).aestronglyMeasurable
  have hw := hi.bdd_mul hm (Eventually.of_forall fun q => hM q.2)
  have hr : cantorBitProbability.prod (volume.restrict K) =
      (cantorBitProbability.prod volume).restrict (univ ×ˢ K) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := cantorBitProbability) (ν := (volume : Measure (ComplexModel 1))) univ K)
  rw [hr] at hw
  have hOn : IntegrableOn (fun q : (ℕ → Bool) × ComplexModel 1 => η q.2*cantorChartDensity j q)
      (univ ×ˢ K) (cantorBitProbability.prod volume) := hw
  apply hOn.integrable_of_forall_notMem_eq_zero
  intro q hq
  have hqK : q.2 ∉ K := fun h => hq ⟨mem_univ _,h⟩
  rw [image_eq_zero_of_notMem_tsupport hqK,zero_mul]

/-- Actual scalar compact-test Fubini with the genuine spatial-AE average readback. -/
theorem cantorAverageDensity_compact_test_fubini (j : Bool) (η : ComplexModel 1 → ℝ)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    (∫ z, η z*cantorAverageDensity j z) =
      ∫ b, (∫ z, η z*cantorChartDensity j (b,z)) ∂cantorBitProbability := by
  have hf := integrable_cantorChart_compact_test j η hη hηc
  have hae := (cantorAverageDensity_ae_integral j (tsupport η) hηc).2.1
  have he := (ae_restrict_iff' hηc.measurableSet).mp hae
  calc
    _ = ∫ z, (∫ b, η z*cantorChartDensity j (b,z) ∂cantorBitProbability) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      by_cases hzK : z ∈ tsupport η
      · rw [hz hzK,integral_const_mul]
      · rw [image_eq_zero_of_notMem_tsupport hzK]
        simp
    _ = _ := (integral_integral_swap hf).symm

/-- Parameter L1 of actual compact-test spatial integrals is also produced. -/
theorem integrable_cantorChart_compact_test_integral (j : Bool) (η : ComplexModel 1 → ℝ)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    Integrable (fun b => ∫ z, η z*cantorChartDensity j (b,z)) cantorBitProbability :=
  (integrable_cantorChart_compact_test j η hη hηc).integral_prod_left

private theorem ddC_density_apply (f : ComplexModel 1 → ℝ)
    (hf : LocallyIntegrableOn f (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume)
    (v w : ComplexModel 1) (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    LocalCurrents.ddC (regularDistribution volume f hf) ![v,w] φ =
      (-1/(4*Real.pi)) *
      ((∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • w)
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)) z * f z) -
        (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v)
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ)) z * f z)) := by
  rw [LocalCurrents.ddC_apply]
  simp [Distribution.lineDerivCLM_apply,regularDistribution_apply]

/-- The actual averaged density's local current; its L1 witness was internally produced. -/
def cantorAverageMetricCurrent (j : Bool) :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  LocalCurrents.ddC (regularDistribution volume (cantorAverageDensity j)
    (locallyIntegrable_cantorAverageDensity j))

/-- Actual scalar Fubini for the TWO transposed second-derivative tests gives full ddC. -/
theorem cantorAverageMetricCurrent_apply_integral (j : Bool) (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    cantorAverageMetricCurrent j ![v,w] φ =
      ∫ b, movingSectionMetricCurrent (cantorCode b) j ![v,w] φ ∂cantorBitProbability := by
  let ψ₁ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ) :=
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • w) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)
  let ψ₂ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ) :=
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ)
  have h₁ := cantorAverageDensity_compact_test_fubini j ψ₁ ψ₁.contDiff.continuous ψ₁.hasCompactSupport
  have h₂ := cantorAverageDensity_compact_test_fubini j ψ₂ ψ₂.contDiff.continuous ψ₂.hasCompactSupport
  have hi₁ := integrable_cantorChart_compact_test_integral j ψ₁ ψ₁.contDiff.continuous ψ₁.hasCompactSupport
  have hi₂ := integrable_cantorChart_compact_test_integral j ψ₂ ψ₂.contDiff.continuous ψ₂.hasCompactSupport
  rw [cantorAverageMetricCurrent,ddC_density_apply]
  change (-1/(4*Real.pi))*((∫ z, ψ₁ z*cantorAverageDensity j z)-
    (∫ z, ψ₂ z*cantorAverageDensity j z)) = _
  rw [h₁,h₂,← integral_sub hi₁ hi₂,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun b => (ddC_density_apply
    (movingSectionDensity (cantorCode b) j)
    (locallyIntegrable_movingSectionDensity (cantorCode b) j) v w φ).symm

/-- The actual kernel current coefficients themselves are parameter-integrable. -/
theorem integrable_movingSectionMetricCurrent_apply (j : Bool) (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    Integrable (fun b => movingSectionMetricCurrent (cantorCode b) j ![v,w] φ) cantorBitProbability := by
  let ψ₁ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ) :=
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • w) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)
  let ψ₂ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ) :=
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ)
  have hi₁ := integrable_cantorChart_compact_test_integral j ψ₁ ψ₁.contDiff.continuous ψ₁.hasCompactSupport
  have hi₂ := integrable_cantorChart_compact_test_integral j ψ₂ ψ₂.contDiff.continuous ψ₂.hasCompactSupport
  have h := (hi₁.sub hi₂).const_mul (-1/(4*Real.pi))
  convert h using 1
  funext b
  exact ddC_density_apply (movingSectionDensity (cantorCode b) j)
    (locallyIntegrable_movingSectionDensity (cantorCode b) j) v w φ

/-- Adding the SAME actual FS coefficient uses genuine probability mass one. -/
theorem cantorAverage_full_current_apply_integral (j : Bool) (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent+cantorAverageMetricCurrent j) ![v,w] φ =
      ∫ b, (projectiveFSCurvatureCurrent+movingSectionMetricCurrent (cantorCode b) j)
        ![v,w] φ ∂cantorBitProbability := by
  change projectiveFSCurvatureCurrent ![v,w] φ+cantorAverageMetricCurrent j ![v,w] φ =
    ∫ b, projectiveFSCurvatureCurrent ![v,w] φ+movingSectionMetricCurrent (cantorCode b) j ![v,w] φ
      ∂cantorBitProbability
  rw [integral_add (integrable_const _) (integrable_movingSectionMetricCurrent_apply j v w φ),
    cantorAverageMetricCurrent_apply_integral]
  simp

/-- Genuine local full-current coefficients on the original finite chart. -/
theorem cantorAverage_full_current_finite_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent+cantorAverageMetricCurrent false) ![v,w] φ =
      ∫ b, φ (projectiveModelEquiv (cantorCode b : ℂ))*(conj (v 0)*w 0).im ∂cantorBitProbability := by
  rw [cantorAverage_full_current_apply_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun b => movingSection_lelongPoincare_finite_apply (cantorCode b) v w φ

/-- Both actual infinity-chart branches, including the genuine zero-center branch. -/
theorem cantorAverage_full_current_infinity_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent+cantorAverageMetricCurrent true) ![v,w] φ =
      ∫ b, (if cantorCode b = 0 then 0 else
        φ (projectiveModelEquiv ((cantorCode b : ℂ)⁻¹))*(conj (v 0)*w 0).im) ∂cantorBitProbability := by
  rw [cantorAverage_full_current_apply_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun b => movingSection_lelongPoincare_infinity_apply (cantorCode b) v w φ

/-- The finite-chart point-evaluation integral is genuinely integrable, not a zero fallback. -/
theorem integrable_cantorAverage_point_current_finite (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    Integrable (fun b => φ (projectiveModelEquiv (cantorCode b : ℂ))*(conj (v 0)*w 0).im)
      cantorBitProbability := by
  have hi := (integrable_const (projectiveFSCurvatureCurrent ![v,w] φ)).add
    (integrable_movingSectionMetricCurrent_apply false v w φ)
  apply hi.congr
  exact Eventually.of_forall fun b => movingSection_lelongPoincare_finite_apply (cantorCode b) v w φ

/-- Even reciprocal-root test values are genuinely integrable; no inverse-code moment is needed. -/
theorem integrable_cantorAverage_point_current_infinity (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    Integrable (fun b => if cantorCode b = 0 then 0 else
      φ (projectiveModelEquiv ((cantorCode b : ℂ)⁻¹))*(conj (v 0)*w 0).im) cantorBitProbability := by
  have hi := (integrable_const (projectiveFSCurvatureCurrent ![v,w] φ)).add
    (integrable_movingSectionMetricCurrent_apply true v w φ)
  apply hi.congr
  exact Eventually.of_forall fun b => movingSection_lelongPoincare_infinity_apply (cantorCode b) v w φ

end SGPT.BBJ
