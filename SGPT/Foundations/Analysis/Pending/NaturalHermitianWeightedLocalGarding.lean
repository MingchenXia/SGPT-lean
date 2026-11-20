import SGPT.Foundations.Analysis.Pending.NaturalHermitianLocalGarding
import SGPT.Foundations.Analysis.Pending.NaturalHermitianVolumeMeasure

/-! # Actual metric-volume weights and original local Gårding estimates -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianWeightedLocalGarding

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalHermitianHodgeStar NaturalHermitianLocalGarding NaturalHermitianVolumeMeasure
  NaturalHermitianMetricCoefficients NaturalHermitianFirstOrderCoefficients
  NaturalHermitianHodgePrincipalSymbol NaturalHermitianFrozenHodgeEnergy

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

/-- The actual normalized metric-volume density multiplying the entire original form metric. -/
def weightedFormMetric (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (y : ComplexModel n) : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ :=
  metricVolumeDensity w e y • formMetricCoefficients w e y q

/-- Literal whole tensor-pair evaluation of the original weighted metric. -/
theorem weightedFormMetric_apply (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (y : ComplexModel n) (η θ : FormCoefficients n q) :
    weightedFormMetric w e q y η θ =
      metricVolumeDensity w e y * formMetricCoefficients w e y q η θ := rfl

/-- The entire weighted operator is genuinely smooth in the old bilinear operator norm. -/
theorem weightedFormMetric_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (weightedFormMetric w e q) e.val.target :=
  (metricVolumeDensity_smooth w e).smul (formMetricCoefficients_smooth w hw e q)

/-- Actual center positivity supplies the original norm coercivity for every natural degree. -/
theorem weightedFormMetric_coercive_at (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (η : FormCoefficients n q) :
    (metricVolumeDensity w e z *
      formMetricCoercivityConstant (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q) * ‖η‖ ^ 2 ≤
        weightedFormMetric w e q z η η := by
  rw [weightedFormMetric_apply, mul_assoc]
  exact mul_le_mul_of_nonneg_left (chart_form_metric_coercive w hw e z hz q η)
    (metricVolumeDensity_positive w hw e z hz).le

/-- Actual two operator evaluations bound every whole bilinear self value. -/
theorem whole_bilinear_self_norm_le (q : ℕ)
    (H : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ)
    (η : FormCoefficients n q) : |H η η| ≤ ‖H‖ * ‖η‖ ^ 2 := by
  calc
    |H η η| = ‖H η η‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖H η‖ * ‖η‖ := (H η).le_opNorm η
    _ ≤ (‖H‖ * ‖η‖) * ‖η‖ := mul_le_mul_of_nonneg_right (H.le_opNorm η) (norm_nonneg η)
    _ = _ := by ring

/-- The genuine original weighted operator produces its own local uniform degree comparison. -/
theorem exists_original_weighted_degree_comparison
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    ∃ r > 0, ∃ m > 0, ∃ M₀ > 0, Metric.ball z r ⊆ e.val.target ∧
      ∀ y ∈ Metric.ball z r, ∀ η : FormCoefficients n q,
        m * ‖η‖ ^ 2 ≤ weightedFormMetric w e q y η η ∧
          weightedFormMetric w e q y η η ≤ M₀ * ‖η‖ ^ 2 := by
  let a := metricVolumeDensity w e z *
    formMetricCoercivityConstant (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q
  have ha : 0 < a := mul_pos (metricVolumeDensity_positive w hw e z hz)
    (formMetricCoercivityConstant_pos _ _ _ q)
  let M₀ := 1 + ‖weightedFormMetric w e q z‖
  have hM : 0 < M₀ := by dsimp [M₀]; positivity
  have hP := (weightedFormMetric_smooth w hw e q).continuousOn.continuousAt
    (e.val.open_target.mem_nhds hz)
  have hDiff : ∀ᶠ y in 𝓝 z,
      ‖weightedFormMetric w e q y - weightedFormMetric w e q z‖ < a / 2 :=
    (hP.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simpa using half_pos ha))
  have hNorm : ∀ᶠ y in 𝓝 z, ‖weightedFormMetric w e q y‖ < M₀ :=
    hP.norm.eventually (gt_mem_nhds (by dsimp [M₀]; linarith))
  have hn : {y | y ∈ e.val.target ∧
      ‖weightedFormMetric w e q y - weightedFormMetric w e q z‖ < a / 2 ∧
      ‖weightedFormMetric w e q y‖ < M₀} ∈ 𝓝 z :=
    inter_mem (e.val.open_target.mem_nhds hz) (hDiff.and hNorm)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, a / 2, half_pos ha, M₀, hM, fun y hy => (hball hy).1, ?_⟩
  intro y hy η
  have hy' := hball hy
  have hc := weightedFormMetric_coercive_at w hw e z hz q η
  change a * ‖η‖ ^ 2 ≤ weightedFormMetric w e q z η η at hc
  have herror := (whole_bilinear_self_norm_le q
    (weightedFormMetric w e q y - weightedFormMetric w e q z) η).trans
      (mul_le_mul_of_nonneg_right hy'.2.1.le (sq_nonneg ‖η‖))
  have herror' : |weightedFormMetric w e q y η η - weightedFormMetric w e q z η η| ≤
      (a / 2) * ‖η‖ ^ 2 := by simpa only [sub_apply] using herror
  refine ⟨?_, ?_⟩
  · nlinarith only [hc, herror',
      neg_abs_le (weightedFormMetric w e q y η η - weightedFormMetric w e q z η η)]
  · exact (le_abs_self _).trans ((whole_bilinear_self_norm_le q _ η).trans
      (mul_le_mul_of_nonneg_right hy'.2.2.le (sq_nonneg ‖η‖)))

/-- A single internally produced neighborhood controls all three actual differential degrees. -/
theorem exists_original_weighted_metric_comparison
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    ∃ r > 0, ∃ m > 0, ∃ M₀ > 0, Metric.ball z r ⊆ e.val.target ∧
      ∀ y ∈ Metric.ball z r, ∀ k, (k = q ∨ k = q + 1 ∨ k = q - 1) →
        ∀ η : FormCoefficients n k, m * ‖η‖ ^ 2 ≤ weightedFormMetric w e k y η η ∧
          weightedFormMetric w e k y η η ≤ M₀ * ‖η‖ ^ 2 := by
  obtain ⟨r₀, hr₀, m₀, hm₀, M₀, hM₀, hball₀, h₀⟩ :=
    exists_original_weighted_degree_comparison w hw e z hz q
  obtain ⟨r₁, hr₁, m₁, hm₁, M₁, hM₁, hball₁, h₁⟩ :=
    exists_original_weighted_degree_comparison w hw e z hz (q + 1)
  obtain ⟨r₂, hr₂, m₂, hm₂, M₂, hM₂, hball₂, h₂⟩ :=
    exists_original_weighted_degree_comparison w hw e z hz (q - 1)
  let r := min r₀ (min r₁ r₂)
  let m := min m₀ (min m₁ m₂)
  let U := M₀ + M₁ + M₂
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  have hm : 0 < m := lt_min hm₀ (lt_min hm₁ hm₂)
  have hU : 0 < U := by dsimp [U]; linarith
  have hbr₀ : Metric.ball z r ⊆ Metric.ball z r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have hbr₁ : Metric.ball z r ⊆ Metric.ball z r₁ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hbr₂ : Metric.ball z r ⊆ Metric.ball z r₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hmm₀ : m ≤ m₀ := min_le_left _ _
  have hmm₁ : m ≤ m₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hmm₂ : m ≤ m₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hMU₀ : M₀ ≤ U := by dsimp [U]; linarith
  have hMU₁ : M₁ ≤ U := by dsimp [U]; linarith
  have hMU₂ : M₂ ≤ U := by dsimp [U]; linarith
  refine ⟨r, hr, m, hm, U, hU, hbr₀.trans hball₀, ?_⟩
  intro y hy k hk η
  rcases hk with rfl | rfl | rfl
  · exact ⟨(mul_le_mul_of_nonneg_right hmm₀ (sq_nonneg _)).trans (h₀ y (hbr₀ hy) η).1,
      (h₀ y (hbr₀ hy) η).2.trans (mul_le_mul_of_nonneg_right hMU₀ (sq_nonneg _))⟩
  · exact ⟨(mul_le_mul_of_nonneg_right hmm₁ (sq_nonneg _)).trans (h₁ y (hbr₁ hy) η).1,
      (h₁ y (hbr₁ hy) η).2.trans (mul_le_mul_of_nonneg_right hMU₁ (sq_nonneg _))⟩
  · exact ⟨(mul_le_mul_of_nonneg_right hmm₂ (sq_nonneg _)).trans (h₂ y (hbr₂ hy) η).1,
      (h₂ y (hbr₂ hy) η).2.trans (mul_le_mul_of_nonneg_right hMU₂ (sq_nonneg _))⟩

omit [IsComplexManifold n M] in
/-- Whole scalar self evaluation is genuinely continuous when the tensor support lies in the actual smooth target. -/
theorem continuous_supported_chart_self (e : ComplexChart n M) (q : ℕ)
    (H : ComplexModel n → FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ)
    (hH : ContinuousOn H e.val.target) (A : ComplexModel n → FormCoefficients n q)
    (hA : Continuous A) (hs : tsupport A ⊆ e.val.target) :
    Continuous (fun y => H y (A y) (A y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport A
  · have hHx := hH.continuousAt (e.val.open_target.mem_nhds (hs hx))
    exact (hHx.clm_apply hA.continuousAt).clm_apply hA.continuousAt
  · have hzero : (fun y => H y (A y) (A y)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy]
    exact continuousAt_const.congr_of_eventuallyEq hzero

/-- Actual bilinear zero evaluation preserves compact tensor support independently of off-target values. -/
theorem hasCompactSupport_chart_self (q : ℕ)
    (H : ComplexModel n → FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ)
    (A : ComplexModel n → FormCoefficients n q) (hc : HasCompactSupport A) :
    HasCompactSupport (fun y => H y (A y) (A y)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun y hy => by simp only [Pi.zero_apply] at hy; simp [hy]

/-- Genuine local regularity and compact support internally integrate the actual weighted chart energy. -/
theorem integrable_weighted_chart_energy
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (hA : Continuous A)
    (hc : HasCompactSupport A) (hs : tsupport A ⊆ e.val.target) :
    Integrable (fun y => weightedFormMetric w e q y (A y) (A y)) μ :=
  (continuous_supported_chart_self e q _ (weightedFormMetric_smooth w hw e q).continuousOn
    A hA hs).integrable_of_hasCompactSupport (hasCompactSupport_chart_self q _ A hc)

/-- The existing actual chart density measure gives exactly the original volume-weighted tensor energy. -/
theorem integral_weighted_chart_energy_eq
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (hA : Continuous A)
    (hc : HasCompactSupport A) (hs : tsupport A ⊆ e.val.target) :
    Integrable (fun y => formMetricCoefficients w e y q (A y) (A y)) (chartDensityMeasure w e) ∧
      (∫ y, weightedFormMetric w e q y (A y) (A y)) =
        ∫ y, formMetricCoefficients w e y q (A y) (A y) ∂chartDensityMeasure w e := by
  let ρ := fun y => ENNReal.ofReal (metricVolumeDensity w e y)
  let f := fun y => formMetricCoefficients w e y q (A y) (A y)
  let g := fun y => weightedFormMetric w e q y (A y) (A y)
  have hρ : AEMeasurable ρ (volume.restrict e.val.target) :=
    ((metricVolumeDensity_smooth w e).continuousOn.aemeasurable
      e.val.open_target.measurableSet).ennreal_ofReal
  have hfin : ∀ᵐ y ∂volume.restrict e.val.target, ρ y < (⊤ : ENNReal) :=
    ae_of_all _ (fun y => ENNReal.ofReal_lt_top)
  have hread : (fun y => (ρ y).toReal • f y) =ᵐ[volume.restrict e.val.target] g := by
    filter_upwards [ae_restrict_mem e.val.open_target.measurableSet] with y hy
    simp only [ρ, ENNReal.toReal_ofReal (metricVolumeDensity_positive w hw e y hy).le,
      smul_eq_mul, f, g, weightedFormMetric_apply]
  have hgi := integrable_weighted_chart_energy volume w hw e q A hA hc hs
  have hwi : Integrable (fun y => (ρ y).toReal • f y) (volume.restrict e.val.target) :=
    hgi.restrict.congr hread.symm
  have hfi : Integrable f (chartDensityMeasure w e) :=
    (integrable_withDensity_iff_integrable_smul₀' hρ hfin).mpr hwi
  refine ⟨hfi, ?_⟩
  have he := integral_withDensity_eq_integral_toReal_smul₀ hρ hfin f
  change (∫ y, f y ∂chartDensityMeasure w e) = _ at he
  rw [integral_congr_ae hread] at he
  rw [he]
  rw [← integral_indicator e.val.open_target.measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    by_cases hy : y ∈ e.val.target
    · simp only [indicator_of_mem hy, g]
    · have hAy := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
      simp only [indicator_of_notMem hy, g, hAy, map_zero])

/-- Exterior differentiation preserves the actual original closed tensor support. -/
theorem tsupport_extDeriv_subset (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) : tsupport (extDeriv A) ⊆ tsupport A := by
  apply closure_minimal _ (isClosed_tsupport A)
  intro x hx
  by_contra h
  apply hx
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ A x) = 0
  rw [fderiv_of_notMem_tsupport ℝ h]
  simp only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]

/-- Genuine variable metric and volume produce the weighted estimate in the original chart norms. -/
theorem exists_original_weighted_local_garding_estimate
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ C > 0, Metric.ball z r ⊆ e.val.target ∧
        ∀ (A : ComplexModel n → FormCoefficients n q), ContDiff ℝ 2 A →
          HasCompactSupport A → tsupport A ⊆ Metric.ball z r →
          (Integrable (fun x => ‖A x‖ ^ 2) volume ∧
            Integrable (fun x => ‖fderiv ℝ A x‖ ^ 2) volume ∧
            Integrable (fun x => ‖extDeriv A x‖ ^ 2) volume ∧
            Integrable (fun x => ‖localCodifferential w e q A x‖ ^ 2) volume ∧
            ∀ i, Integrable (fun x => ‖fderiv ℝ A x (b i)‖ ^ 2) volume) ∧
          (Integrable (fun x => weightedFormMetric w e q x (A x) (A x)) volume ∧
            Integrable (fun x => weightedFormMetric w e (q + 1) x
              (extDeriv A x) (extDeriv A x)) volume ∧
            Integrable (fun x => weightedFormMetric w e (q - 1) x
              (localCodifferential w e q A x) (localCodifferential w e q A x)) volume) ∧
          (∫ x, ‖A x‖ ^ 2) + (∑ i, ∫ x, ‖fderiv ℝ A x (b i)‖ ^ 2) ≤
            C * ((∫ x, weightedFormMetric w e q x (A x) (A x)) +
              (∫ x, weightedFormMetric w e (q + 1) x (extDeriv A x) (extDeriv A x)) +
              (∫ x, weightedFormMetric w e (q - 1) x
                (localCodifferential w e q A x) (localCodifferential w e q A x))) := by
  classical
  obtain ⟨b, hb, ho, r₀, hr₀, C₀, hC₀, hball₀, hG⟩ :=
    exists_original_local_garding_estimate volume w hw e z hz q
  obtain ⟨r₁, hr₁, m, hm, M₀, _, hball₁, hcomparison⟩ :=
    exists_original_weighted_metric_comparison w hw e z hz q
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hbr₀ : Metric.ball z r ⊆ Metric.ball z r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have hbr₁ : Metric.ball z r ⊆ Metric.ball z r₁ := Metric.ball_subset_ball (min_le_right _ _)
  have hball : Metric.ball z r ⊆ e.val.target := hbr₁.trans hball₁
  refine ⟨b, hb, ho, r, hr, C₀ / m, div_pos hC₀ hm, hball, ?_⟩
  intro A hA hc hs
  have HG := hG A hA hc (hs.trans hbr₀)
  have hDA := hA.continuous_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hdCont : Continuous (extDeriv A) := T.continuous.comp hDA
  have hcD : HasCompactSupport (extDeriv A) := hasCompactSupport_clm T (hc.fderiv (𝕜 := ℝ))
  have hsD : tsupport (extDeriv A) ⊆ Metric.ball z r := (tsupport_extDeriv_subset q A).trans hs
  have hδCont := (localCodifferential_contDiff_of_chart_support w hw e q A hA
    (hs.trans hball)).continuous
  have hcδ : HasCompactSupport (localCodifferential w e q A) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_localCodifferential_subset w e q A)
  have hsδ : tsupport (localCodifferential w e q A) ⊆ Metric.ball z r :=
    (tsupport_localCodifferential_subset w e q A).trans hs
  have hWA := integrable_weighted_chart_energy volume w hw e q A hA.continuous hc (hs.trans hball)
  have hWD := integrable_weighted_chart_energy volume w hw e (q + 1) (extDeriv A)
    hdCont hcD (hsD.trans hball)
  have hWδ := integrable_weighted_chart_energy volume w hw e (q - 1)
    (localCodifferential w e q A) hδCont hcδ (hsδ.trans hball)
  refine ⟨HG.1, ⟨hWA, hWD, hWδ⟩, ?_⟩
  have hLower (k : ℕ) (hk : k = q ∨ k = q + 1 ∨ k = q - 1)
      (F : ComplexModel n → FormCoefficients n k) (hsF : tsupport F ⊆ Metric.ball z r)
      (x : ComplexModel n) : m * ‖F x‖ ^ 2 ≤ weightedFormMetric w e k x (F x) (F x) := by
    by_cases hx : x ∈ Metric.ball z r
    · exact (hcomparison x (hbr₁ hx) k hk (F x)).1
    · have hFx := image_eq_zero_of_notMem_tsupport (fun h => hx (hsF h))
      simp only [hFx, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, map_zero]
      rfl
  have hAlower := integral_mono (HG.1.1.const_mul m) hWA
    (hLower q (Or.inl rfl) A hs)
  have hDlower := integral_mono (HG.1.2.2.1.const_mul m) hWD
    (hLower (q + 1) (Or.inr (Or.inl rfl)) (extDeriv A) hsD)
  have hδlower := integral_mono (HG.1.2.2.2.1.const_mul m) hWδ
    (hLower (q - 1) (Or.inr (Or.inr rfl)) (localCodifferential w e q A) hsδ)
  rw [integral_const_mul] at hAlower hDlower hδlower
  have hsum := add_le_add (add_le_add hAlower hDlower) hδlower
  have hsum' : m * ((∫ x, ‖A x‖ ^ 2) + (∫ x, ‖extDeriv A x‖ ^ 2) +
      (∫ x, ‖localCodifferential w e q A x‖ ^ 2)) ≤
      (∫ x, weightedFormMetric w e q x (A x) (A x)) +
      (∫ x, weightedFormMetric w e (q + 1) x (extDeriv A x) (extDeriv A x)) +
      (∫ x, weightedFormMetric w e (q - 1) x
        (localCodifferential w e q A x) (localCodifferential w e q A x)) := by
    calc
      _ = _ := by ring
      _ ≤ _ := hsum
  have hdiv := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hsum')
  calc
    _ ≤ C₀ * ((∫ x, ‖A x‖ ^ 2) + (∫ x, ‖extDeriv A x‖ ^ 2) +
        (∫ x, ‖localCodifferential w e q A x‖ ^ 2)) := HG.2
    _ ≤ C₀ * (((∫ x, weightedFormMetric w e q x (A x) (A x)) +
        (∫ x, weightedFormMetric w e (q + 1) x (extDeriv A x) (extDeriv A x)) +
        (∫ x, weightedFormMetric w e (q - 1) x
          (localCodifferential w e q A x) (localCodifferential w e q A x))) / m) :=
      mul_le_mul_of_nonneg_left hdiv hC₀.le
    _ = _ := by ring

end SGPT.Foundations.Analysis.Pending.NaturalHermitianWeightedLocalGarding
