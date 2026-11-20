import SGPT.Foundations.Analysis.Pending.NaturalHermitianFiniteChartLocalizers
import Mathlib.Algebra.Order.Chebyshev

/-! # Actual global L2 norm reconstructed from original finite chart values -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalNormReconstruction

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  NaturalHermitianSmoothFormMetric NaturalHermitianMetricCoefficients
  NaturalHermitianOrthonormalFormBasis NaturalHermitianFrozenCoefficientSobolev
  NaturalCoefficientSobolevRellich NaturalHermitianGraphEnergy NaturalHermitianFormL2
  NaturalHermitianVolumeMeasure NaturalHermitianHodgeStar NaturalHermitianWeightedLocalGarding
  NaturalHermitianLocalGarding NaturalHermitianChartGraphEnergy
  NaturalHermitianFiniteChartLocalizers NaturalChartScalarNativeCutoffs
  NaturalChartCutoffCoefficientTests ChartPartition ProductTestForms XiaoChartLocalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

local instance formNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (FormCoefficients n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (FormCoefficients n k →L[ℝ] FormCoefficients n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (k : ℕ) :
    NormedSpace ℝ (FormCoefficients n k →L[ℝ] FormCoefficients n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance graphNormedAddCommGroup (w : KahlerBackground n M) (k : ℕ) :
    NormedAddCommGroup (GraphEnergy w k) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w k)

local instance graphInnerProductSpace (w : KahlerBackground n M) (k : ℕ) :
    InnerProductSpace ℝ (GraphEnergy w k) :=
  Submodule.innerProductSpace (graphEnergySubmodule w k)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Literal original scalar multiplication of the full positive fiber pairing. -/
theorem pointwisePair_smulFun_self (w : SmoothRealForm n M 2)
    (f : M → ℝ) (hf : ChartSmooth (n := n) f) (α : SmoothRealForm n M q) (x : M) :
    pointwisePair w (smulFun f hf α) (smulFun f hf α) x =
      f x ^ 2 * pointwisePair w α α x := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  change formMetricCoefficients w e (e.val x) q
    ((smulFun f hf α).coeff e (e.val x)) ((smulFun f hf α).coeff e (e.val x)) = _
  simp only [smulFun_coeff, e.val.left_inv hx, map_smul, smul_apply, smul_eq_mul]
  change f x * (f x * pointwisePair w α α x) = f x ^ 2 * pointwisePair w α α x
  ring

/-- Genuine whole normalized-volume norm readback of an original scalar chart cutoff. -/
theorem integralPair_cutoff_eq_weighted_native (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source)
    (α : SmoothRealForm n M q) :
    let K := transportedScalarCompact e f hc hs
    let hK := transportedScalarCompact_subset_target e f hc hs
    let φ := nativeScalarChartCutoff e f hf hc hs
    integralPair w hw (smulFun f hf α) (smulFun f hf α) =
      ∫ y, weightedFormMetric w e q y (chartCutoffTest e K hK φ α y)
        (chartCutoffTest e K hK φ α y) ∂volume.restrict K := by
  classical
  let K := transportedScalarCompact e f hc hs
  let hK := transportedScalarCompact_subset_target e f hc hs
  let φ := nativeScalarChartCutoff e f hf hc hs
  let T := chartCutoffTest e K hK φ α
  let β := smulFun f hf α
  let μ := hermitianVolumeMeasure w hw
  let ν := chartDensityMeasure w e
  let p := pointwisePair w β β
  let F := fun y => formMetricCoefficients w e y q (T y) (T y)
  change (∫ x, p x ∂μ) = ∫ y, weightedFormMetric w e q y (T y) (T y) ∂volume.restrict K
  have hzero : ∀ x ∉ e.val.source, p x = 0 := by
    intro x hx
    have hfzero : f x = 0 := by
      by_contra hne
      exact hx (hs (subset_tsupport f hne))
    dsimp only [p, β]
    rw [pointwisePair_smulFun_self w f hf α x, hfzero]
    simp
  have hpindicator : e.val.source.indicator p = p := by
    funext x
    by_cases hx : x ∈ e.val.source
    · exact indicator_of_mem hx p
    · rw [indicator_of_notMem hx, hzero x hx]
  have hglobal : (∫ x, p x ∂μ) = ∫ x, p x ∂μ.restrict e.val.source := by
    calc
      _ = ∫ x, e.val.source.indicator p x ∂μ := by rw [hpindicator]
      _ = _ := integral_indicator e.val.open_source.measurableSet
  have hmap : Measure.map e.val.symm ν = μ.restrict e.val.source := by
    simpa only [chartVolumeMeasure] using (hermitianVolumeMeasure_restrict_chart w hw e).symm
  have hinverse : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous (volume.restrict e.val.target)
        (fun y => ENNReal.ofReal (metricVolumeDensity w e y)))
  have hpi : Integrable p μ := pointwisePair_integrable w hw β β
  have hpm : AEStronglyMeasurable p (Measure.map e.val.symm ν) := by
    rw [hmap]
    exact hpi.aestronglyMeasurable.restrict
  have hT : ∀ y ∈ e.val.target, T y = β.coeff e y := by
    intro y hy
    dsimp only [T, β]
    rw [chartCutoffTest_apply, nativeScalarChartCutoff_of_mem e f hf hc hs y hy,
      smulFun_coeff]
  have htarget : ∀ᵐ y ∂ν, y ∈ e.val.target :=
    (withDensity_absolutelyContinuous (volume.restrict e.val.target)
      (fun y => ENNReal.ofReal (metricVolumeDensity w e y))).ae_le
        (ae_restrict_mem e.val.open_target.measurableSet)
  have hread : (p ∘ e.val.symm) =ᵐ[ν] F := by
    filter_upwards [htarget] with y hy
    dsimp only [Function.comp_def, p, F]
    rw [pointwisePair_chart w hw β β e y hy, hT y hy]
  have hνeq : (∫ y, F y ∂ν) = ∫ x, p x ∂μ.restrict e.val.source := by
    calc
      _ = ∫ y, p (e.val.symm y) ∂ν := (integral_congr_ae hread).symm
      _ = ∫ x, p x ∂Measure.map e.val.symm ν := (integral_map hinverse hpm).symm
      _ = _ := by rw [hmap]
  have hKm : MeasurableSet (K : Set (ComplexModel n)) := K.isCompact.isClosed.measurableSet
  have hFzero : ∀ y ∉ (K : Set (ComplexModel n)), F y = 0 := by
    intro y hy
    have hTy : T y = 0 := by
      by_contra hne
      exact hy (T.tsupport_subset (subset_tsupport (T : ComplexModel n → FormCoefficients n q) hne))
    simp only [F, hTy, map_zero]
  have hFindicator : (K : Set (ComplexModel n)).indicator F = F := by
    funext y
    by_cases hy : y ∈ (K : Set (ComplexModel n))
    · exact indicator_of_mem hy F
    · rw [indicator_of_notMem hy, hFzero y hy]
  have hrestrict : (∫ y, F y ∂ν) = ∫ y, F y ∂ν.restrict K := by
    calc
      _ = ∫ y, (K : Set (ComplexModel n)).indicator F y ∂ν := by rw [hFindicator]
      _ = _ := integral_indicator hKm
  have hnread : (∫ y, F y ∂ν.restrict K) =
      ∫ y, formMetricCoefficients w e y q (β.coeff e y) (β.coeff e y) ∂ν.restrict K := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hKm] with y hy
    dsimp only [F]
    rw [hT y (hK hy)]
  have hwread : (∫ y, weightedFormMetric w e q y (T y) (T y) ∂volume.restrict K) =
      ∫ y, weightedFormMetric w e q y (β.coeff e y) (β.coeff e y) ∂volume.restrict K := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hKm] with y hy
    rw [hT y (hK hy)]
  calc
    _ = ∫ x, p x ∂μ.restrict e.val.source := hglobal
    _ = ∫ y, F y ∂ν := hνeq.symm
    _ = ∫ y, F y ∂ν.restrict K := hrestrict
    _ = ∫ y, formMetricCoefficients w e y q (β.coeff e y) (β.coeff e y) ∂ν.restrict K := hnread
    _ = ∫ y, weightedFormMetric w e q y (β.coeff e y) (β.coeff e y) ∂volume.restrict K :=
      (integral_weighted_original_chart_eq_density w hw e q K hK β).2.2.symm
    _ = _ := hwread.symm

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The compact entire weighted metric and the genuine frozen old-norm coercivity internally give its comparison constant. -/
theorem exists_compact_chart_metric_upper (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (k : ℕ) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    ∃ C > 0, ∀ y ∈ (K : Set (ComplexModel n)), ∀ η : FormCoefficients n k,
      weightedFormMetric w e k y η η ≤ C * formMetricCoefficients w e z k η η := by
  let H := weightedFormMetric w e k
  obtain ⟨a, ha⟩ := K.isCompact.exists_bound_of_continuousOn
    ((weightedFormMetric_smooth w hw e k).continuousOn.mono hK)
  let m := max a 0 + 1
  have hm : 0 < m := by dsimp [m]; have := le_max_right a 0; linarith
  let c := formMetricCoercivityConstant (w.coeff e z) (hw e z hz).1 (hw e z hz).2 k
  have hc : 0 < c := formMetricCoercivityConstant_pos _ _ _ k
  refine ⟨m / c, div_pos hm hc, ?_⟩
  intro y hy η
  have hu : ‖H y‖ ≤ m := (ha y hy).trans (by dsimp [m]; have := le_max_left a 0; linarith)
  have hl : c * ‖η‖ ^ 2 ≤ formMetricCoefficients w e z k η η :=
    chart_form_metric_coercive w hw e z hz k η
  calc
    H y η η ≤ ‖H y η η‖ := le_abs_self _
    _ ≤ ‖H y η‖ * ‖η‖ := (H y η).le_opNorm η
    _ ≤ (‖H y‖ * ‖η‖) * ‖η‖ :=
      mul_le_mul_of_nonneg_right ((H y).le_opNorm η) (norm_nonneg _)
    _ = ‖H y‖ * ‖η‖ ^ 2 := by ring
    _ ≤ m * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_right hu (sq_nonneg _)
    _ = (m / c) * (c * ‖η‖ ^ 2) := by rw [← mul_assoc, div_mul_cancel₀ m hc.ne']
    _ ≤ (m / c) * formMetricCoefficients w e z k η η :=
      mul_le_mul_of_nonneg_left hl (div_pos hm hc).le

/-- Every internally chosen original cutoff has an internally bounded full global norm reconstruction. -/
theorem exists_finite_cutoff_norm_reconstruction {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) :
    ∃ C : Fin D.card → ℝ, (∀ i, 0 < C i) ∧
      ∀ i (α : SmoothRealForm n M q),
        integralPair w.form.val w.isKahler.1
          (smulFun (D.cutoff i) (D.smooth i) α) (smulFun (D.cutoff i) (D.smooth i) α) ≤
        C i * ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 := by
  classical
  have hex (i : Fin D.card) : ∃ C > 0, ∀ y ∈ (finiteChartCompact D i : Set (ComplexModel n)),
      ∀ η : FormCoefficients n q,
        weightedFormMetric w.form.val (D.localizer i).chart q y η η ≤
          C * formMetricCoefficients w.form.val (D.localizer i).chart (D.localizer i).center q η η :=
    exists_compact_chart_metric_upper w.form.val w.isKahler.1 (D.localizer i).chart
      (D.localizer i).center (D.localizer i).center_mem q (finiteChartCompact D i)
      (finiteChartCompact_subset_target D i)
  choose C hC hbound using hex
  refine ⟨C, hC, ?_⟩
  intro i α
  let d := D.localizer i
  let K := finiteChartCompact D i
  let hK := finiteChartCompact_subset_target D i
  let T := chartCutoffTest d.chart K hK (finiteNativeCutoff D i) α
  let G := formMetricCoefficients w.form.val d.chart d.center q
  let F := fun y : ComplexModel n => G (T y) (T y)
  let H := fun y : ComplexModel n => weightedFormMetric w.form.val d.chart q y (T y) (T y)
  have hFi : Integrable F (volume.restrict K) :=
    ContinuousOn.integrableOn_compact K.isCompact
      (((continuous_const.clm_apply T.continuous).clm_apply T.continuous).continuousOn)
  have hHi : Integrable H (volume.restrict K) :=
    ContinuousOn.integrableOn_compact K.isCompact
      (((weightedFormMetric_smooth w.form.val w.isKahler.1 d.chart q).continuousOn.clm_apply
        T.continuous.continuousOn).clm_apply T.continuous.continuousOn |>.mono hK)
  have hKm : MeasurableSet (K : Set (ComplexModel n)) := K.isCompact.isClosed.measurableSet
  have hFzero : ∀ y ∉ (K : Set (ComplexModel n)), F y = 0 := by
    intro y hy
    have hTy : T y = 0 := by
      by_contra hne
      exact hy (T.tsupport_subset (subset_tsupport (T : ComplexModel n → FormCoefficients n q) hne))
    simp only [F, hTy, map_zero]
  have hFindicator : (K : Set (ComplexModel n)).indicator F = F := by
    funext y
    by_cases hy : y ∈ (K : Set (ComplexModel n))
    · exact indicator_of_mem hy F
    · rw [indicator_of_notMem hy, hFzero y hy]
  have hrestrict : (∫ y, F y ∂volume.restrict K) = ∫ y, F y := by
    calc
      _ = ∫ y, (K : Set (ComplexModel n)).indicator F y := (integral_indicator hKm).symm
      _ = _ := by rw [hFindicator]
  have hvalue : ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 = ∫ y, F y := by
    rw [finiteChartValueCLM_smooth_readback D i α]
    simpa only [formMetricCoefficients_eq_original w.form.val w.isKahler.1 d.chart
      d.center d.center_mem q, F, G, T, d, K, hK] using
        fixedFormValueCLM_norm_sq_native
          (w.form.val.coeff d.chart d.center) (w.isKahler.1 d.chart d.center d.center_mem).1
          (w.isKahler.1 d.chart d.center d.center_mem).2 d.basis d.orthonormal q volume K T
  have hglobal : integralPair w.form.val w.isKahler.1
      (smulFun (D.cutoff i) (D.smooth i) α) (smulFun (D.cutoff i) (D.smooth i) α) =
        ∫ y, H y ∂volume.restrict K :=
    integralPair_cutoff_eq_weighted_native w.form.val w.isKahler.1 d.chart
      (D.cutoff i) (D.smooth i) (D.support_compact i)
      ((D.support_ball i).trans (chartBallOpen_subset_source d)) α
  rw [hglobal, hvalue]
  calc
    _ ≤ ∫ y, C i * F y ∂volume.restrict K :=
      integral_mono_ae hHi (hFi.const_mul (C i)) (by
        filter_upwards [ae_restrict_mem hKm] with y hy
        exact hbound i y hy (T y))
    _ = C i * (∫ y, F y ∂volume.restrict K) := integral_const_mul (C i) F
    _ = _ := by rw [hrestrict]

/-- The original finite partition gives its literal full-fiber norm inequality at every actual point. -/
theorem finite_partition_pointwise_reconstruction {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (α : SmoothRealForm n M q) (x : M) :
    pointwisePair w.form.val α α x ≤ (D.card : ℝ) *
      ∑ i, pointwisePair w.form.val (smulFun (D.cutoff i) (D.smooth i) α)
        (smulFun (D.cutoff i) (D.smooth i) α) x := by
  classical
  have hcs : (1 : ℝ) ≤ (D.card : ℝ) * ∑ i, (D.cutoff i x) ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin, D.sum_one x, one_pow] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin D.card => D.cutoff i x))
  have hnonneg := pointwisePair_self_nonneg w.form.val w.isKahler.1 α x
  have hm := mul_le_mul_of_nonneg_right hcs hnonneg
  simpa only [one_mul, Finset.sum_mul, pointwisePair_smulFun_self, mul_assoc] using hm

/-- The finite original scalar partition internally produces a positive bound for every genuine smooth graph image. -/
theorem exists_smooth_finite_value_norm_reconstruction {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) :
    ∃ B > 0, ∀ α : SmoothRealForm n M q,
      ‖energyInclusion w q (smoothEnergyLinear w q α)‖ ^ 2 ≤
        B * ∑ i, ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hlocal⟩ := exists_finite_cutoff_norm_reconstruction D
  let U := 1 + ∑ i, C i
  let B := ((D.card : ℝ) + 1) * U
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  have hU : 0 < U := by dsimp [U]; linarith
  have hcard : 0 ≤ (D.card : ℝ) := Nat.cast_nonneg _
  have hB : 0 < B := mul_pos (by linarith) hU
  have hCi (i : Fin D.card) : (D.card : ℝ) * C i ≤ B := by
    have hi : C i ≤ ∑ j, C j :=
      Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp [B, U]
    nlinarith
  refine ⟨B, hB, ?_⟩
  intro α
  let μ := hermitianVolumeMeasure w.form.val w.isKahler.1
  let P := pointwisePair w.form.val α α
  let F := fun i => pointwisePair w.form.val (smulFun (D.cutoff i) (D.smooth i) α)
    (smulFun (D.cutoff i) (D.smooth i) α)
  have hPi : Integrable P μ := pointwisePair_integrable w.form.val w.isKahler.1 α α
  have hFi (i : Fin D.card) : Integrable (F i) μ :=
    pointwisePair_integrable w.form.val w.isKahler.1 _ _
  have hSum : Integrable (fun x => ∑ i, F i x) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hFi i)
  have hintegral : (∫ x, P x ∂μ) ≤ (D.card : ℝ) * ∑ i, ∫ x, F i x ∂μ := by
    calc
      _ ≤ ∫ x, (D.card : ℝ) * ∑ i, F i x ∂μ :=
        integral_mono hPi (hSum.const_mul (D.card : ℝ))
          (finite_partition_pointwise_reconstruction D α)
      _ = (D.card : ℝ) * (∫ x, ∑ i, F i x ∂μ) := integral_const_mul _ _
      _ = _ := by rw [integral_finsetSum Finset.univ (fun i _ => hFi i)]
  have hnorm : ‖energyInclusion w q (smoothEnergyLinear w q α)‖ ^ 2 =
      integralPair w.form.val w.isKahler.1 α α := by
    change ‖toHilbertFormL2 w.form.val w.isKahler.1 α‖ ^ 2 = _
    exact hilbert_norm_sq w.form.val w.isKahler.1 α
  rw [hnorm]
  change (∫ x, P x ∂μ) ≤ _
  calc
    _ ≤ (D.card : ℝ) * ∑ i, ∫ x, F i x ∂μ := hintegral
    _ ≤ (D.card : ℝ) * ∑ i, C i * ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hlocal i α) hcard
    _ = ∑ i, ((D.card : ℝ) * C i) * ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, B * ‖finiteChartValueCLM D i (smoothEnergyLinear w q α)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hCi i) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The genuine finite native value single injection, using only the actual finite Hilbert product. -/
def finiteChartValueSingleCLM {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q) →L[ℝ]
      PiLp 2 (fun _ : Fin D.card =>
        CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D.card =>
    CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin D.card =>
        CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)) i)

theorem finiteChartValueSingleCLM_apply {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (i : Fin D.card)
    (v : CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)) (j : Fin D.card) :
    finiteChartValueSingleCLM D i v j =
      (Pi.single i v : Fin D.card → CoefficientL2 volume (FormIndex n q)) j := by
  classical
  by_cases h : j = i
  · subst j
    simp [finiteChartValueSingleCLM]
  · simp [finiteChartValueSingleCLM, h]

/-- The literal finite sum of the genuine full-graph chart values in the actual Hilbert product. -/
def finiteChartValueTupleCLM {w : KahlerBackground n M} (D : FiniteChartLocalization w q) :
    GraphEnergy w q →L[ℝ]
      PiLp 2 (fun _ : Fin D.card => CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)) :=
  ∑ i, (finiteChartValueSingleCLM D i).comp (finiteChartValueCLM D i)

theorem finiteChartValueTupleCLM_apply {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (u : GraphEnergy w q) (i : Fin D.card) :
    finiteChartValueTupleCLM D u i = finiteChartValueCLM D i u := by
  classical
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin D.card => CoefficientL2 volume (FormIndex n q)) i)
    ((∑ j, (finiteChartValueSingleCLM D j).comp (finiteChartValueCLM D j)) u) = _
  rw [sum_apply, map_sum]
  simp [finiteChartValueSingleCLM_apply, Pi.single_apply]

theorem finiteChartValueTupleCLM_norm_sq {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (u : GraphEnergy w q) :
    ‖finiteChartValueTupleCLM D u‖ ^ 2 = ∑ i, ‖finiteChartValueCLM D i u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteChartValueTupleCLM_apply]

/-- Genuine smooth-core density extends the internally obtained finite-value reconstruction to the entire original graph. -/
theorem whole_graph_finite_value_norm_reconstruction {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) :
    ∃ B > 0, ∀ u : GraphEnergy w q,
      ‖energyInclusion w q u‖ ≤ Real.sqrt B * ‖finiteChartValueTupleCLM D u‖ := by
  obtain ⟨B, hB, hbound⟩ := exists_smooth_finite_value_norm_reconstruction D
  refine ⟨B, hB, ?_⟩
  intro u
  refine (smoothEnergy_denseRange w q).induction_on
    (p := fun v => ‖energyInclusion w q v‖ ≤ Real.sqrt B * ‖finiteChartValueTupleCLM D v‖) u
    (isClosed_le (energyInclusion w q).continuous.norm
      (continuous_const.mul (finiteChartValueTupleCLM D).continuous.norm)) ?_
  intro α
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hB.le, finiteChartValueTupleCLM_norm_sq]
  exact hbound α

/-- Only the original background and degree are inputs: the finite original family and the whole-graph reconstruction bound are internal outputs. -/
theorem exists_whole_graph_finite_value_norm_reconstruction (w : KahlerBackground n M) (q : ℕ) :
    ∃ D : FiniteChartLocalization w q, ∃ B > 0,
      ∀ u : GraphEnergy w q,
        ‖energyInclusion w q u‖ ≤ Real.sqrt B * ‖finiteChartValueTupleCLM D u‖ := by
  obtain ⟨D⟩ := exists_finiteChartLocalization w q
  obtain ⟨B, hB, hbound⟩ := whole_graph_finite_value_norm_reconstruction D
  exact ⟨D, B, hB, hbound⟩

end SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalNormReconstruction
