import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation
import SGPT.Foundations.Analysis.PlurisubharmonicAE

/-!
# Pointwise order retained by actual weak PSH distribution limits

The original nonnegative smooth tests internally produce positivity of the
actual difference-density distribution, hence genuine almost-everywhere
order. Original PSH comparison then recovers every original point, including
poles. Strong L1 convergence is neither assumed nor concluded here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder

open SmoothTestMeasureSeparation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The genuine pullback of a locally finite measure to an open domain is locally finite. -/
theorem isLocallyFiniteMeasure_open_comap (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.comap (Subtype.val : Ω → E)) := by
  constructor
  intro x
  obtain ⟨V, hxV, hVo, hVm⟩ := μ.exists_isOpen_measure_lt_top (x : E)
  refine ⟨Subtype.val ⁻¹' V, (hVo.preimage continuous_subtype_val).mem_nhds hxV, ?_⟩
  have hemb : MeasurableEmbedding (Subtype.val : Ω → E) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hread := hemb.comap_preimage μ V
  rw [hread]
  exact (measure_mono inter_subset_left).trans_lt hVm

/-- Positive smooth tests recover the almost-everywhere order of the actual real densities. -/
theorem ae_le_of_nonnegative_test_integrals (ξ : Measure Ω) [IsLocallyFiniteMeasure ξ]
    {f g : Ω → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : LocallyIntegrable f ξ) (hg : LocallyIntegrable g ξ)
    (hle : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      (∫ x : Ω, φ x * f x ∂ξ) ≤ ∫ x : Ω, φ x * g x ∂ξ) :
    ∀ᵐ x ∂ξ, f x ≤ g x := by
  have hint : ∀ (h : Ω → ℝ), LocallyIntegrable h ξ →
      ∀ φ : 𝓓(Ω, ℝ), Integrable (fun x : Ω => φ x * h x) ξ := by
    intro h hh φ
    have hcont : Continuous fun x : Ω => φ x := φ.continuous.comp continuous_subtype_val
    have hsupp : HasCompactSupport fun x : Ω => φ x := by
      let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
      have heq : (fun x : Ω => φ x) = g₀ := by funext x; simp [g₀]
      rw [heq]
      exact g₀.hasCompactSupport
    simpa [smul_eq_mul, mul_comm] using
      hh.integrable_smul_right_of_hasCompactSupport hcont hsupp
  have hd : LocallyIntegrable (fun x => g x - f x) ξ := hg.sub hf
  have hrep : ∀ φ : 𝓓(Ω, ℝ),
      subtypeRegularDistribution ξ (fun x => g x - f x) hd φ =
        ∫ x : Ω, φ x * (g x - f x) ∂ξ :=
    subtypeRegularDistribution_apply ξ _ hd
  have hpos : PositiveDistribution (subtypeRegularDistribution ξ (fun x => g x - f x) hd) := by
    intro φ hφ
    rw [hrep]
    simp_rw [mul_sub]
    rw [integral_sub (hint g hg φ) (hint f hf φ), sub_nonneg]
    exact hle φ hφ
  exact (ae_nonneg_of_positiveDistribution_integral hpos ξ (hgm.sub hfm) hd hrep).mono
    (fun x hx => sub_nonneg.mp hx)

/-- Actual ambient test integrals recover the density order on the original open domain. -/
theorem ae_le_of_nonnegative_ambient_test_integrals
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {f g : E → ℝ}
    (hfm : Measurable (fun x : Ω => f x)) (hgm : Measurable (fun x : Ω => g x))
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ)
    (hle : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      (∫ x, φ x * f x ∂μ) ≤ ∫ x, φ x * g x ∂μ) :
    ∀ᵐ x ∂μ.restrict Ω, f x ≤ g x := by
  let ξ : Measure Ω := μ.comap Subtype.val
  let _ : IsLocallyFiniteMeasure ξ := isLocallyFiniteMeasure_open_comap μ
  have hf' : LocallyIntegrable (fun x : Ω => f x) ξ :=
    (locallyIntegrable_comap Ω.isOpen.measurableSet).mpr hf
  have hg' : LocallyIntegrable (fun x : Ω => g x) ξ :=
    (locallyIntegrable_comap Ω.isOpen.measurableSet).mpr hg
  have hread : ∀ (h : E → ℝ) (φ : 𝓓(Ω, ℝ)),
      (∫ x : Ω, φ x * h x ∂ξ) = ∫ x, φ x * h x ∂μ := by
    intro h φ
    calc
      _ = ∫ x in (Ω : Set E), φ x * h x ∂μ := by
        exact integral_subtype_comap Ω.isOpen.measurableSet (fun x => φ x * h x)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)), zero_mul])
  apply (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr
  exact ae_le_of_nonnegative_test_integrals ξ hfm hgm hf' hg' (fun φ hφ => by
    rw [hread f φ, hread g φ]
    exact hle φ hφ)

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- A genuine weak original PSH limit retains an eventual original pointwise upper barrier. -/
theorem le_of_weak_limit_eventually_le
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → E → EReal} {v w : E → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hv : PlurisubharmonicOn v Ω) (hw : PlurisubharmonicOn w Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnu : ∀ i, ∃ x ∈ Ω, u i x ≠ ⊥)
    (hnv : ∃ x ∈ Ω, v x ≠ ⊥) (hnw : ∃ x ∈ Ω, w x ≠ ⊥)
    (hlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ x, φ x * (u i x).toReal ∂μ) l
        (𝓝 (∫ x, φ x * (v x).toReal ∂μ)))
    (hdom : ∀ᶠ i in l, ∀ x ∈ Ω, u i x ≤ w x) :
    ∀ x ∈ Ω, v x ≤ w x := by
  have hvi := hv.locallyIntegrableOn_toReal μ hΩ hnv
  have hwi := hw.locallyIntegrableOn_toReal μ hΩ hnw
  have hvm : Measurable (fun x : Ω => (v x).toReal) :=
    (upperSemicontinuousOn_iff_restrict.mpr hv.upperSemicontinuousOn).measurable.ereal_toReal
  have hwm : Measurable (fun x : Ω => (w x).toReal) :=
    (upperSemicontinuousOn_iff_restrict.mpr hw.upperSemicontinuousOn).measurable.ereal_toReal
  have htest : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      (∫ x, φ x * (v x).toReal ∂μ) ≤ ∫ x, φ x * (w x).toReal ∂μ := by
    intro φ hφ
    apply le_of_tendsto (hlim φ)
    filter_upwards [hdom] with i hi
    have hui := (hu i).locallyIntegrableOn_toReal μ hΩ (hnu i)
    have hai : ∀ᵐ x ∂μ.restrict Ω, (u i x).toReal ≤ (w x).toReal := by
      filter_upwards [(hu i).ae_coe_toReal μ hΩ (hnu i),
        hw.ae_coe_toReal μ hΩ hnw, ae_restrict_mem Ω.isOpen.measurableSet] with x hux hwx hx
      exact EReal.coe_le_coe_iff.mp (hux.le.trans ((hi x hx).trans hwx.symm.le))
    have hai' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hai
    have hfi : Integrable (fun x => φ x * (u i x).toReal) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hui
    have hfw : Integrable (fun x => φ x * (w x).toReal) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hwi
    apply integral_mono_ae hfi hfw
    filter_upwards [hai'] with x hx
    by_cases hxΩ : x ∈ Ω
    · exact mul_le_mul_of_nonneg_left (hx hxΩ) (hφ x)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hxΩ (φ.tsupport_subset h))]
      simp
  have hreal := ae_le_of_nonnegative_ambient_test_integrals μ hvm hwm hvi hwi htest
  apply hv.le_of_ae_le Ω.isOpen hw.upperSemicontinuousOn μ
  filter_upwards [hv.ae_coe_toReal μ hΩ hnv, hw.ae_coe_toReal μ hΩ hnw, hreal]
    with x hvx hwx hx
  exact hvx.symm.le.trans ((EReal.coe_le_coe_iff.mpr hx).trans hwx.le)

end SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder
