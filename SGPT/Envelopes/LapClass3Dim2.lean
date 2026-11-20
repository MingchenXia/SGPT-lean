import SGPT.Envelopes.LapClass3Measure

/-!
# `θ_fⁿ` is a Radon measure in complex dimension `2`

Lane CZ-LP (`claude-cz-lp`, node `czlp:dim2`).  The book's remark after `lma:DNTroof` asserts that
for `f ∈ C^{1,1̄}(X)` the measure `ω_fⁿ` is an absolutely continuous Radon measure, because the
complex Hessian of `f` is in `Lⁿ`.  The `L²` theory of `LapClass3Density` gives this for `n = 2`:

* `LapApprox.exists_density_sq`: the Hessian densities are in `L²_loc` (Fatou).
* `integrableOn_hessDensity_of_two`: for `n = 2`, every Hessian density of `f ∘ e⁻¹ + ψ` (`ψ` a local
  potential of `θ`) has a locally integrable determinant density `(2/π²) Re det h`, i.e. the signed
  measure `(θ + ddᶜf)²` is an absolutely continuous Radon measure;
* `isFiniteMeasure_lapTopMeasure_of_two`: `θ_f² = lapTopMeasure θ f` is finite.

For `n ≥ 3` the same statements need the complex Hessian in `Lⁿ_loc` (Calderón–Zygmund); this is not
proved (see the lane report).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11

section L2

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  {w : KahlerBackground (m + 1) Y} {f : Y → ℝ}

theorem continuous_ofReal_sum_norm_sq :
    Continuous fun B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ =>
      ENNReal.ofReal (∑ p, ∑ q, ‖B p q‖ ^ 2) := by
  refine ENNReal.continuous_ofReal.comp ?_
  fun_prop

/-- **The Hessian densities are in `L²_loc`.** -/
theorem LapApprox.exists_density_sq (A : LapApprox w f) (hfc : Continuous f)
    (e : ComplexChart (m + 1) Y) :
    ∃ h : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      IsHessianDensityOn (fun z => f (e.val.symm z)) h e.val.target ∧
      ∀ K, IsCompact K → K ⊆ e.val.target →
        ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) < ⊤ := by
  obtain ⟨h, hh, ht⟩ := A.exists_density hfc e
  refine ⟨h, hh, fun K hK hKt => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_hessian_sq_le w e hK hKt
  set B : ℝ := C * (A.K ^ 2 * (kahlerVolume w univ).toReal) with hB
  set F : ℕ → ComplexModel (m + 1) → ℝ≥0∞ := fun k z => ENNReal.ofReal
    (∑ p, ∑ q, ‖complexHessian (fun y => A.v k (e.val.symm y)) z p q‖ ^ 2) with hF
  have hcontK : ∀ k, ContinuousOn (fun z => ∑ p, ∑ q,
      ‖complexHessian (fun y => A.v k (e.val.symm y)) z p q‖ ^ 2) K := fun k =>
    continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ =>
      ((continuousOn_complexHessian_apply e.val.open_target (A.smooth k e) p q).mono hKt).norm.pow 2
  have hFk : ∀ k, ∫⁻ z in K, F k z ≤ ENNReal.ofReal B := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal ((hcontK k).integrableOn_compact hK)
      (Eventually.of_forall fun z => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((hC _ (A.smooth k)).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have hcont := continuous_laplacian' w (A.smooth k)
    calc ∫ x, laplacian w.form.val (A.v k) x ^ 2 ∂(kahlerVolume w)
        ≤ ∫ _x, A.K ^ 2 ∂(kahlerVolume w) :=
          integral_mono ((hcont.pow 2).integrable_of_hasCompactSupport
            (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)))
            (integrable_const _) fun x => by
              have := A.lap_le k x
              exact sq_le_sq' (by linarith [neg_abs_le (laplacian w.form.val (A.v k) x)])
                ((le_abs_self _).trans this)
      _ = A.K ^ 2 * (kahlerVolume w univ).toReal := by
          rw [integral_const, smul_eq_mul, measureReal_def, mul_comm]
  have hmeas : ∀ k, AEMeasurable (F k) (volume.restrict K) := fun k =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hcontK k).aemeasurable hK.measurableSet)
  have hlim : ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun k => F k z) atTop (𝓝 (ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2))) := by
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae ht] with z hzK hz
    exact (continuous_ofReal_sum_norm_sq.tendsto _).comp (hz (hKt hzK))
  calc ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2)
      = ∫⁻ z in K, liminf (fun k => F k z) atTop :=
        lintegral_congr_ae (hlim.mono fun z hz => hz.liminf_eq.symm)
    _ ≤ liminf (fun k => ∫⁻ z in K, F k z) atTop := lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' (Frequently.of_forall hFk)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Hessian densities of `f ∘ e⁻¹ + ψ` are in `L²_loc`. -/
theorem lintegral_sq_lt_top_of_density (hf : HasBoundedMetricLaplacian w f)
    {e : ComplexChart (m + 1) Y} {W : Set (ComplexModel (m + 1))} {ψ : ComplexModel (m + 1) → ℝ}
    (hW : IsOpen W) (hWt : W ⊆ e.val.target) (hψ : ContDiffOn ℝ ∞ ψ W)
    {h : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W)
    {K : Set (ComplexModel (m + 1))} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) < ⊤ := by
  obtain ⟨A⟩ := nonempty_lapApprox w hf
  obtain ⟨h₀, hh₀, hsq⟩ := A.exists_density_sq hf.1 e
  have hden := (hh₀.mono hW hWt).add_contDiffOn hψ
  have hae := hh.ae_eq hden
  have hS : ∀ p q, ∃ c, ∀ z ∈ K, ‖smoothHess W ψ z p q‖ ≤ c := fun p q => by
    obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn
      ((continuousOn_complexHessian_apply hW hψ p q).mono hKW)
    refine ⟨c, fun z hz => ?_⟩
    simpa [smoothHess, hKW hz] using hc z hz
  choose c hc using hS
  set c₀ : ℝ := ∑ p, ∑ q, c p q ^ 2 with hc₀
  have hbound : ∀ᵐ z ∂volume.restrict K, ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) ≤
      2 * ENNReal.ofReal (∑ p, ∑ q, ‖h₀ z p q‖ ^ 2) + 2 * ENNReal.ofReal c₀ := by
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae hae] with z hzK hz
    rw [hz (hKW hzK)]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.mul_sum, hc₀, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ => ?_
    have h1 := hc p q z hzK
    have h2 : ‖(h₀ z + smoothHess W ψ z) p q‖ ≤ ‖h₀ z p q‖ + c p q :=
      (norm_add_le _ _).trans (add_le_add le_rfl h1)
    have h3 : 0 ≤ ‖smoothHess W ψ z p q‖ := norm_nonneg _
    have h4 : 0 ≤ c p q := h3.trans h1
    nlinarith [norm_nonneg ((h₀ z + smoothHess W ψ z) p q), norm_nonneg (h₀ z p q),
      sq_nonneg (‖h₀ z p q‖ - c p q)]
  refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (hsq K hK (hKW.trans hWt)),
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      hK.measure_lt_top⟩

end L2

/-! ### Dimension two -/

section Two

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (1 + 1)) Y]
  [IsComplexManifold (1 + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem norm_det_two_le (B : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖B.det‖ ≤ ∑ p, ∑ q, ‖B p q‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Fin.sum_univ_two]
  have h1 : ‖B 0 0 * B 1 1 - B 0 1 * B 1 0‖ ≤ ‖B 0 0‖ * ‖B 1 1‖ + ‖B 0 1‖ * ‖B 1 0‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  nlinarith [sq_nonneg (‖B 0 0‖ - ‖B 1 1‖), sq_nonneg (‖B 0 1‖ - ‖B 1 0‖), norm_nonneg (B 0 0),
    norm_nonneg (B 1 1), norm_nonneg (B 0 1), norm_nonneg (B 1 0)]

/-- **For `n = 2` the signed density of `(θ + ddᶜf)²` is locally integrable**: every Hessian
density `h` of `f ∘ e⁻¹ + ψ` (`ψ` a local potential of `θ` on `W`) has `(2/π²) Re det h ∈ L¹_loc(W)`,
so `(θ + ddᶜf)²` is an absolutely continuous signed Radon measure. -/
theorem integrableOn_hessDensity_of_two (w : KahlerBackground (1 + 1) Y)
    (θ : ClosedRealOneOneForm (1 + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f)
    {e : ComplexChart (1 + 1) Y} {W : Set (ComplexModel (1 + 1))} {ψ : ComplexModel (1 + 1) → ℝ}
    (hψ : IsSmoothLocalPotential θ.val e W ψ)
    {h : ComplexModel (1 + 1) → Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W)
    {K : Set (ComplexModel (1 + 1))} (hK : IsCompact K) (hKW : K ⊆ W) :
    IntegrableOn (hessDensity h) K := by
  have hsq := lintegral_sq_lt_top_of_density hf hψ.1 hψ.2.1 hψ.2.2.1 hh hK hKW
  refine ⟨(measurable_hessDensity hh.measurable).aestronglyMeasurable, ?_⟩
  set c : ℝ := ((1 + 1).factorial : ℝ) / Real.pi ^ (1 + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hb : ∀ z, ‖hessDensity h z‖ₑ ≤
      ENNReal.ofReal c * ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) := fun z => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hc0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hessDensity, abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (norm_det_two_le _)) hc0
  calc ∫⁻ z in K, ‖hessDensity h z‖ₑ
      ≤ ∫⁻ z in K, ENNReal.ofReal c * ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) :=
        lintegral_mono hb
    _ = ENNReal.ofReal c * ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖h z p q‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsq

/-- **For `n = 2`, `θ_f² = lapTopMeasure θ f` is a finite (Radon) measure** for `f ∈ C^{1,1̄}(X)`. -/
theorem isFiniteMeasure_lapTopMeasure_of_two (w : KahlerBackground (1 + 1) Y)
    (θ : ClosedRealOneOneForm (1 + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    IsFiniteMeasure (lapTopMeasure θ f) := by
  classical
  have hdens := hasHessianDensities_of_hasBoundedMetricLaplacian w hf
  have hloc : ∀ x : Y, ∃ N : Set Y, IsOpen N ∧ x ∈ N ∧ lapTopMeasure θ f N < ⊤ := by
    intro x
    set e := complexChartAt (n := 1 + 1) x with he
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ψ, hz₀W, hψ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x) hz₀
    obtain ⟨h, hh⟩ := hdens.exists_add e hψ.1 hψ.2.1 hψ.2.2.1
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hψ.1 (e.val x) hz₀W
    set r := ε / 2 with hr
    have hr0 : 0 < r := by positivity
    have hKW : closedBall (e.val x) r ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
    have hKt : closedBall (e.val x) r ⊆ e.val.target := hKW.trans hψ.2.1
    refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) r,
      e.val.isOpen_inter_preimage isOpen_ball, ⟨hxe, mem_ball_self hr0⟩, ?_⟩
    have hsub : e.val.source ∩ e.val ⁻¹' ball (e.val x) r ⊆
        e.val.symm '' closedBall (e.val x) r := fun y hy =>
      ⟨e.val y, ball_subset_closedBall hy.2, e.val.left_inv hy.1⟩
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [lapTopMeasure_image_eq w θ hf hψ hh measurableSet_closedBall hKW]
    have hint := integrableOn_hessDensity_of_two w θ hf hψ hh (isCompact_closedBall _ _) hKW
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hint.2
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  choose N hNo hxN hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  refine ⟨lt_of_le_of_lt (measure_mono ht) ?_⟩
  refine lt_of_le_of_lt (measure_biUnion_finset_le t N) ?_
  exact ENNReal.sum_lt_top.mpr fun x _ => hN x

end Two

end SGPT.Envelopes.LapClass3
