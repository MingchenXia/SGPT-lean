import SGPT.Analysis.CZHessianDensity

/-!
# Hessian densities as limits of smooth complex Hessians

Lane CZ-LP (`claude-cz-lp`, node `czlp:limit`).  If smooth functions `G_k` converge locally
uniformly to `g` on an open set `U ⊆ ℂⁿ` and their complex Hessians converge in `L¹_loc(U)` to a
matrix function `h`, then `h` is the Hessian density of `g` (`IsHessianDensityOn.of_tendsto`).  If
only the `L¹(K)` norms of the increments `∂∂̄G_{k+1} - ∂∂̄G_k` are summable on every compact
`K ⊆ U`, the complex Hessians converge almost everywhere on `U`, their limit is a Hessian density
of `g`, and the convergence also holds in `L¹_loc`
(`exists_isHessianDensityOn_of_summable`).  This is how densities are produced from smooth
approximations whose Hessians form an `L²`-Cauchy sequence (`LapClass3Density`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal NNReal Matrix

namespace SGPT.Analysis.CZLp

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11

variable {n : ℕ}

theorem continuous_hermQuad_left (v : ComplexModel n) :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => hermQuad A v := by
  simp only [hermQuad, sesqForm]
  fun_prop

theorem integrableOn_hermQuad_of_integrableOn {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hmeas : ∀ i j, Measurable fun z => h z i j) {K : Set (ComplexModel n)}
    (hint : ∀ i j, IntegrableOn (fun z => h z i j) K) (v : ComplexModel n) :
    IntegrableOn (fun z => hermQuad (h z) v) K := by
  refine Integrable.mono' ((integrable_finsetSum Finset.univ fun p _ =>
    integrable_finsetSum Finset.univ fun q _ => (hint p q).norm).mul_const (‖v‖ ^ 2))
    (measurable_hermQuad hmeas v).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_hermQuad_le _ _

theorem hermQuad_sub (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    hermQuad (A - B) v = hermQuad A v - hermQuad B v := by
  have h := hermQuad_add A ((-1 : ℝ) • B) v
  have e : A + ((-1 : ℝ) : ℂ) • B = A - B := by simp [sub_eq_add_neg]
  have h' := hermQuad_smul (-1) B v
  rw [show ((-1 : ℝ) • B) = ((-1 : ℝ) : ℂ) • B by ext; simp] at h
  rw [e, h'] at h
  linarith

/-- **Limits of smooth complex Hessians are densities.** -/
theorem IsHessianDensityOn.of_tendsto {G : ℕ → ComplexModel n → ℝ} {g : ComplexModel n → ℝ}
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : ∀ k, ContDiffOn ℝ ∞ (G k) U) (hgc : ContinuousOn g U)
    (hconv : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn G g atTop K)
    (hherm : ∀ z, (h z).IsHermitian) (hmeas : ∀ i j, Measurable fun z => h z i j)
    (hint : ∀ K, IsCompact K → K ⊆ U → ∀ i j, IntegrableOn (fun z => h z i j) K)
    (hL1 : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ z in K, ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖) atTop
        (𝓝 0)) :
    IsHessianDensityOn g h U where
  isOpen := hU
  continuousOn := hgc
  isHermitian := hherm
  measurable := hmeas
  integrableOn := hint
  levi φ hφ hφc hφU v := by
    set K := tsupport φ with hKdef
    have hK : IsCompact K := hφc
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    set L : ComplexModel n → ℝ := fun z => leviForm φ z v with hL
    have hLc : Continuous L := continuous_leviForm hφ2 v
    have hLsupp : ∀ z, z ∉ K → L z = 0 := fun z hz => by
      simp only [hL, leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hz, add_zero,
        zero_div]
    have hsub : Function.support L ⊆ K := fun z hz => by
      by_contra h'
      exact hz (hLsupp z h')
    have hLcs : HasCompactSupport L := hφc.mono' hsub
    have hLts : tsupport L ⊆ U := (closure_minimal hsub (isClosed_tsupport φ)).trans hφU
    have hφ0 : ∀ z, z ∉ K → φ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
    -- the smooth identities
    have hsm : ∀ k, ∫ z, G k z * L z = ∫ z, hermQuad (smoothHess U (G k) z) v * φ z :=
      fun k => (isHessianDensityOn_of_contDiffOn hU (hG k)).levi φ hφ hφc hφU v
    -- left-hand sides converge
    have hleft : Tendsto (fun k => ∫ z, G k z * L z) atTop (𝓝 (∫ z, g z * L z)) := by
      obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hgc.mono hφU)
      obtain ⟨BL, hBL⟩ := hLcs.exists_bound_of_continuous hLc
      have hev : ∀ᶠ k in atTop, ∀ z ∈ K, dist (g z) (G k z) < 1 :=
        (Metric.tendstoUniformlyOn_iff.mp (hconv K hK hφU)) 1 one_pos
      refine tendsto_integral_filter_of_dominated_convergence
        (fun z => (B + 1) * BL * K.indicator (fun _ => (1 : ℝ)) z) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun k =>
          (integrable_mul_of_continuousOn hU (hG k).continuousOn hLc hLcs hLts).aestronglyMeasurable
      · filter_upwards [hev] with k hk
        refine Eventually.of_forall fun z => ?_
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_mul, mul_one]
          have h1 : |G k z| ≤ B + 1 := by
            have := hk z hz
            rw [Real.dist_eq] at this
            have hb := hB z hz
            rw [Real.norm_eq_abs] at hb
            have : |G k z| ≤ |g z| + |g z - G k z| := by
              calc |G k z| = |g z - (g z - G k z)| := by ring_nf
                _ ≤ |g z| + |g z - G k z| := abs_sub _ _
            linarith
          have h2 : |L z| ≤ BL := by have := hBL z; rwa [Real.norm_eq_abs] at this
          exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [abs_nonneg (G k z)])
        · rw [hLsupp z hz, mul_zero, norm_zero, indicator_of_notMem hz, mul_zero]
      · exact ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator
          hK.measurableSet).const_mul _
      · refine Eventually.of_forall fun z => ?_
        by_cases hz : z ∈ K
        · exact ((hconv K hK hφU).tendsto_at hz).mul_const _
        · simp only [hLsupp z hz, mul_zero]
          exact tendsto_const_nhds
    -- right-hand sides converge
    have hright : Tendsto (fun k => ∫ z, hermQuad (smoothHess U (G k) z) v * φ z) atTop
        (𝓝 (∫ z, hermQuad (h z) v * φ z)) := by
      obtain ⟨Bφ, hBφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
      set c : ℝ := ‖v‖ ^ 2 * |Bφ| with hc
      have hint_k : ∀ k, Integrable (fun z => hermQuad (smoothHess U (G k) z) v * φ z) := fun k =>
        (isHessianDensityOn_of_contDiffOn hU (hG k)).integrable_hermQuad_mul hφ.continuous hφc
          hφU v
      have hint_h : Integrable (fun z => hermQuad (h z) v * φ z) := by
        have h1 : IntegrableOn (fun z => hermQuad (h z) v * φ z) K := by
          have hq : IntegrableOn (fun z => hermQuad (h z) v) K :=
            integrableOn_hermQuad_of_integrableOn hmeas (hint K hK hφU) v
          exact hq.mul_continuousOn hφ.continuous.continuousOn hK
        have heq : (fun z => hermQuad (h z) v * φ z) =
            K.indicator (fun z => hermQuad (h z) v * φ z) := by
          funext z
          by_cases hz : z ∈ K
          · rw [indicator_of_mem hz]
          · rw [indicator_of_notMem hz, hφ0 z hz, mul_zero]
        rw [heq]
        exact h1.integrable_indicator hK.measurableSet
      have hbound : ∀ k, |(∫ z, hermQuad (smoothHess U (G k) z) v * φ z) -
          ∫ z, hermQuad (h z) v * φ z| ≤
          c * ∫ z in K, ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖ := by
        intro k
        rw [← integral_sub (hint_k k) hint_h]
        have hfun : (fun z => hermQuad (smoothHess U (G k) z) v * φ z - hermQuad (h z) v * φ z) =
            K.indicator (fun z => hermQuad (complexHessian (G k) z - h z) v * φ z) := by
          funext z
          by_cases hz : z ∈ K
          · rw [indicator_of_mem hz, hermQuad_sub, sub_mul]
            simp only [smoothHess, hφU hz, if_true]
          · rw [indicator_of_notMem hz, hφ0 z hz, mul_zero, mul_zero, sub_zero]
        rw [hfun, integral_indicator hK.measurableSet, ← integral_const_mul]
        have hHc : ContinuousOn (fun z => complexHessian (G k) z) K := by
          refine continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_
          exact (continuousOn_complexHessian_apply hU (hG k) p q).mono hφU
        have hq1 : IntegrableOn (fun z => hermQuad (complexHessian (G k) z) v) K :=
          ((continuous_hermQuad_left v).comp_continuousOn hHc).integrableOn_compact hK
        have hq2 : IntegrableOn (fun z => hermQuad (h z) v) K :=
          integrableOn_hermQuad_of_integrableOn hmeas (hint K hK hφU) v
        have hq : IntegrableOn
            (fun z => hermQuad (complexHessian (G k) z - h z) v * φ z) K := by
          have := (hq1.sub hq2).mul_continuousOn hφ.continuous.continuousOn hK
          refine this.congr_fun (fun z _ => ?_) hK.measurableSet
          simp only [hermQuad_sub, Pi.sub_apply]
        refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hq.abs ?_
          hK.measurableSet fun z hz => ?_)
        · refine Integrable.const_mul ?_ c
          refine integrable_finsetSum Finset.univ fun p _ =>
            integrable_finsetSum Finset.univ fun q _ => ?_
          exact ((((continuousOn_complexHessian_apply hU (hG k) p q).mono hφU).integrableOn_compact
            hK).sub (hint K hK hφU p q)).norm
        · rw [abs_mul]
          have hq := abs_hermQuad_le (complexHessian (G k) z - h z) v
          have hφb : |φ z| ≤ |Bφ| := (by have := hBφ z; rwa [Real.norm_eq_abs] at this :
            |φ z| ≤ Bφ).trans (le_abs_self _)
          simp only [Matrix.sub_apply] at hq
          calc |hermQuad (complexHessian (G k) z - h z) v| * |φ z|
              ≤ ((∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖) * ‖v‖ ^ 2) * |Bφ| :=
                mul_le_mul hq hφb (abs_nonneg _) (by positivity)
            _ = c * ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖ := by rw [hc]; ring
      have hlim := (hL1 K hK hφU).const_mul c
      rw [mul_zero] at hlim
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
        (fun k => ?_) hlim)
      rw [Real.norm_eq_abs]
      exact hbound k
    have hleft' : Tendsto (fun k => ∫ z, hermQuad (smoothHess U (G k) z) v * φ z) atTop
        (𝓝 (∫ z, g z * leviForm φ z v)) := by
      refine hleft.congr fun k => ?_
      exact hsm k
    exact tendsto_nhds_unique hleft' hright

theorem norm_le_sum_sum (a : Fin n → Fin n → ℂ) (p q : Fin n) :
    ‖a p q‖ ≤ ∑ i, ∑ j, ‖a i j‖ :=
  (Finset.single_le_sum (f := fun j => ‖a p j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ q)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖a i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ p))

theorem isHermitian_herm_part (A : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (A + Aᴴ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

theorem herm_part_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (1 / 2 : ℂ) • (A + Aᴴ) = A := by
  rw [hA.eq, ← two_smul ℂ A, smul_smul]
  norm_num

/-- **Summable `L¹` increments produce a density.**  If smooth `G_k → g` locally uniformly on `U`
and `∑_k ‖∂∂̄G_{k+1} - ∂∂̄G_k‖_{L¹(K)} < ∞` for every compact `K ⊆ U`, then the complex Hessians
converge almost everywhere on `U` to a Hessian density of `g`. -/
theorem exists_isHessianDensityOn_of_summable {G : ℕ → ComplexModel n → ℝ}
    {g : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hG : ∀ k, ContDiffOn ℝ ∞ (G k) U) (hgc : ContinuousOn g U)
    (hconv : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn G g atTop K)
    (hsum : ∀ K, IsCompact K → K ⊆ U →
      ∑' k, ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q,
        ‖complexHessian (G (k + 1)) z p q - complexHessian (G k) z p q‖) ≠ ⊤) :
    ∃ h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ, IsHessianDensityOn g h U ∧
      ∀ᵐ z, z ∈ U → Tendsto (fun k => complexHessian (G k) z) atTop (𝓝 (h z)) := by
  set D : ℕ → ComplexModel n → ℝ := fun k z => ∑ p, ∑ q,
    ‖complexHessian (G (k + 1)) z p q - complexHessian (G k) z p q‖ with hD
  have hD0 : ∀ k z, 0 ≤ D k z := fun k z =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hHc : ∀ k p q, ContinuousOn (fun z => complexHessian (G k) z p q) U := fun k p q =>
    continuousOn_complexHessian_apply hU (hG k) p q
  have hDc : ∀ k, ContinuousOn (D k) U := fun k =>
    continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun q _ =>
      ((hHc (k + 1) p q).sub (hHc k p q)).norm
  have hmeasK : ∀ K, IsCompact K → K ⊆ U → ∀ k,
      AEMeasurable (fun z => ENNReal.ofReal (D k z)) (volume.restrict K) := fun K hK hKU k =>
    ENNReal.measurable_ofReal.comp_aemeasurable (((hDc k).mono hKU).aemeasurable hK.measurableSet)
  -- Step A: almost everywhere summability on compacts
  have hsumK : ∀ K, IsCompact K → K ⊆ U → ∀ᵐ z, z ∈ K → Summable (fun k => D k z) := by
    intro K hK hKU
    have hlt : ∀ᵐ z ∂volume.restrict K, ∑' k, ENNReal.ofReal (D k z) < ⊤ := by
      refine ae_lt_top' (AEMeasurable.tsum (hmeasK K hK hKU)) ?_
      rw [lintegral_tsum (hmeasK K hK hKU)]
      exact hsum K hK hKU
    rw [← ae_restrict_iff' hK.measurableSet]
    filter_upwards [hlt] with z hz
    have : Summable (fun k => (D k z).toNNReal) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      exact hz.ne
    refine (NNReal.summable_coe.mpr this).congr fun k => ?_
    simp [Real.coe_toNNReal _ (hD0 k z)]
  have hsumU : ∀ᵐ z, z ∈ U → Summable (fun k => D k z) := by
    refine IsHessianDensityOn.ae_of_forall_ball hU fun z₀ _ R _ hball => ?_
    have hKU : closedBall z₀ (2 * R) ⊆ U :=
      (closedBall_subset_closedBall (by linarith)).trans hball
    filter_upwards [hsumK _ (isCompact_closedBall _ _) hKU] with z hz hzB
    exact hz (ball_subset_closedBall hzB)
  have hstep : ∀ z k p q, dist (complexHessian (G k) z p q) (complexHessian (G (k + 1)) z p q) ≤
      D k z := fun z k p q => by
    rw [dist_eq_norm, norm_sub_rev]
    exact norm_le_sum_sum (fun i j =>
      complexHessian (G (k + 1)) z i j - complexHessian (G k) z i j) p q
  have hcauchy : ∀ᵐ z, z ∈ U → ∀ p q, ∃ l,
      Tendsto (fun k => complexHessian (G k) z p q) atTop (𝓝 l) := by
    filter_upwards [hsumU] with z hz hzU p q
    exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable (fun k => D k z) (fun k => hstep z k p q) (hz hzU))
  -- Step B: measurable limits
  have hlim : ∀ p q, ∃ H : ComplexModel n → ℂ, Measurable H ∧
      ∀ᵐ z ∂volume.restrict U, Tendsto (fun k => complexHessian (G k) z p q) atTop (𝓝 (H z)) := by
    intro p q
    refine measurable_limit_of_tendsto_metrizable_ae
      (fun k => (hHc k p q).aemeasurable hU.measurableSet) ?_
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mpr hcauchy] with z hz using hz p q
  choose H hHm hHt using hlim
  set h0 : ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun z => Matrix.of fun p q => H p q z
    with hh0
  set h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun z => (1 / 2 : ℂ) • (h0 z + (h0 z)ᴴ)
    with hhdef
  have hHtall : ∀ᵐ z, z ∈ U → ∀ p q,
      Tendsto (fun k => complexHessian (G k) z p q) atTop (𝓝 (H p q z)) := by
    have : ∀ᵐ z ∂volume.restrict U, ∀ p q,
        Tendsto (fun k => complexHessian (G k) z p q) atTop (𝓝 (H p q z)) := by
      rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro q; exact hHt p q
    exact (ae_restrict_iff' hU.measurableSet).mp this
  have hgood : ∀ᵐ z, z ∈ U → h z = h0 z ∧ Summable (fun k => D k z) ∧ ∀ p q,
      Tendsto (fun k => complexHessian (G k) z p q) atTop (𝓝 (h z p q)) := by
    filter_upwards [hHtall, hsumU] with z hz hs hzU
    have hherm0 : (h0 z).IsHermitian := by
      ext p q
      simp only [Matrix.conjTranspose_apply, hh0, Matrix.of_apply]
      have h1 := hz hzU q p
      have h2 := hz hzU p q
      have hc : Tendsto (fun k => star (complexHessian (G k) z q p)) atTop (𝓝 (star (H q p z))) :=
        (continuous_star.tendsto _).comp h1
      have hsym : (fun k => star (complexHessian (G k) z q p)) =
          fun k => complexHessian (G k) z p q := by
        funext k
        have hk := complexHessian_isHermitian (((hG k z hzU).contDiffAt
          (hU.mem_nhds hzU)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
        have := congrFun (congrFun hk.eq p) q
        simpa [Matrix.conjTranspose_apply] using this
      rw [hsym] at hc
      exact tendsto_nhds_unique hc h2
    have heq : h z = h0 z := herm_part_eq hherm0
    refine ⟨heq, hs hzU, fun p q => ?_⟩
    rw [heq]
    exact hz hzU p q
  have hmeas : ∀ i j, Measurable fun z => h z i j := by
    intro i j
    simp only [hhdef, hh0, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, smul_eq_mul]
    have h1 := hHm i j
    have h2 := hHm j i
    fun_prop
  -- Step C: tail bounds
  have htail : ∀ᵐ z, z ∈ U → ∀ k, ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖ ≤
      (n : ℝ) ^ 2 * ∑' m, D (k + m) z := by
    filter_upwards [hgood] with z hz hzU k
    obtain ⟨-, hs, ht⟩ := hz hzU
    have hpq : ∀ p q, ‖complexHessian (G k) z p q - h z p q‖ ≤ ∑' m, D (k + m) z := fun p q => by
      rw [← dist_eq_norm]
      exact dist_le_tsum_of_dist_le_of_tendsto (fun m => D m z) (fun m => hstep z m p q) hs (ht p q) k
    calc ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖ ≤ ∑ _p : Fin n, ∑ _q : Fin n,
          ∑' m, D (k + m) z := Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpq p q
      _ = (n : ℝ) ^ 2 * ∑' m, D (k + m) z := by simp [Finset.sum_const]; ring
  have hlint : ∀ K, IsCompact K → K ⊆ U → ∀ k,
      ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖) ≤
        ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' m, ∫⁻ z in K, ENNReal.ofReal (D (m + k) z) := by
    intro K hK hKU k
    have hsK := hsumK K hK hKU
    calc ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖)
        ≤ ∫⁻ z in K, ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' m, ENNReal.ofReal (D (m + k) z) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hK.measurableSet,
            ae_restrict_of_ae htail, ae_restrict_of_ae hsK] with z hz ht hs
          have hs' : Summable (fun m => D (m + k) z) := by
            have := (hs hz).comp_injective (add_left_injective k)
            exact this
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => hD0 _ z) hs',
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ((ht (hKU hz) k).trans (le_of_eq ?_))
          congr 1
          exact tsum_congr fun m => by rw [add_comm]
      _ = ENNReal.ofReal ((n : ℝ) ^ 2) * ∑' m, ∫⁻ z in K, ENNReal.ofReal (D (m + k) z) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_tsum fun m => hmeasK K hK hKU (m + k)]
  have hlintlim : ∀ K, IsCompact K → K ⊆ U → Tendsto (fun k =>
      ∫⁻ z in K, ENNReal.ofReal (∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖)) atTop (𝓝 0) := by
    intro K hK hKU
    have h1 := ENNReal.tendsto_sum_nat_add
      (fun m => ∫⁻ z in K, ENNReal.ofReal (D m z)) (hsum K hK hKU)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal ((n : ℝ) ^ 2))
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => zero_le) (hlint K hK hKU)
  -- Step D: integrability and `L¹` convergence
  have hFm : ∀ K, IsCompact K → K ⊆ U → ∀ k, AEStronglyMeasurable
      (fun z => ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖) (volume.restrict K) := by
    intro K hK hKU k
    refine (Finset.aestronglyMeasurable_fun_sum _ fun p _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun q _ => ?_)
    exact ((((hHc k p q).mono hKU).aestronglyMeasurable hK.measurableSet).sub
      (hmeas p q).aestronglyMeasurable).norm
  have hint : ∀ K, IsCompact K → K ⊆ U → ∀ i j, IntegrableOn (fun z => h z i j) K := by
    intro K hK hKU i j
    have hF0 : HasFiniteIntegral (fun z => ∑ p, ∑ q, ‖complexHessian (G 0) z p q - h z p q‖)
        (volume.restrict K) := by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      refine ((hlint K hK hKU 0).trans_lt ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (by simpa only [add_zero] using (hsum K hK hKU).lt_top)
    have hI0 : Integrable (fun z => ∑ p, ∑ q, ‖complexHessian (G 0) z p q - h z p q‖)
        (volume.restrict K) := ⟨hFm K hK hKU 0, hF0⟩
    have hc0 : IntegrableOn (fun z => complexHessian (G 0) z i j) K :=
      ((hHc 0 i j).mono hKU).integrableOn_compact hK
    refine Integrable.mono' (hc0.norm.add hI0) (hmeas i j).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    calc ‖h z i j‖ ≤ ‖complexHessian (G 0) z i j‖ + ‖complexHessian (G 0) z i j - h z i j‖ := by
          have := norm_sub_le (complexHessian (G 0) z i j) (complexHessian (G 0) z i j - h z i j)
          simp only [sub_sub_cancel] at this
          exact this
      _ ≤ _ := add_le_add le_rfl (norm_le_sum_sum
          (fun p q => complexHessian (G 0) z p q - h z p q) i j)
  have hL1 : ∀ K, IsCompact K → K ⊆ U → Tendsto
      (fun k => ∫ z in K, ∑ p, ∑ q, ‖complexHessian (G k) z p q - h z p q‖) atTop (𝓝 0) := by
    intro K hK hKU
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlintlim K hK hKU)
    rw [ENNReal.toReal_zero] at h1
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hFm K hK hKU k)]
  refine ⟨h, IsHessianDensityOn.of_tendsto hU hG hgc hconv
    (fun z => isHermitian_herm_part (h0 z)) hmeas hint hL1, ?_⟩
  filter_upwards [hgood] with z hz hzU
  obtain ⟨-, -, ht⟩ := hz hzU
  exact tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => ht p q

end SGPT.Analysis.CZLp
