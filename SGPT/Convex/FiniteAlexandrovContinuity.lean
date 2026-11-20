import SGPT.Convex.AlexandrovContinuity

namespace SGPT.Convex

open Set Filter Topology MeasureTheory Metric
open scoped Pointwise Topology CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Original compact-uniform finite convex sequences have genuinely uniform late
raw-covector bounds over each actual compact primal set. -/
theorem eventually_canonical_rawSubgradientImageOn_norm_le
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ A : Set E, IsCompact A → TendstoUniformlyOn F f atTop A)
    {K : Set E} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ m ∈ rawSubgradientImageOn continuousDualPairing (fun x ↦ (f x : EReal)) K,
        ‖m‖ ≤ R) ∧
      ∀ᶠ i in atTop, ∀ m ∈ rawSubgradientImageOn continuousDualPairing
        (fun x ↦ (F i x : EReal)) K, ‖m‖ ≤ R := by
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hcomp : IsCompact (K + closedBall (0 : E) 1) :=
    hK.add (isCompact_closedBall 0 1)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp ((hcomp.image hc).isBounded)
  let S := max R 0 + 1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hval : ∀ z ∈ K + closedBall (0 : E) 1, |f z| ≤ S := by
    intro z hz
    exact (hR (f z) (mem_image_of_mem f hz)).trans (by dsimp [S]; linarith [le_max_left R 0])
  have hu := Metric.tendstoUniformlyOn_iff.mp (hF _ hcomp) 1 zero_lt_one
  refine ⟨2 * S, by positivity,
    canonical_rawSubgradientImageOn_norm_le_of_value_bound hf hS hval, ?_⟩
  filter_upwards [hu] with i hi
  apply canonical_rawSubgradientImageOn_norm_le_of_value_bound (hFcv i) hS
  intro z hz
  have he := hi z hz
  rw [Real.dist_eq, abs_sub_comm] at he
  calc
    |F i z| ≤ |F i z - f z| + |f z| := by
      simpa only [sub_add_cancel] using abs_add_le (F i z - f z) (f z)
    _ ≤ S := by
      have hb := hR (f z) (mem_image_of_mem f hz)
      change |f z| ≤ R at hb
      dsimp [S]
      linarith [le_max_left R 0]

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  [FiniteDimensional ℝ M]

/-- The true perfect-pairing inverse transports both produced late and limiting
canonical bounds to the original dual space. -/
theorem eventually_rawSubgradientImageOn_norm_le
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ A : Set E, IsCompact A → TendstoUniformlyOn F f atTop A)
    {K : Set E} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ m ∈ rawSubgradientImageOn B (fun x ↦ (f x : EReal)) K, ‖m‖ ≤ R) ∧
      ∀ᶠ i in atTop, ∀ m ∈ rawSubgradientImageOn B
        (fun x ↦ (F i x : EReal)) K, ‖m‖ ≤ R := by
  let e := B.flip.toContPerfPair.toContinuousLinearEquiv
  obtain ⟨R, hR, hfR, hFR⟩ := eventually_canonical_rawSubgradientImageOn_norm_le hf hFcv hF hK
  have hmap (g : E → ℝ) (m : M)
      (hm : m ∈ rawSubgradientImageOn B (fun x ↦ (g x : EReal)) K) :
      e m ∈ rawSubgradientImageOn continuousDualPairing (fun x ↦ (g x : EReal)) K := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp hm
    obtain ⟨hxK, hxm⟩ := mem_iUnion.mp hx
    have hi := rawSubdifferential_image_toContPerfPair B (fun z ↦ (g z : EReal)) x
    exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxK, hi ▸ mem_image_of_mem e hxm⟩⟩
  have hbound (g : E → ℝ)
      (hg : ∀ m ∈ rawSubgradientImageOn continuousDualPairing (fun x ↦ (g x : EReal)) K, ‖m‖ ≤ R) :
      ∀ m ∈ rawSubgradientImageOn B (fun x ↦ (g x : EReal)) K,
        ‖m‖ ≤ ‖e.symm.toContinuousLinearMap‖ * R := by
    intro m hm
    calc
      ‖m‖ = ‖e.symm (e m)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e m‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * R :=
        mul_le_mul_of_nonneg_left (hg (e m) (hmap g m hm)) e.symm.toContinuousLinearMap.opNorm_nonneg
  exact ⟨‖e.symm.toContinuousLinearMap‖ * R,
    mul_nonneg e.symm.toContinuousLinearMap.opNorm_nonneg hR, hbound f hfR,
    hFR.mono (fun i hi ↦ hbound (F i) hi)⟩

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] {ν : Measure M} [ν.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual raw-image containment over the original compact test support bounds
the literal conjugate test integrand by an actual finite-support indicator AE. -/
theorem ae_norm_conjugateTestIntegrand_le_indicator_of_rawImage_subset
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) (h : C_c(E, ℝ)) {P : Set M}
    (himg : rawSubgradientImageOn B (fun x ↦ (f x : EReal)) (tsupport h) ⊆ P) :
    ∀ᵐ m ∂ν, ‖conjugateTestIntegrand B (fun x ↦ (f x : EReal)) h m‖ ≤
      P.indicator (fun _ ↦ ‖h.toBoundedContinuousFunction‖) m := by
  have hp := isProper_conjugate_of_isContPerfPair B (isProper_coe_of_convexOn hf)
  have hd := ae_differentiableAt_toReal_of_isProper (μ := ν) hp
  filter_upwards [hd] with m hdm
  by_cases hm : m ∈ P
  · rw [indicator_of_mem hm]
    exact norm_conjugateTestIntegrand_le B _ h m
  · rw [indicator_of_notMem hm]
    have hz : conjugateTestIntegrand B (fun x ↦ (f x : EReal)) h m = 0 := by
      by_cases hi : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal))))
      · have hzero : h (conjugateGradient B (fun x ↦ (f x : EReal)) m) = 0 := by
          by_contra hn
          have hraw := mem_rawSubdifferential_conjugateGradient_coe B hf hi (hdm hi)
          have himgmem : m ∈ rawSubgradientImageOn B (fun x ↦ (f x : EReal)) (tsupport h) :=
            mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨subset_tsupport h hn, hraw⟩⟩
          exact hm (himg himgmem)
        simp only [conjugateTestIntegrand, indicator_of_mem hi, hzero]
      · simp only [conjugateTestIntegrand, indicator_of_notMem hi]
    rw [hz, norm_zero]

/-- Genuine local raw-covector domination proves compact-test continuity for
all finite convex functions, without any global conjugate-domain bound. -/
theorem tendsto_integral_alexandrovMeasure_of_finite_convex_compact_convergence
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    (h : C_c(E, ℝ)) :
    Tendsto (fun i ↦ ∫ x, h x ∂alexandrovMeasure B ν (fun z ↦ (F i z : EReal))) atTop
      (𝓝 (∫ x, h x ∂alexandrovMeasure B ν (fun z ↦ (f z : EReal)))) := by
  obtain ⟨R, hR, hfr, hFr⟩ := eventually_rawSubgradientImageOn_norm_le B hf hFcv hF h.hasCompactSupport
  let P : Set M := closedBall 0 R
  have hP : IsCompact P := isCompact_closedBall 0 R
  have hbint : Integrable (P.indicator (fun _ ↦ ‖h.toBoundedContinuousFunction‖)) ν := by
    rw [integrable_indicator_iff hP.measurableSet]
    exact integrableOn_const hP.measure_lt_top.ne
  have hbound : ∀ᶠ i in atTop, ∀ᵐ m ∂ν,
      ‖conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h m‖ ≤
        P.indicator (fun _ ↦ ‖h.toBoundedContinuousFunction‖) m := by
    filter_upwards [hFr] with i hi
    apply ae_norm_conjugateTestIntegrand_le_indicator_of_rawImage_subset B (hFcv i) h
    intro m hm
    simpa only [P, mem_closedBall, dist_zero_right] using hi m hm
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (P.indicator (fun _ ↦ ‖h.toBoundedContinuousFunction‖))
    (Eventually.of_forall (fun i ↦
      (measurable_conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h).aestronglyMeasurable))
    hbound hbint
    (ae_tendsto_conjugateTestIntegrand_of_convex_compact_convergence B hf hFcv hF h)
  simp_rw [integral_alexandrovMeasure_eq_conjugateTestIntegrand B]
  exact tendsto_const_nhds.mul ht

end SGPT.Convex
