import SGPT.TestCurve.KFiltObstacle
import SGPT.Okounkov.TranscendentalExtensionAnalytic

/-!
# The analytic section ring of a compact Kähler manifold as a metered section ring

Sources `def:testcurve:L1134` and `ex:RWN` (chapter *Test curves*) in the book's setting of a
connected compact Kähler manifold `X` (not necessarily projective). Blueprint `claude-k-filt`,
nodes `claude-k-filt:analytic-metric`, `claude-k-filt:multiplier`.

For a Hermitian holomorphic line bundle `(L, h)` with smooth metric, `θ = c₁(L, h)`, the analytic
section ring `⊕_k H⁰(X, L^k)` (`twistedSections L unit k`, product `sectionMul`) with the tensor
metrics `|s|²_{h^k}` is a `SectionMetric` (`analyticSectionMetric`):

* Lelong–Poincaré: `log |s|²_{h^k} ∈ PSH(X, kθ)` for `s ≠ 0` (the Chern form of
  `L^{⊗k} ⊗ 𝒪` is `kθ`, `isOwn_twistedPower_unit`);
* `log |s|²_{h^k}` has analytic singularities (`hasManifoldAnalyticSingularityType_logNormSq`:
  in a frame, `log |s|² = log |g|² + log |e|²_h` with `g` holomorphic).

Moreover every section `s` with `k⁻¹ log |s|²_{h^k} ⪯ ψ` (`ψ` quasi-psh) lies in
`H⁰(X, L^k ⊗ 𝓘(kψ))` (`mem_fullHolomorphicIdealSections_of_singularityLE`), the step of the
book's proof of `eq:Gammatautheta`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Bundle Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `H⁰(X, L^k)` is finite-dimensional on a compact manifold. -/
instance twistedSections_unit_finiteDimensional [CompactSpace X]
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) (k : ℕ) :
    FiniteDimensional ℂ (twistedSections L unit k) :=
  twistedSections_finiteDimensional L unit k

/-- The Chern form of `L^{⊗k} ⊗ 𝒪` with its tensor metric is `k c₁(L, h)`. -/
theorem isOwn_twistedPower_unit (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (k : ℕ) :
    SGPT.PSH.GlobalL2.IsOwnFirstChernForm (twistedPower L unit k)
      ((k : ℝ) • sourceNativeFirstChernForm L hL) := by
  intro c e z hz hzE
  have h := sourceNativeFirstChernForm_isOwn (twistedPower L unit k)
    (sourceNativeTwistedPower_smooth L unit hL sourceNativeUnit_smooth k) c e z hz hzE
  rw [sourceNativeTwistedPower_chern_coeff L unit hL sourceNativeUnit_smooth c hz k,
    sourceNativeUnit_chern_coeff c hz, add_zero] at h
  simpa only [ClosedRealOneOneForm.coeff_smul] using h

/-- A holomorphic function on the manifold, read in an atlas chart. -/
theorem differentiableAt_comp_chart_symm {e : ComplexChart n X} {g : X → ℂ}
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (e.val.symm z)) :
    DifferentiableAt ℂ (fun w => g (e.val.symm w)) z := by
  have h2 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.2 hz
  have h3 := hg.comp z h2
  rwa [mdifferentiableAt_iff_differentiableAt] at h3

/-- **`log |s|²_h` has analytic singularities** for every holomorphic section `s` of a Hermitian
holomorphic line bundle (in a frame `e`, `log |s|² = log |g|² + log |e|²_h`, `g` holomorphic). -/
theorem hasManifoldAnalyticSingularityType_logNormSq {V : HermitianHolomorphicLineBundle.{0, 0} n X}
    (s : HolomorphicSections (n := n) V.Fiber) :
    QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n)
      (fun x => ENNReal.log (ENNReal.ofReal (‖s x‖ ^ 2))) := by
  intro e z hz
  set y := e.val.symm z
  let f := preferredOriginalFrame V.Fiber y
  let := f.property
  have hy : y ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ V.Fiber y
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' f.val.baseSet) :=
    e.val.isOpen_inter_preimage_symm f.val.open_baseSet
  have hzD : z ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.baseSet := ⟨hz, hy⟩
  set G : ComplexModel n → ℂ := fun w => sectionCoefficient V.Fiber f.val s (e.val.symm w)
  set h : ComplexModel n → ℝ := fun w => Real.log (frameNorm V.Fiber f.val (e.val.symm w) ^ 2)
  have hG : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w := by
    filter_upwards [hD.mem_nhds hzD] with w hw
    exact differentiableAt_comp_chart_symm hw.1
      (originalSectionCoefficient_holomorphicAt V.Fiber f s hw.2).self_of_nhds
  have hh : ContinuousAt h z := by
    have hsymm : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz
    have hfn : ContinuousAt (frameNorm V.Fiber f.val) y :=
      (frameNorm_continuousOn V.Fiber f.val).continuousAt (f.val.open_baseSet.mem_nhds hy)
    have hpos : 0 < frameNorm V.Fiber f.val y := frameNorm_pos V.Fiber f.val hy
    exact ((hfn.comp hsymm).pow 2).log (pow_pos hpos 2).ne'
  have hA := SGPT.Okounkov.TranscendentalCore.hasAnalyticSingularityTypeAt_generatorLog
    (H := fun _ : Fin 1 => G) (fun _ => hG) (c := 1) one_pos
  have hB := SGPT.Okounkov.TranscendentalExtension.hasAnalyticSingularityTypeAt_add_continuous hA hh
  refine SGPT.Okounkov.TranscendentalExtension.hasAnalyticSingularityTypeAt_congr hB ?_
  filter_upwards [hD.mem_nhds hzD] with w hw
  have hpos : 0 < frameNorm V.Fiber f.val (e.val.symm w) ^ 2 :=
    pow_pos (frameNorm_pos V.Fiber f.val hw.2) 2
  change (((1 : ℚ) : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => G) w + (h w : EReal) =
    ENNReal.log (ENNReal.ofReal (‖s (e.val.symm w)‖ ^ 2))
  rw [norm_eq_coefficient_mul_frameNorm V.Fiber f.val s hw.2, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hpos,
    generatorLog_eq_log_sum, Fin.sum_univ_one]
  simp only [Rat.cast_one, EReal.coe_one, one_mul]
  rfl

section Instance

variable [ConnectedSpace X]

/-- **The analytic section ring as a metered section ring** (`SectionMetric`): the graded pieces
`H⁰(X, L^k) = twistedSections L unit k`, the product `sectionMul`, the tensor metrics
`|s|²_{h^k}` and `θ = c₁(L, h)`. -/
def analyticSectionMetric (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) :
    SectionMetric n X (twistedSections L unit) (sectionMul (L := L)) where
  θ := sourceNativeFirstChernForm L hL
  normSq k s x := ‖s x‖ ^ 2
  normSq_nonneg _ _ _ := sq_nonneg _
  normSq_smul k c s x := by
    change ‖c • s x‖ ^ 2 = _
    rw [norm_smul, mul_pow, Complex.normSq_eq_norm_sq]
  sqrt_normSq_add_le k s t x := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    exact norm_add_le (s x) (t x)
  normSq_mul k k' s t x := by
    rw [norm_sectionMul, mul_pow]
  continuous_normSq k s := (ContinuousFiberNorm.continuous.comp s.contMDiff.continuous).pow 2
  exists_normSq_ne_zero k s hs := by
    obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
      by_contra h
      exact hs (ContMDiffSection.ext fun y => not_not.mp fun hy => h ⟨y, hy⟩)
    exact ⟨y, pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)⟩
  mul_ne_zero := sectionMul_ne_zero
  isThetaPsh k _ s hs :=
    ⟨sourceSectionLogNormSq_thetaPlurisubharmonic_of_isOwn (twistedPower L unit k)
      (sourceNativeTwistedPower_smooth L unit hL sourceNativeUnit_smooth k) _
      (isOwn_twistedPower_unit L hL k) s,
    sourceSectionLogNormSq_locallyNondegenerate (twistedPower L unit k) s hs⟩
  analyticType _ s _ := hasManifoldAnalyticSingularityType_logNormSq s

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)

@[simp] theorem analyticSectionMetric_θ :
    (analyticSectionMetric L hL).θ = sourceNativeFirstChernForm L hL := rfl

theorem analyticSectionMetric_normSq (k : ℕ) (s : twistedSections L unit k) (x : X) :
    (analyticSectionMetric L hL).normSq k s x = ‖s x‖ ^ 2 := rfl

/-! ### Multiplier sections -/

/-- The local estimate in the proof of `eq:Gammatautheta`: in the chart at `x` and the preferred
frame at `x`, the coefficient `g` of `s ∈ H⁰(X, L^k)` lies in `𝓘(k · k⁻¹ log |s|²_{h^k})`: the
weighted density `|g|² e^{-log |s|²}` equals `|e|^{-2}_{h^k}`, bounded near `x`. -/
theorem multiplierIntegrableAt_normalizedLog {k : ℕ} (hk : 0 < k) (s : twistedSections L unit k)
    (x : X) :
    MultiplierIntegrableAt
      (chartFunction ((analyticSectionMetric L hL).normalizedLog k s) (complexChartAt (n := n) x))
      (k : ℝ)
      (fun z => sectionCoefficient (twistedPower L unit k).Fiber
        (preferredOriginalFrame (twistedPower L unit k).Fiber x).val s
        ((complexChartAt (n := n) x).val.symm z))
      ((complexChartAt (n := n) x).val x) volume := by
  set V := (twistedPower L unit k).Fiber
  set e := complexChartAt (n := n) x with he_def
  let f := preferredOriginalFrame V x
  let := f.property
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set G : ComplexModel n → ℂ := fun z => sectionCoefficient V f.val s (e.val.symm z)
  set Fn : ComplexModel n → ℝ := fun z => frameNorm V f.val (e.val.symm z) ^ 2
  set D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' f.val.baseSet with hD_def
  have hDopen : IsOpen D := e.val.isOpen_inter_preimage_symm f.val.open_baseSet
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz0D : e.val x ∈ D := by
    refine ⟨e.val.map_source hxe, ?_⟩
    change e.val.symm (e.val x) ∈ f.val.baseSet
    rw [e.val.left_inv hxe]
    exact mem_baseSet_trivializationAt ℂ V x
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r' := r / 2
  have hr' : 0 < r' := half_pos hr
  have hcb : Metric.closedBall (e.val x) r' ⊆ D := fun z hz =>
    hrD (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (half_lt_self hr))
  have hFcont : ContinuousOn Fn D := by
    intro z hz
    have hsymm : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz.1
    have hfn : ContinuousAt (frameNorm V f.val) (e.val.symm z) :=
      (frameNorm_continuousOn V f.val).continuousAt (f.val.open_baseSet.mem_nhds hz.2)
    exact ((hfn.comp hsymm).pow 2).continuousWithinAt
  have hFpos : ∀ z ∈ D, 0 < Fn z := fun z hz => pow_pos (frameNorm_pos V f.val hz.2) 2
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_closedBall (e.val x) r').exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr'.le) (hFcont.mono hcb)
  set μ := Fn zm
  have hm : 0 < μ := hFpos zm (hcb hzm)
  set dens := multiplierDensity
    (chartFunction ((analyticSectionMetric L hL).normalizedLog k s) e) (k : ℝ) G
  have hdens_eq : ∀ z, dens z = ENNReal.ofReal (‖G z‖ ^ 2) *
      (ENNReal.ofReal (‖s (e.val.symm z)‖ ^ 2))⁻¹ := by
    intro z
    have hcancel : ∀ y : EReal, ((k : ℝ) : EReal) * (((k⁻¹ : ℝ) : EReal) * y) = y := by
      intro y
      rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hkR.ne', EReal.coe_one, one_mul]
    simp only [dens, multiplierDensity, multiplierWeight, chartFunction,
      SectionMetric.normalizedLog, hcancel, SectionMetric.logNormSq, analyticSectionMetric_normSq,
      EReal.exp_neg, ENNReal.exp_log]
  have hnorm : ∀ z ∈ D, ‖s (e.val.symm z)‖ ^ 2 = ‖G z‖ ^ 2 * Fn z := by
    intro z hz
    rw [norm_eq_coefficient_mul_frameNorm V f.val s hz.2, mul_pow]
  have hbound : ∀ z ∈ Metric.closedBall (e.val x) r', dens z ≤ ENNReal.ofReal μ⁻¹ := by
    intro z hz
    have hzD := hcb hz
    rw [hdens_eq z, hnorm z hzD]
    by_cases hG : G z = 0
    · simp only [hG, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ENNReal.ofReal_zero, zero_mul, zero_le]
    · have ha : 0 < ‖G z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hG) 2
      have hb : 0 < Fn z := hFpos z hzD
      rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_div_div, div_self ha.ne', one_div]
      exact inv_anti₀ hm (hmin hz)
  have hGdiff : ∀ z ∈ D, DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_comp_chart_symm hz.1
      (originalSectionCoefficient_holomorphicAt V f s hz.2).self_of_nhds
  refine ⟨hkR, Metric.ball (e.val x) r', Metric.isOpen_ball, Metric.mem_ball_self hr', ?_, ?_, ?_⟩
  · intro z hz
    exact (hGdiff z (hcb (Metric.ball_subset_closedBall hz))).differentiableWithinAt
  · have hGc : ContinuousOn G (Metric.ball (e.val x) r') := fun z hz =>
      (hGdiff z (hcb (Metric.ball_subset_closedBall hz))).continuousAt.continuousWithinAt
    have hNc : ContinuousOn (fun z => ‖s (e.val.symm z)‖ ^ 2) (Metric.ball (e.val x) r') := by
      intro z hz
      have hsymm : ContinuousAt e.val.symm z :=
        e.val.continuousAt_symm (hcb (Metric.ball_subset_closedBall hz)).1
      exact ((((ContinuousFiberNorm.continuous.comp s.contMDiff.continuous).continuousAt).comp
        hsymm).pow 2).continuousWithinAt
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (Metric.ball (e.val x) r')) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => (ENNReal.ofReal (‖s (e.val.symm z)‖ ^ 2))⁻¹)
        (volume.restrict (Metric.ball (e.val x) r')) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hNc.aemeasurable measurableSet_ball)).inv
    have hfun : dens = fun z => ENNReal.ofReal (‖G z‖ ^ 2) *
        (ENNReal.ofReal (‖s (e.val.symm z)‖ ^ 2))⁻¹ := funext hdens_eq
    change AEMeasurable dens _
    rw [hfun]
    exact h1.mul h2
  · calc (∫⁻ y in Metric.ball (e.val x) r', dens y ∂volume)
        ≤ ∫⁻ _ in Metric.ball (e.val x) r', ENNReal.ofReal μ⁻¹ ∂volume :=
          setLIntegral_mono measurable_const
            (fun z hz => hbound z (Metric.ball_subset_closedBall hz))
      _ = ENNReal.ofReal μ⁻¹ * volume (Metric.ball (e.val x) r') := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- **Multiplier sections** (the step `s ∈ H⁰(X, L^k ⊗ 𝓘(kΓ))` of the proof of
`eq:Gammatautheta`): a section `s ∈ H⁰(X, L^k)`, `k > 0`, with `k⁻¹ log |s|²_{h^k} ⪯ ψ` for a
quasi-psh `ψ` lies in `H⁰(X, L^k ⊗ 𝓘(kψ))`. -/
theorem mem_fullHolomorphicIdealSections_of_singularityLE [CompactSpace X] {k : ℕ} (hk : 0 < k)
    (s : twistedSections L unit k) {ψ : X → EReal}
    (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hle : SGPT.PSH.SingularityLE ((analyticSectionMetric L hL).normalizedLog k s) ψ) :
    s ∈ fullHolomorphicIdealSections (n := n) (twistedPower L unit k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k ψ) := by
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L unit k).Fiber
    _ (sourceDegreeMultiplierIdeal_isCoherent k hψ) s, sourceDegreeMultiplierIdeal_pos k hk]
  intro x
  refine ⟨originalSectionCoefficient_holomorphicAt (n := n) (twistedPower L unit k).Fiber
    (preferredOriginalFrame (twistedPower L unit k).Fiber x) s
    (mem_baseSet_trivializationAt ℂ (twistedPower L unit k).Fiber x), ?_⟩
  set e := complexChartAt (n := n) x
  have hz := e.val.map_source (mem_complexChartAt_source x)
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hle
  exact multiplierIntegrableAt_of_moreSingularAt (hψ.1 e _ hz)
    ⟨C, Filter.Eventually.of_forall fun z => hC _⟩ (multiplierIntegrableAt_normalizedLog L hL hk s x)

/-- If every section `s ∈ H⁰(X, L^k)` (`k > 0`) satisfies `k⁻¹ log |s|²_{h^k} ⪯ ψ`, then
`h⁰(X, L^k ⊗ 𝓘(kψ)) = h⁰(X, L^k)`. -/
theorem finrank_literal_eq_of_singularityLE [CompactSpace X] {k : ℕ} (hk : 0 < k) {ψ : X → EReal}
    (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hle : ∀ s : twistedSections L unit k,
      SGPT.PSH.SingularityLE ((analyticSectionMetric L hL).normalizedLog k s) ψ) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L unit k ψ) =
      Module.finrank ℂ (twistedSections L unit k) := by
  have htop : fullHolomorphicIdealSections (n := n) (twistedPower L unit k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k ψ) = ⊤ :=
    Submodule.eq_top_iff'.mpr fun s =>
      mem_fullHolomorphicIdealSections_of_singularityLE L hL hk s hψ (hle s)
  rw [(literalTwistedMultiplierSectionEquiv L unit k ψ).finrank_eq, htop, finrank_top]

end Instance

end SGPT.TestCurve.KFilt
