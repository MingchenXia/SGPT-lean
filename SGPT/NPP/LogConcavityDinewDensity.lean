import SGPT.NPP.LogConcavityDinewLocal

/-!
# Dinew's inequality against a measure with continuous density

FPT `prop:nonpluripolar-multifactor-common-measure` for the common measure `ν = f dV` with `f`
continuous on `Ω ⊆ ℂⁿ` and constant coefficients `cᵢ ≥ 0`: if `⟨(ddᶜuᵢ)ⁿ⟩ ≥ cᵢ ν` on `Ω` for
plurisubharmonic `uᵢ` (possibly unbounded), then `⟨ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ⟩ ≥ (∏ᵢ cᵢ^{1/n}) ν`
(`mixedTruncationLimitMeasure_ge_withDensity`). The case `ν = (ddᶜg)ⁿ` for a smooth psh `g`
(the coordinate form of `ωⁿ`) is `mixedTruncationLimitMeasure_ge_smoothMeasure`.

Proof: near each point `f` is within `δ` of a constant, so the constant-density case on balls
(`mixedTruncationLimitMeasure_ge_on_ball`) gives `⟨⋀ ddᶜuᵢ⟩ ≥ (∏ cᵢ^{1/n}) (f - 2δ)₊ dV` there;
the local estimates glue by a Lindelöf covering, and `δ → 0` by monotone convergence.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ContDiff ENNReal
open TopologicalSpace

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

variable {n : ℕ}

theorem smul_le_smul_measure {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (h : μ ≤ ν)
    (c : ℝ≥0∞) : c • μ ≤ c • ν :=
  Measure.le_iff.mpr fun s _ => by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr

theorem prod_mul_const_rpow (hn : 0 < n) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i) {m : ℝ}
    (hm : 0 ≤ m) : ∏ i, (c i * m) ^ ((n : ℝ)⁻¹) = (∏ i, c i ^ ((n : ℝ)⁻¹)) * m := by
  simp_rw [Real.mul_rpow (hc _) hm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hm hn.ne']

/-- **The estimate near a point**, with an additive error `2δ` in the density. -/
theorem exists_ball_mixedTruncationLimitMeasure_ge_sub (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {f : ComplexModel n → ℝ} (hf : ContinuousOn f Ω) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hμ : ∀ i, ENNReal.ofReal (c i) • (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ truncationLimitMeasure Ω (u i) (hu i))
    {δ : ℝ} (hδ : 0 < δ) {x₀ : ComplexModel n} (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, Metric.ball x₀ r ⊆ Ω ∧ (volume.restrict (Metric.ball x₀ r)).withDensity
        (fun z => ENNReal.ofReal ((∏ i, c i ^ ((n : ℝ)⁻¹)) * (f z - 2 * δ))) ≤
      (mixedTruncationLimitMeasure Ω u hu).restrict (Metric.ball x₀ r) := by
  have hfc : ContinuousAt f x₀ := hf.continuousAt (Ω.isOpen.mem_nhds hx₀)
  obtain ⟨δ₁, hδ₁, hfδ⟩ := Metric.continuousAt_iff.mp hfc δ hδ
  obtain ⟨ε₂, hε₂, hballΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x₀ hx₀
  set R : ℝ := min δ₁ ε₂ with hR
  have hRpos : 0 < R := lt_min hδ₁ hε₂
  set Ω' : Opens (ComplexModel n) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ with hΩ'
  have hΩ'Ω : Ω' ≤ Ω := fun z hz => hballΩ (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hu' : ∀ i, PlurisubharmonicOn (u i) Ω' := fun i => (hu i).mono hΩ'Ω
  set m : ℝ := max (f x₀ - δ) 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hfz : ∀ z ∈ (Ω' : Set (ComplexModel n)), |f z - f x₀| < δ := fun z hz => by
    have := hfδ (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hmf : ∀ z ∈ (Ω' : Set (ComplexModel n)), ENNReal.ofReal m ≤ ENNReal.ofReal (f z) := by
    intro z hz
    have h1 := (abs_lt.mp (hfz z hz)).1
    rcases le_total (f x₀ - δ) 0 with h | h
    · rw [hm, max_eq_right h, ENNReal.ofReal_zero]; exact zero_le
    · rw [hm, max_eq_left h]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the hypothesis on the small ball, with a constant density
  have hμ' : ∀ i, ENNReal.ofReal (c i * m) • volume.restrict (Ω' : Set (ComplexModel n)) ≤
      truncationLimitMeasure Ω' (u i) (hu' i) := by
    intro i
    rw [← truncationLimitMeasure_restrict_open hΩ'Ω (hu i) (hu' i)]
    calc ENNReal.ofReal (c i * m) • volume.restrict (Ω' : Set (ComplexModel n))
        = ENNReal.ofReal (c i) • (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
            (fun _ => ENNReal.ofReal m) := by
          rw [withDensity_const, smul_smul, ENNReal.ofReal_mul (hc i)]
      _ ≤ ENNReal.ofReal (c i) • (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
            (fun z => ENNReal.ofReal (f z)) := by
          refine smul_le_smul_measure (withDensity_mono ?_) _
          filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with z hz
          exact hmf z hz
      _ = (ENNReal.ofReal (c i) • (volume.restrict (Ω : Set (ComplexModel n))).withDensity
            (fun z => ENNReal.ofReal (f z))).restrict Ω' := by
          rw [Measure.restrict_smul, restrict_withDensity Ω'.isOpen.measurableSet,
            Measure.restrict_restrict_of_subset hΩ'Ω]
      _ ≤ (truncationLimitMeasure Ω (u i) (hu i)).restrict Ω' :=
          Measure.restrict_mono subset_rfl (hμ i)
  have hcm : ∀ i, 0 ≤ c i * m := fun i => mul_nonneg (hc i) hm0
  have hcl : Metric.closedBall x₀ (R / 2) ⊆ Ω' := Metric.closedBall_subset_ball (by linarith)
  have hloc := mixedTruncationLimitMeasure_ge_on_ball hn hu' hcm hμ' (half_pos hRpos) hcl
  rw [prod_mul_const_rpow hn hc hm0, ← mixedTruncationLimitMeasure_restrict_open hΩ'Ω hu,
    Measure.restrict_restrict_of_subset (show Metric.ball x₀ (R / 2 / 4) ⊆ (Ω' : Set (ComplexModel n))
      from Metric.ball_subset_ball (by linarith))]
    at hloc
  refine ⟨R / 2 / 4, by positivity, fun z hz => hΩ'Ω (Metric.ball_subset_ball (by linarith) hz),
    le_trans ?_ hloc⟩
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball (x := x₀) (ε := R / 2 / 4)).measurableSet]
    with z hz
  have hzΩ' : z ∈ (Ω' : Set (ComplexModel n)) := Metric.ball_subset_ball (by linarith) hz
  have h1 := (abs_lt.mp (hfz z hzΩ')).2
  have hP : 0 ≤ ∏ i, c i ^ ((n : ℝ)⁻¹) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hc i) _
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hP)
  exact le_trans (by linarith) (le_max_left _ _)

/-- **The glued estimate with an additive error.** -/
theorem mixedTruncationLimitMeasure_ge_withDensity_sub (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {f : ComplexModel n → ℝ} (hf : ContinuousOn f Ω) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hμ : ∀ i, ENNReal.ofReal (c i) • (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ truncationLimitMeasure Ω (u i) (hu i))
    {δ : ℝ} (hδ : 0 < δ) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal ((∏ i, c i ^ ((n : ℝ)⁻¹)) * (f z - 2 * δ))) ≤
      mixedTruncationLimitMeasure Ω u hu := by
  set g : ComplexModel n → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((∏ i, c i ^ ((n : ℝ)⁻¹)) * (f z - 2 * δ)) with hg
  have hglue := restrict_le_restrict_of_isLindelof
    (μ := (volume.restrict (Ω : Set (ComplexModel n))).withDensity g)
    (ν := mixedTruncationLimitMeasure Ω u hu)
    (HereditarilyLindelofSpace.isLindelof (Ω : Set (ComplexModel n))) fun x hx => by
      obtain ⟨r, hr, hrΩ, hle⟩ := exists_ball_mixedTruncationLimitMeasure_ge_sub hn hu hf hc hμ hδ hx
      refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
      rwa [restrict_withDensity Metric.isOpen_ball.measurableSet,
        Measure.restrict_restrict_of_subset hrΩ]
  rw [restrict_withDensity Ω.isOpen.measurableSet,
    Measure.restrict_restrict Ω.isOpen.measurableSet, inter_self] at hglue
  exact hglue.trans Measure.restrict_le_self

/-- **Dinew's inequality against `f dV`, `f` continuous** (FPT
`prop:nonpluripolar-multifactor-common-measure`, constant coefficients): for psh `uᵢ` on `Ω` with
`⟨(ddᶜuᵢ)ⁿ⟩ ≥ cᵢ f dV`, `⟨ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ⟩ ≥ (∏ᵢ cᵢ^{1/n}) f dV`. -/
theorem mixedTruncationLimitMeasure_ge_withDensity (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {f : ComplexModel n → ℝ} (hf : ContinuousOn f Ω) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hμ : ∀ i, ENNReal.ofReal (c i) • (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ truncationLimitMeasure Ω (u i) (hu i)) :
    ENNReal.ofReal (∏ i, c i ^ ((n : ℝ)⁻¹)) •
        (volume.restrict (Ω : Set (ComplexModel n))).withDensity (fun z => ENNReal.ofReal (f z)) ≤
      mixedTruncationLimitMeasure Ω u hu := by
  set P : ℝ := ∏ i, c i ^ ((n : ℝ)⁻¹) with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hc i) _
  set ν := volume.restrict (Ω : Set (ComplexModel n)) with hν
  have hfm : AEMeasurable f ν := hf.aemeasurable Ω.isOpen.measurableSet
  refine Measure.le_iff.mpr fun s hs => ?_
  set F : ℕ → ComplexModel n → ℝ≥0∞ :=
    fun k z => ENNReal.ofReal (P * (f z - 2 * (1 / ((k : ℝ) + 1)))) with hF
  have hFle : ∀ k, ∫⁻ z in s, F k z ∂ν ≤ mixedTruncationLimitMeasure Ω u hu s := fun k => by
    have h := mixedTruncationLimitMeasure_ge_withDensity_sub hn hu hf hc hμ
      (δ := 1 / ((k : ℝ) + 1)) (by positivity)
    have := h s
    rwa [withDensity_apply _ hs] at this
  have hFmono : ∀ z, Monotone fun k => F k z := by
    intro z j k hjk
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hP)
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
    linarith
  have hFsup : ∀ z, ⨆ k, F k z = ENNReal.ofReal P * ENNReal.ofReal (f z) := by
    intro z
    rw [← ENNReal.ofReal_mul hP]
    refine iSup_eq_of_tendsto (hFmono z) ?_
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := ((h0.const_mul (2 : ℝ)).const_sub (f z)).const_mul P
    have h2 : Tendsto (fun k : ℕ => P * (f z - 2 * (1 / ((k : ℝ) + 1)))) atTop
        (𝓝 (P * f z)) := by simpa using h1
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hFm : ∀ k, AEMeasurable (F k) (ν.restrict s) := fun k =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((aemeasurable_const.mul (hfm.sub aemeasurable_const)).mono_measure Measure.restrict_le_self)
  calc (ENNReal.ofReal P • ν.withDensity (fun z => ENNReal.ofReal (f z))) s
      = ∫⁻ z in s, ENNReal.ofReal P * ENNReal.ofReal (f z) ∂ν := by
        rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ z in s, ⨆ k, F k z ∂ν := by simp_rw [hFsup]
    _ = ⨆ k, ∫⁻ z in s, F k z ∂ν :=
        lintegral_iSup' hFm (ae_of_all _ hFmono)
    _ ≤ _ := iSup_le hFle

/-! ### The smooth Monge–Ampère measure as common measure -/

theorem continuousOn_realHessian' {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (a b : ComplexModel n) :
    ContinuousOn (fun z ↦ realHessian u z a b) U := by
  have h2 : ContinuousOn (iteratedFDeriv ℝ 2 u) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hu U.isOpen
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change ContinuousOn (fun z ↦ iteratedFDeriv ℝ 2 u z ![a, b]) U
  exact (continuous_eval_const ![a, b]).comp_continuousOn h2

/-- The Monge–Ampère density of a smooth function is continuous. -/
theorem continuousOn_smoothDensity' {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContinuousOn (smoothDensity u) U := by
  have hH (j k : Fin n) : ContinuousOn (fun z ↦ complexHessian u z j k) U := by
    have h00 := continuousOn_realHessian' hu (coordinateVector j) (coordinateVector k)
    have hII := continuousOn_realHessian' hu
      (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)
    have h0I := continuousOn_realHessian' hu
      (coordinateVector j) (Complex.I • coordinateVector k)
    have hI0 := continuousOn_realHessian' hu
      (Complex.I • coordinateVector j) (coordinateVector k)
    have ha : ContinuousOn (fun z ↦
        ((realHessian u z (coordinateVector j) (coordinateVector k) +
          realHessian u z (Complex.I • coordinateVector j)
            (Complex.I • coordinateVector k) : ℝ) : ℂ)) U :=
      Complex.continuous_ofReal.comp_continuousOn (h00.add hII)
    have hb : ContinuousOn (fun z ↦
        ((realHessian u z (coordinateVector j) (Complex.I • coordinateVector k) -
          realHessian u z (Complex.I • coordinateVector j)
            (coordinateVector k) : ℝ) : ℂ)) U :=
      Complex.continuous_ofReal.comp_continuousOn (h0I.sub hI0)
    unfold complexHessian
    exact (ha.div_const 4).add
      (((continuousOn_const : ContinuousOn (fun _ : ComplexModel n ↦ Complex.I) U).mul
        hb).div_const 4)
  have hmat : ContinuousOn (complexHessian u) U :=
    continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ hH j k
  have hdet : ContinuousOn (fun z ↦ (complexHessian u z).det) U :=
    continuous_id.matrix_det.comp_continuousOn hmat
  have hre : ContinuousOn (fun z ↦ (complexHessian u z).det.re) U :=
    Complex.continuous_re.comp_continuousOn hdet
  unfold smoothDensity
  exact (continuousOn_const.mul hre)

/-- **Dinew's inequality against a smooth Monge–Ampère measure** (the coordinate form of `ωⁿ`). -/
theorem mixedTruncationLimitMeasure_ge_smoothMeasure (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {g : ComplexModel n → ℝ} (hg : IsSmoothPshOn Ω g) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hμ : ∀ i, ENNReal.ofReal (c i) • smoothMeasure Ω g hg ≤
      truncationLimitMeasure Ω (u i) (hu i)) :
    ENNReal.ofReal (∏ i, c i ^ ((n : ℝ)⁻¹)) • smoothMeasure Ω g hg ≤
      mixedTruncationLimitMeasure Ω u hu :=
  mixedTruncationLimitMeasure_ge_withDensity hn hu (continuousOn_smoothDensity' hg.1) hc hμ

end SGPT.NPP.LogConcavityDinew
