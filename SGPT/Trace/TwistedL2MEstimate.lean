import SGPT.Trace.TwistedL2MApriori

/-!
# The twisted a priori estimate for finite families of local pieces on `ℂⁿ`

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:apriori`).  Combining the integrated twisted
inequality with the data bound and a Cauchy--Schwarz inequality: for a twisted datum `T` on
`X = ℂⁿ` with finite data energy `M = ∫_U D e^{-φ} dμ` and a finite family of local test pieces
`h_i ⊗ e_i`,

`|∑_i ⟨∂̄G, h_i ⊗ e_i⟩|² ≤ M · (‖T*(∑_i h_i ⊗ e_i)‖² + Q)`,

with `Q = -Re ∫ tr(A_W Ā_W) a e^{-φ}` (`apriori`), and `‖T* τ‖²` is the `H₁` norm of the actual
section `∑_i localTStar_i` (`lintegral_tstar_eq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ContDiff ComplexConjugate Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}
  (hρ : IsChartDensity T.μ chart0 ρ)
  {ι : Type} {s : Finset ι} {e : ι → AtlasFrame T.L} {h : ι → ComplexModel n → ComplexModel n}
  (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))

include hρ hh

theorem sum_localDataPairing_eq :
    ∑ i ∈ s, T.localDataPairing chart0 (e i) ρ (h i) = ∫ z, T.Φ (T.FD ρ) s e h z := by
  unfold Φ
  rw [integral_finsetSum _ fun i _ => T.integrable_piece hh (isGaugeForm_data hρ) i]
  rfl

/-- The `H₁`-energy of the actual sections `T*(h_i ⊗ e_i)` (`localTStar`) is the integral of the
`T*`-form. -/
theorem norm_sq_sum_localTStar {z : ComplexModel n} (hz : z ∈ T.U) :
    ‖∑ i ∈ s, T.localTStar chart0 (e i) ρ (h i) z‖ ^ 2 * T.H1weight z * ρ z =
      (T.Φ (T.FA ρ) s e h z).re := by
  set e₀ := atlasFrameAt T.L z
  have hz₀ : z ∈ T.dom e₀ := frameAt_mem_dom hz
  have hzb : z ∈ e₀.val.baseSet := ((T.mem_dom).mp hz₀).1
  have hterm : ∀ i ∈ s, T.localTStar chart0 (e i) ρ (h i) z =
      (((T.a z + T.b z : ℝ) : ℂ) * chartTheta (T.pW ρ e₀) (transp T.L (e i) e₀ (h i)) z) •
        e₀.val.symm z 1 := by
    intro i _
    by_cases hzi : z ∈ (e i).val.baseSet
    · have hzdi : z ∈ T.dom (e i) := (T.mem_dom).mpr ⟨hzi, hz⟩
      have hxs : z ∈ (chart0 (n := n)).val.source ∩ (e i).val.baseSet := ⟨mem_univ z, hzi⟩
      rw [T.localTStar_of_mem hxs]
      simp only [pieceTheta, chart0_apply, chart0_symm_apply]
      have g := T.gaugeData_pW (ρ := ρ) e₀ (e i)
      have hp : DifferentiableAt ℝ (T.pW ρ e₀) z :=
        (pW_contDiffAt hρ hz₀).differentiableAt (by simp)
      have hθ : chartTheta (localWeight T.L chart0 (e i) ρ T.φ) (h i) z =
          frameTrans T.L e₀ (e i) z * chartTheta (T.pW ρ e₀) (transp T.L (e i) e₀ (h i)) z := by
        rw [chartTheta_congr (eventuallyEq_frameTrans_smul_transp (T.tsupport_subset_base hh i)
          ⟨hzb, hzi⟩)]
        exact chartTheta_gauge g ⟨hz₀, hzdi⟩ hp
          ((T.contDiffAt_transp hh i hzb).differentiableAt (by simp))
      rw [hθ, frame_eq_frameTrans_smul (e i) e₀ ⟨hzi, hzb⟩, smul_smul]
      congr 1
      have h1 := frameTrans_mul_symm e₀ (e i) ⟨hzb, hzi⟩
      linear_combination (((T.a z + T.b z : ℝ) : ℂ) *
        chartTheta (T.pW ρ e₀) (transp T.L (e i) e₀ (h i)) z) * h1
    · have hzs : z ∉ tsupport (h i) := fun h' => hzi (T.tsupport_subset_base hh i h')
      have hxs : z ∉ (chart0 (n := n)).val.source ∩ (e i).val.baseSet := fun h' => hzi h'.2
      rw [TwistedDatum.localTStar, if_neg hxs,
        chartTheta_eq_zero_of_eventuallyEq (transp_eventuallyEq_zero hzs), mul_zero, zero_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← Finset.mul_sum,
    ← chartTheta_finset_sum s fun i _ => (T.contDiffAt_transp hh i hzb).differentiableAt (by simp)]
  change ‖(((T.a z + T.b z : ℝ) : ℂ) * chartTheta (T.pW ρ e₀) (T.tot s e h e₀) z) •
    e₀.val.symm z 1‖ ^ 2 * T.H1weight z * ρ z = _
  rw [Φ_eq_diag hh (isGaugeForm_tstar hρ) hz, FA_diag_re, norm_smul, mul_pow, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (T.ab_pos hz).le]
  have hexp := T.exp_neg_localWeight e₀ hρ hz₀.1
  simp only [chart0_symm_apply] at hexp
  change _ = _ * _ * Real.exp (-localWeight T.L chart0 e₀ ρ T.φ z)
  rw [hexp, H1weight]
  have hab := (T.ab_pos hz).ne'
  simp only [frameNormSq]
  field_simp
  ring

theorem FA_re_nonneg (z : ComplexModel n) : 0 ≤ (T.Φ (T.FA ρ) s e h z).re := by
  by_cases hz : z ∈ T.U
  · rw [Φ_eq_diag hh (isGaugeForm_tstar hρ) hz, FA_diag_re]
    exact mul_nonneg (mul_nonneg (T.ab_pos hz).le (sq_nonneg _)) (Real.exp_pos _).le
  · simp [Φ_eq_zero hh (isGaugeForm_tstar hρ) hz]

omit hρ in
theorem localTStar_eq_zero_of_notMem {z : ComplexModel n} (hz : z ∉ T.U) (i : ι) :
    T.localTStar chart0 (e i) ρ (h i) z = 0 := by
  refine T.localTStar_eq_zero fun hzs => hz ?_
  exact (T.pieceSupport_subset (hh i) hzs).1

/-- **`‖T* τ‖²` as an integral over `ℂⁿ`.** -/
theorem lintegral_tstar_eq :
    ∫⁻ x in T.U, ENNReal.ofReal (‖∑ i ∈ s, T.localTStar chart0 (e i) ρ (h i) x‖ ^ 2 *
        T.H1weight x) ∂T.μ = ENNReal.ofReal (∫ z, (T.Φ (T.FA ρ) s e h z).re) := by
  have iA : Integrable (fun z => (T.Φ (T.FA ρ) s e h z).re) :=
    (T.integrable_sum_pieces (s := s) hh (isGaugeForm_tstar hρ)).re
  have hρm : Measurable fun z => ENNReal.ofReal (ρ z) :=
    ENNReal.measurable_ofReal.comp (continuous_of_isChartDensity hρ).measurable
  rw [← lintegral_indicator T.isOpen_U.measurableSet, measure_eq_withDensity hρ,
    lintegral_withDensity_eq_lintegral_mul_non_measurable volume hρm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ofReal_integral_eq_lintegral_ofReal iA (Eventually.of_forall (FA_re_nonneg hρ hh))]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  by_cases hz : z ∈ T.U
  · rw [indicator_of_mem hz, ← ENNReal.ofReal_mul (pos_of_isChartDensity hρ z).le,
      ← norm_sq_sum_localTStar hρ hh hz]
    ring_nf
  · rw [indicator_of_notMem hz, mul_zero, Φ_eq_zero hh (isGaugeForm_tstar hρ) hz]
    simp

/-- **The twisted a priori estimate on `ℂⁿ`** (`claude-tl2-main:apriori`). -/
theorem apriori
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ‖∑ i ∈ s, T.localDataPairing chart0 (e i) ρ (h i)‖ ^ 2 ≤
      (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
        ((∫ z, (T.Φ (T.FA ρ) s e h z).re) - (∫ z, T.Φ (T.FT ρ) s e h z).re) := by
  set M := (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal with hM
  set k : ComplexModel n → ℝ := fun z => ‖T.Φ (T.FD ρ) s e h z‖ with hk
  set g : ComplexModel n → ℝ := fun z => (T.Φ (T.FH ρ) s e h z).re with hg
  set f : ComplexModel n → ℝ := fun z => k z ^ 2 / g z with hf
  have iD : Integrable (fun z => T.Φ (T.FD ρ) s e h z) :=
    T.integrable_sum_pieces (s := s) hh (isGaugeForm_data hρ)
  have ik : Integrable k := iD.norm
  have ig : Integrable g := (T.integrable_sum_pieces (s := s) hh (isGaugeForm_curv hρ)).re
  have hg0 : ∀ z, 0 ≤ g z := curv_nonneg hρ hh
  have hk0 : ∀ z, 0 ≤ k z := fun z => norm_nonneg _
  have hf0 : ∀ z, 0 ≤ f z := fun z => div_nonneg (sq_nonneg _) (hg0 z)
  have hdata := data_sq_le hρ hh (s := s)
  have hkfg : ∀ z, k z ^ 2 ≤ f z * g z := by
    intro z
    by_cases hgz : g z = 0
    · have := hdata z
      change k z ^ 2 ≤ _ * g z at this
      rw [hgz, mul_zero] at this
      rw [hgz, mul_zero]
      exact this
    · rw [hf, div_mul_cancel₀ _ hgz]
  have hfm : Measurable f := by
    have hkc : Continuous k := (continuous_finsetSum s fun i _ =>
      T.continuous_piece hh (isGaugeForm_data hρ) i).norm
    have hgc : Continuous g := Complex.continuous_re.comp (continuous_finsetSum s fun i _ =>
      T.continuous_piece hh (isGaugeForm_curv hρ) i)
    exact (hkc.measurable.pow_const 2).div hgc.measurable
  -- the lower integral bound by the data energy
  have hpt : ∀ z, ENNReal.ofReal (f z) ≤ ENNReal.ofReal (ρ z) *
      T.U.indicator (fun x => ENNReal.ofReal (T.D x * Real.exp (-T.φ x))) z := by
    intro z
    rcases (hf0 z).eq_or_lt with h0 | hpos
    · rw [← h0, ENNReal.ofReal_zero]; exact bot_le
    · have hgz : 0 < g z := by
        rcases (hg0 z).eq_or_lt with h' | h'
        · exfalso; simp [hf, ← h'] at hpos
        · exact h'
      have hle : f z ≤ T.U.indicator (fun x => T.D x * Real.exp (-T.φ x)) z * ρ z := by
        rw [hf, div_le_iff₀ hgz]
        exact hdata z
      by_cases hz : z ∈ T.U
      · rw [indicator_of_mem hz] at hle ⊢
        rw [← ENNReal.ofReal_mul (pos_of_isChartDensity hρ z).le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · rw [indicator_of_notMem hz, zero_mul] at hle
        linarith
  have hρm : Measurable fun z => ENNReal.ofReal (ρ z) :=
    ENNReal.measurable_ofReal.comp (continuous_of_isChartDensity hρ).measurable
  have hlint : ∫⁻ z, ENNReal.ofReal (f z) ≤
      ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ := by
    calc ∫⁻ z, ENNReal.ofReal (f z)
        ≤ ∫⁻ z, ENNReal.ofReal (ρ z) *
            T.U.indicator (fun x => ENNReal.ofReal (T.D x * Real.exp (-T.φ x))) z :=
          lintegral_mono hpt
      _ = ∫⁻ z, T.U.indicator (fun x => ENNReal.ofReal (T.D x * Real.exp (-T.φ x))) z
            ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z)) :=
          (lintegral_withDensity_eq_lintegral_mul_non_measurable volume hρm
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _).symm
      _ = _ := by
        rw [← measure_eq_withDensity hρ, lintegral_indicator T.isOpen_U.measurableSet]
  have ifn : Integrable f :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).mpr
      (hlint.trans_lt hfin)⟩
  have hfM : ∫ z, f z ≤ M := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_mono hfin.ne hlint
  have hCS := sq_integral_le_of_sq_le_mul ifn ig ik hf0 hg0 hk0 hkfg
  have hcurv := integral_curv_le hρ hh (s := s)
  have hgI : 0 ≤ ∫ z, g z := integral_nonneg hg0
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hnorm : ‖∑ i ∈ s, T.localDataPairing chart0 (e i) ρ (h i)‖ ≤ ∫ z, k z := by
    rw [sum_localDataPairing_eq hρ hh]
    exact norm_integral_le_integral_norm _
  have h1 : ‖∑ i ∈ s, T.localDataPairing chart0 (e i) ρ (h i)‖ ^ 2 ≤ (∫ z, k z) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ‖∑ i ∈ s, T.localDataPairing chart0 (e i) ρ (h i)‖ ^ 2 ≤ (∫ z, k z) ^ 2 := h1
    _ ≤ (∫ z, f z) * ∫ z, g z := hCS
    _ ≤ M * ∫ z, g z := mul_le_mul_of_nonneg_right hfM hgI
    _ ≤ M * ((∫ z, (T.Φ (T.FA ρ) s e h z).re) - (∫ z, T.Φ (T.FT ρ) s e h z).re) :=
      mul_le_mul_of_nonneg_left hcurv hM0

end TwistedDatum

end SGPT.Trace.TwistedL2
