import SGPT.NAPotential.WeightedSkodaCurvature
import SGPT.Okounkov.TranscendentalSkodaTwisted

/-!
# The kernel-bundle correction for a smooth psh extra weight

This is the integral-estimate half of the weighted Skoda route.  It applies
the proved kernel-bundle Hörmander estimate to the actual Skoda lift, with
weight `p log |G|² + ψ`.  No solution, output bound, or division result is
assumed.  The hypothesis is finiteness of the genuine weighted input integral.  The
resulting correction is a kernel-valued weak solution with the quantitative
bound needed for the later holomorphic division argument.

The original tuple is assumed surjective on `D`, and `ψ` is smooth psh.
Neither arbitrary singular psh weights nor tuples with common zeros are
covered here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter MeasureTheory
open scoped Topology ComplexConjugate ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Okounkov.TranscendentalSkoda

/-- Weighted Skoda numerator for an actual surjective holomorphic tuple. -/
def weightedSkodaInput {n R : ℕ} (G : Fin R → ComplexModel n → ℂ)
    (f : ComplexModel n → ℂ) (p : ℝ) (ψ : ComplexModel n → ℝ)
    (D : Set (ComplexModel n)) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal
    (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z))

/-- The smooth psh weight is admitted by the existing kernel-bundle estimate,
and the resulting solution has a bound by the literal weighted input integral.
The domains and cutoff shifts depend only on `D`, `K`, `n`, and `p`, so the
bound has no dependence on the size or oscillation of `ψ`. -/
theorem exists_weighted_skoda_correction (n : ℕ) (hn : 0 < n)
    (D : Set (ComplexModel n)) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) (K : Set (ComplexModel n))
    (hK : IsCompact K) (hKD : K ⊆ D) (p : ℝ) (hp : (n : ℝ) < p) :
    ∃ (D' U : Set (ComplexModel n)) (lam₁ lam₂ : ComplexModel n → ℝ),
      IsOpen D' ∧ closure D' ⊆ D ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ D' ∧
      ContinuousOn lam₁ D' ∧ ContinuousOn lam₂ D' ∧
      (∀ z ∈ D', 0 ≤ lam₁ z ∧ lam₁ z ≤ lam₂ z) ∧
      (∀ z ∈ U, lam₁ z = 0 ∧ lam₂ z = 0) ∧
      ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ),
        (∀ i, DifferentiableOn ℂ (G i) D) →
        (∀ z ∈ D, 0 < generatorNormSq G z) →
      ∀ (f : ComplexModel n → ℂ), DifferentiableOn ℂ f D →
      ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D →
        PlurisubharmonicOn (fun z => (ψ z : EReal)) D →
        weightedSkodaInput G f p ψ D ≠ ⊤ →
      ∃ u : Fin R → ComplexModel n → ℂ,
        (∀ i, MemLp (u i) 2 (weightedVolume D' fun z =>
          p * Real.log (generatorNormSq G z) + ψ z + lam₁ z)) ∧
        (∀ᵐ z ∂(volume.restrict D'), ∑ i, G i z * u i z = 0) ∧
        (∀ i, WeakDbarEq D' (u i) (skodaForm G f i)) ∧
        ∫ z in D', (∑ i, ‖u i z‖ ^ 2) *
            Real.exp (-(p * Real.log (generatorNormSq G z) + ψ z + lam₁ z)) ≤
          (1 + (p - n) / (2 * n)) * ((p - n) / (2 * n))⁻¹ *
            (weightedSkodaInput G f p ψ D).toReal := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := (p - n) / (2 * n) with htdef
  have ht : 0 < t := div_pos (by linarith) (by positivity)
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'D, hUo, hKU, hUD', hlam₁, hlam₂,
    hlam, hlamU, hmain⟩ :=
    twistedHormanderStatement n D hDo hDc hDb K hK hKD t ht
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  refine ⟨D', U, lam₁, lam₂, hD'o, hD'D, hUo, hKU, hUD', hlam₁, hlam₂,
    hlam, hlamU, ?_⟩
  intro R G hG hpos f hf ψ hψ hpsh hI
  set I := weightedSkodaInput G f p ψ D with hIdef
  set Φ : ComplexModel n → ℝ := fun z => p * Real.log (generatorNormSq G z) + ψ z with hΦdef
  have hΦ : ContDiffOn ℝ ∞ Φ D := (contDiffOn_skodaWeight hDo hG hpos p).add hψ
  have hclc : IsCompact (closure D') :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hDb.subset hD'D)
  have hD'b : Bornology.IsBounded D' := hDb.subset hD'sub
  have hcurv : ∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      (1 + t) * secondFundamental G z α ≤ vectorLevi Φ z α := by
    intro z hz α hα
    have h := skoda_curvature_add_smooth_psh hDo hn hG hpos hp hψ hpsh hz hα
    have hB : 0 ≤ secondFundamental G z α :=
      div_nonneg (sq_nonneg _) (generatorNormSq_nonneg G z)
    have htb : 0 ≤ ((p - n) / (2 * n)) * secondFundamental G z α :=
      mul_nonneg (by simpa only [htdef] using ht.le) hB
    linarith
  have hvcont : ∀ i j, ContinuousOn (skodaForm G f i j) D := fun i j =>
    (contDiffOn_dbarDir hDo (contDiffOn_skodaLift hDo hG hpos hf i) _).continuousOn
  have hvbd : ∀ i j, ∃ C, ∀ z ∈ D', ‖skodaForm G f i j z‖ ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ := hclc.exists_bound_of_continuousOn ((hvcont i j).mono hD'D)
    exact ⟨C, fun z hz => hC z (subset_closure hz)⟩
  obtain ⟨B, hB⟩ := hclc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hD'D)
  have hw₂ : ContinuousOn (fun z => Φ z + lam₂ z) D' :=
    (hΦ.continuousOn.mono hD'sub).add hlam₂
  have hw₁ : ContinuousOn (fun z => Φ z + lam₁ z) D' :=
    (hΦ.continuousOn.mono hD'sub).add hlam₁
  have hv : ∀ i j, MemLp (skodaForm G f i j) 2 (weightedVolume D' fun z => Φ z + lam₂ z) := by
    intro i j
    obtain ⟨C, hC⟩ := hvbd i j
    refine memLp_weightedVolume_of_bounded hD'o hD'b hw₂ (B := B) (fun z hz => ?_)
      (((hvcont i j).mono hD'sub).aestronglyMeasurable hD'o.measurableSet) hC
    have h1 := hB z (subset_closure hz)
    rw [Real.norm_eq_abs] at h1
    linarith [(abs_le.mp h1).1, (hlam z hz).1, (hlam z hz).2]
  have hvker : ∀ z ∈ D', InKernel G z fun i j => skodaForm G f i j z :=
    fun z hz j => sum_mul_skodaForm hDo hG hpos hf (hD'sub hz) j
  have hvcl : ∀ i, WeakDbarClosed D' (skodaForm G f i) :=
    fun i => weakDbarClosed_skodaForm hDo hD'sub hG hpos hf i
  set g : ComplexModel n → ℝ := fun z => ‖f z‖ ^ 2 / (t * generatorNormSq G z) with hgdef
  have hg0 : ∀ z ∈ D', 0 ≤ g z := fun z _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg ht.le (generatorNormSq_nonneg G z))
  have hgb : ∀ z ∈ D', ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      ‖∑ i, ∑ j, conj (α i j) * skodaForm G f i j z‖ ^ 2 ≤
        g z * (vectorLevi Φ z α - (1 + t) * secondFundamental G z α) := by
    intro z hz α hα
    simpa only [hgdef, hΦdef, htdef] using
      skodaForm_twisted_bound_add_smooth_psh hDo hn hG hpos hf hp hψ hpsh (hD'sub hz) hα
  have hgle : ∀ z ∈ D', g z * Real.exp (-(Φ z + lam₁ z)) ≤
      (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) / t) * Real.exp (-ψ z) := by
    intro z hz
    simpa only [hgdef, hΦdef] using
      (skoda_g_mul_exp_add_shift_le (p := p) (ψ := ψ z)
        (hpos z (hD'sub hz)) ht (sq_nonneg ‖f z‖) (hlam z hz).1)
  have hIt : ∫⁻ z in D', ENNReal.ofReal
      ((‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) / t) * Real.exp (-ψ z)) ≤
      ENNReal.ofReal t⁻¹ * I := by
    calc
      _ = ∫⁻ z in D', ENNReal.ofReal t⁻¹ * ENNReal.ofReal
          (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z)) := by
            refine lintegral_congr fun z => ?_
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
            congr 1
            ring
      _ = ENNReal.ofReal t⁻¹ * ∫⁻ z in D', ENNReal.ofReal
          (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t⁻¹ * I := by
        gcongr
        exact lintegral_mono_set hD'sub
  have hgmeas : AEStronglyMeasurable (fun z => g z * Real.exp (-(Φ z + lam₁ z)))
      (volume.restrict D') := by
    have hgc : ContinuousOn g D' := by
      refine ContinuousOn.div ((hf.continuousOn.mono hD'sub).norm.pow 2)
        (continuousOn_const.mul ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono hD'sub))
        fun z hz => (mul_pos ht (hpos z (hD'sub hz))).ne'
    exact (hgc.mul (Real.continuous_exp.comp_continuousOn hw₁.neg)).aestronglyMeasurable
      hD'o.measurableSet
  have hgint : Integrable (fun z => g z * Real.exp (-(Φ z + lam₁ z))) (volume.restrict D') := by
    refine ⟨hgmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · refine lt_of_le_of_lt (setLIntegral_mono' hD'o.measurableSet fun z hz =>
        ENNReal.ofReal_le_ofReal (hgle z hz)) (lt_of_le_of_lt hIt ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hI)
    · filter_upwards [ae_restrict_mem hD'o.measurableSet] with z hz
      exact mul_nonneg (hg0 z hz) (Real.exp_pos _).le
  obtain ⟨u, hu2, huker, hueq, hubd⟩ :=
    hmain R G hG hpos Φ hΦ hcurv (skodaForm G f) hv hvker hvcl g hg0 hgb hgint
  have hgI : ∫ z in D', g z * Real.exp (-(Φ z + lam₁ z)) ≤ t⁻¹ * I.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem hD'o.measurableSet] with z hz
      exact mul_nonneg (hg0 z hz) (Real.exp_pos _).le) hgmeas]
    have h1 : ∫⁻ z in D', ENNReal.ofReal (g z * Real.exp (-(Φ z + lam₁ z))) ≤
        ENNReal.ofReal t⁻¹ * I :=
      (setLIntegral_mono' hD'o.measurableSet fun z hz =>
        ENNReal.ofReal_le_ofReal (hgle z hz)).trans hIt
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)] at h2
  refine ⟨u, ?_, huker, hueq, ?_⟩
  · simpa only [hΦdef] using hu2
  · have h := hubd.trans (mul_le_mul_of_nonneg_left hgI (by linarith : 0 ≤ 1 + t))
    simpa only [hΦdef, htdef, hIdef, mul_assoc] using h

end SGPT.NAPotential.GAGAMult
