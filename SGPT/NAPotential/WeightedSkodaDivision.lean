import SGPT.NAPotential.WeightedSkodaCorrection

/-!
# Division for a surjective tuple with an extra smooth psh weight

This is the Weyl-lemma and weighted-estimate continuation of
`WeightedSkodaCorrection`.  It produces actual holomorphic quotient functions
and retains the exact additional `exp(-ψ)` factor.  It is not a singular-weight
or common-zero division theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter MeasureTheory
open scoped Topology ComplexConjugate ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Okounkov.TranscendentalSkoda

/-- Smooth-weight Skoda division for actual holomorphic tuples without common
zeros.  The open set and estimate constant are independent of the functions
`G`, `f`, and `ψ`; all integrals carry the same original `exp(-ψ)` factor. -/
theorem exists_smooth_psh_weighted_skoda_division (n : ℕ) (hn : 0 < n)
    (D : Set (ComplexModel n)) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) (K : Set (ComplexModel n))
    (hK : IsCompact K) (hKD : K ⊆ D) (p : ℝ) (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
      ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ),
        (∀ i, DifferentiableOn ℂ (G i) D) →
        (∀ z ∈ D, 0 < generatorNormSq G z) →
      ∀ (f : ComplexModel n → ℂ), DifferentiableOn ℂ f D →
      ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D →
        PlurisubharmonicOn (fun z => (ψ z : EReal)) D →
        weightedSkodaInput G f p ψ D ≠ ⊤ →
      ∃ H : Fin R → ComplexModel n → ℂ,
        (∀ i, DifferentiableOn ℂ (H i) U) ∧
        (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
        (∫⁻ z in U, ENNReal.ofReal
          ((∑ i, ‖H i z‖ ^ 2) * generatorNormSq G z ^ (-p) * Real.exp (-ψ z))) ≤
          ENNReal.ofReal (2 + 2 * n / (p - n)) * weightedSkodaInput G f p ψ D := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := (p - n) / (2 * n) with htdef
  have ht : 0 < t := div_pos (by linarith) (by positivity)
  obtain ⟨D', U, lam₁, lam₂, hD'o, hD'D, hUo, hKU, hUD', hlam₁, hlam₂,
    hlam, hlamU, hcorr⟩ := exists_weighted_skoda_correction n hn D hDo hDc hDb K hK hKD p hp
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  refine ⟨U, hUo, hKU, hUD'.trans hD'sub, ?_⟩
  intro R G hG hpos f hf ψ hψ hpsh hI
  set I := weightedSkodaInput G f p ψ D with hIdef
  set Φ : ComplexModel n → ℝ := fun z => p * Real.log (generatorNormSq G z) + ψ z with hΦdef
  have hΦ : ContDiffOn ℝ ∞ Φ D := (contDiffOn_skodaWeight hDo hG hpos p).add hψ
  have hw₁ : ContinuousOn (fun z => Φ z + lam₁ z) D' :=
    (hΦ.continuousOn.mono hD'sub).add hlam₁
  obtain ⟨u, hu2, huker, hueq, hubd⟩ := hcorr R G hG hpos f hf ψ hψ hpsh hI
  have hLcont : ∀ i, ContinuousOn (skodaLift G f i) D := fun i =>
    (contDiffOn_skodaLift hDo hG hpos hf i).continuousOn
  have hHex : ∀ i, ∃ H : ComplexModel n → ℂ, DifferentiableOn ℂ H D' ∧
      ∀ᵐ z ∂(volume.restrict D'), skodaLift G f i z - u i z = H z := by
    intro i
    have hu₀loc : LocallyIntegrableOn (u i) D' :=
      SGPT.Foundations.Analysis.Pending.OTChen.locallyIntegrableOn_of_memLp_weightedVolume hD'o hw₁
        (hu2 i)
    have haloc : LocallyIntegrableOn (skodaLift G f i) D' :=
      ((hLcont i).mono hD'sub).locallyIntegrableOn hD'o.measurableSet
    have hFloc : LocallyIntegrableOn (fun z => skodaLift G f i z - u i z) D' := haloc.sub hu₀loc
    have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
        ∫ z, (skodaLift G f i z - u i z) * dbarDir (coordVec j) h z = 0 := by
      intro h hh j
      have hdc : Continuous (dbarDir (coordVec j) h) :=
        SGPT.Foundations.Analysis.Pending.OTChen.continuous_dbarDir'
          (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
      have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
      have hdts := (SGPT.Foundations.Analysis.Pending.OTChen.tsupport_dbarDir_subset (coordVec j) h).trans
        hh.2.2
      have i1 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn haloc hdc
        hdcs hdts
      have i2 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn hu₀loc
        hdc hdcs hdts
      simp only [sub_mul]
      rw [integral_sub i1 i2, weakDbarEq_skodaLift hDo hD'sub hG hpos hf i h hh j, hueq i h hh j]
      ring
    exact SGPT.Foundations.Analysis.Pending.exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
      (SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  choose H hHhol hHae using hHex
  have hHae' : ∀ᵐ z ∂(volume.restrict D'), ∀ i, skodaLift G f i z - u i z = H i z :=
    ae_all_iff.mpr hHae
  have hid : EqOn f (fun z => ∑ i, G i z * H i z) D' := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hD'o (hf.continuousOn.mono hD'sub) ?_
    · filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with z hz hzk hzD
      simp_rw [← hz, mul_sub, Finset.sum_sub_distrib, hzk, sub_zero]
      exact (sum_mul_skodaLift hpos f (hD'sub hzD)).symm
    · exact continuousOn_finsetSum _ fun i _ =>
        ((hG i).continuousOn.mono hD'sub).mul (hHhol i).continuousOn
  have hpyth : ∀ᵐ z ∂(volume.restrict D'), ∑ i, ‖H i z‖ ^ 2 =
      ‖f z‖ ^ 2 / generatorNormSq G z + ∑ i, ‖u i z‖ ^ 2 := by
    filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with z hz hzk hzD
    simp_rw [← hz]
    exact skoda_pythagoras (hpos z (hD'sub hzD)) hzk
  refine ⟨H, fun i => (hHhol i).mono hUD', fun z hz => hid (hUD' hz), ?_⟩
  have hexpΦ : ∀ z ∈ D, Real.exp (-Φ z) =
      generatorNormSq G z ^ (-p) * Real.exp (-ψ z) := by
    intro z hz
    rw [Real.rpow_def_of_pos (hpos z hz)]
    simp only [hΦdef]
    rw [show -(p * Real.log (generatorNormSq G z) + ψ z) =
      Real.log (generatorNormSq G z) * (-p) + -ψ z by ring, Real.exp_add]
  have hu_int : Integrable (fun z => (∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z)))
      (volume.restrict D') := by
    have h := integrable_finsetSum Finset.univ fun i _ =>
      integrable_sq_mul_exp_of_memLp hD'o hw₁ (hu2 i)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Finset.sum_mul]
  have hupart : ∫⁻ z in U, ENNReal.ofReal
      ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) * Real.exp (-ψ z)) ≤
      ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
    calc
      _ = ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) := by
        refine setLIntegral_congr_fun hUo.measurableSet fun z hz => ?_
        rw [(hlamU z hz).1, add_zero, hexpΦ z (hD'sub (hUD' hz))]
        congr 1
        ring
      _ ≤ ∫⁻ z in D', ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
        lintegral_mono_set hUD'
      _ = ENNReal.ofReal (∫ z in D', (∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
        (ofReal_integral_eq_lintegral_ofReal hu_int (Filter.Eventually.of_forall fun z =>
          mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)).symm
      _ ≤ ENNReal.ofReal (((1 + t) * t⁻¹) * I.toReal) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [hΦdef, htdef, hIdef, mul_assoc] using hubd
      _ = ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hI]
  have hfmeas : AEMeasurable (fun z => ENNReal.ofReal
      (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z)))
      (volume.restrict U) := by
    have hc : ContinuousOn (fun z =>
        ‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z)) U := by
      refine (((hf.continuousOn.mono (hUD'.trans hD'sub)).norm.pow 2).mul ?_).mul ?_
      · exact ContinuousOn.rpow_const ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono
          (hUD'.trans hD'sub)) fun z hz => Or.inl (hpos z (hD'sub (hUD' hz))).ne'
      · exact Real.continuous_exp.comp_continuousOn ((hψ.continuousOn.mono
          (hUD'.trans hD'sub)).neg)
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hUo.measurableSet
  have hpythU := ae_restrict_of_ae_restrict_of_subset hUD' hpyth
  calc
    _ = ∫⁻ z in U, ENNReal.ofReal
        (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z) +
          (∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) * Real.exp (-ψ z)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hpythU, ae_restrict_mem hUo.measurableSet] with z hz hzU
      have hS := hpos z (hD'sub (hUD' hzU))
      rw [hz]
      congr 1
      rw [Real.rpow_neg hS.le, Real.rpow_neg hS.le, Real.rpow_add hS, Real.rpow_one]
      field_simp
    _ ≤ ∫⁻ z in U, (ENNReal.ofReal
        (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z)) +
        ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) * Real.exp (-ψ z))) :=
      lintegral_mono fun z => ENNReal.ofReal_add_le
    _ = (∫⁻ z in U, ENNReal.ofReal
        (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z))) +
        ∫⁻ z in U, ENNReal.ofReal
          ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) * Real.exp (-ψ z)) :=
      lintegral_add_left' hfmeas _
    _ ≤ I + ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
      gcongr
      exact lintegral_mono_set (hUD'.trans hD'sub)
    _ = ENNReal.ofReal (2 + 2 * n / (p - n)) * I := by
      have hval : 2 + 2 * (n : ℝ) / (p - n) = 1 + (1 + t) * t⁻¹ := by
        have hpn : p - n ≠ 0 := by linarith
        have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
        simp only [htdef]
        field_simp
        ring
      rw [hval, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
      ring

end SGPT.NAPotential.GAGAMult
