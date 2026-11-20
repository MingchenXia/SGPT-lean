import SGPT.NPP.LogConcavityDinewLinear
import SGPT.NPP.LogConcavityMixedDiscriminant
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotMonotoneMeasure
import SGPT.Foundations.Analysis.Pending.SmoothBedfordTaylorMeasure

/-!
# Dinew's inequality for bounded plurisubharmonic functions

FPT `cor:bounded-multifactor-continuous-density` with constant densities: let `u₁, …, uₙ` be
locally bounded plurisubharmonic functions on `Ω ⊆ ℂⁿ` with `(ddᶜuᵢ)ⁿ ≥ cᵢ · (n!/πⁿ) dV`, `cᵢ > 0`.
Then on every ball `B(x₀, R/4)` with `B̄(x₀, R) ⊆ Ω`,
`ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ cᵢ^{1/n}) · (n!/πⁿ) dV` (`mixedBedfordTaylor_ge_on_ball`).

Proof (FPT, `prop:bounded-monge-ampere-linear-density`): the radial mollifications `uᵢ * ρⱼ` of
TN's `RadialConvolutionSystem` decrease to `uᵢ`; by the linear inequalities along all frames
(`integral_mul_frameLevi_ge`) their complex Hessians satisfy `det ≥ cᵢ`
(`pow_le_det_of_forall_frame`); the geometric-mean inequality for mixed discriminants (S50,
`factorial_mul_prod_det_rpow_le_mixedCoefficient_re`) bounds the mixed densities from below; and
the canonical mixed Bedford–Taylor measure is the vague limit of the smooth mixed measures along
any decreasing approximation (TN `canonicalMixedBedfordTaylorMeasure_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ContDiff
open TopologicalSpace

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

variable {n : ℕ}

/-- **Mollifications with a determinant bound.** -/
theorem exists_decreasingApproximation_det_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c)
    (hμ : ENNReal.ofReal (mongeAmpereConst n * c) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω) :
    ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation ⟨Metric.ball x₀ (R / 4), Metric.isOpen_ball⟩ u f ∧
      ∀ j, ∀ z ∈ Metric.ball x₀ (R / 4), c ≤ (complexHessian (f j) z).det.re := by
  set N : Set (ComplexModel n) := Metric.ball x₀ (R / 4) with hNdef
  set K : Set (ComplexModel n) := Metric.closedBall x₀ (3 * R / 8) with hKdef
  have hN : IsOpen N := Metric.isOpen_ball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKΩ : K ⊆ Ω := (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hNΩ : N ⊆ Ω := Metric.ball_subset_closedBall.trans
    ((Metric.closedBall_subset_closedBall (by linarith)).trans hball)
  have hballK : ∀ x ∈ N, Metric.closedBall x (R / 8) ⊆ K := by
    intro x hx y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have : dist x x₀ < R / 4 := hx
    linarith [dist_triangle y x x₀]
  have hR8 : (0 : ℝ) < R / 8 := by positivity
  let hpL : LocallyIntegrableOn u Ω volume := locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hpLevi : HasNonnegativeDistributionalLevi (regularDistribution volume u hpL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  obtain ⟨S, -⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh hu hR8 hN hNΩ hK
    hKΩ hballK
  let f : ℕ → ComplexModel n → ℝ := fun j ↦ translationPairing volume (K.indicator u) (S.kernel j)
  have hg : LocallyIntegrable (K.indicator u) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hK hKΩ).locallyIntegrable
  have hfDisc (j : ℕ) : DiscPshOn (fun x ↦ (f j x : EReal)) N :=
    discPshOn_translationPairing_indicator hpL hpLevi (S.kernel_hasCompactSupport j)
      (S.kernel_contDiff j) (S.kernel_nonneg j) hK hKΩ (S.translated_tsupport j)
  have hfPsh (j : ℕ) : PlurisubharmonicOn (fun x ↦ (f j x : EReal)) N :=
    (hfDisc j).plurisubharmonicOn hN
  have hfC (j : ℕ) : ContDiff ℝ ∞ (f j) :=
    contDiff_translationPairing hg (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
  have hfSmooth (j : ℕ) : IsSmoothPshOn ⟨N, hN⟩ (f j) :=
    FirstPass.MongeAmpere.isSmoothPshOn_of_psh (hfC j).contDiffOn (hfPsh j)
  have hanti : ∀ x ∈ N, Antitone (fun j ↦ f j x) := fun x hx => S.antitone_pairing x hx
  have hpoint : ∀ x ∈ N, Tendsto (fun j ↦ f j x) atTop (𝓝 (u x)) :=
    tendsto_everywhere_of_ae_of_antitone_psh (hu.1.mono hNΩ) hfPsh hanti S.ae_tendsto_pairing
  refine ⟨f, ⟨hfSmooth, hanti, hpoint⟩, fun j z hz => ?_⟩
  -- the frame inequalities for the mollification
  have hf2 : ContDiffAt ℝ 2 (f j) z :=
    ((hfC j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hpsd : (complexHessian (f j) z).PosSemidef := (hfSmooth j).2.2 z hz
  have hκ2 : ContDiff ℝ 2 (S.kernel j) :=
    (S.kernel_contDiff j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  set χ : ComplexModel n → ℝ := fun x => S.kernel j (x - z) with hχ
  have hχd : ContDiff ℝ 2 χ := hκ2.comp (contDiff_id.sub contDiff_const)
  have hχc : HasCompactSupport χ := (S.kernel_hasCompactSupport j).comp_homeomorph
    (Homeomorph.subRight z)
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => S.kernel_nonneg j _
  have hχK : tsupport χ ⊆ K := S.translated_tsupport j z hz
  have hχsupp : tsupport χ ⊆ Metric.ball x₀ (R / 2) :=
    hχK.trans (Metric.closedBall_subset_ball (by linarith))
  have hχ1 : ∫ x, χ x = 1 := by
    rw [hχ, integral_sub_right_eq_self (fun x => S.kernel j x) z, S.kernel_integral_one j]
  have hframe : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ‖Y.det‖ = 1 →
      n * c ^ ((n : ℝ)⁻¹) ≤ (Yᴴ * complexHessian (f j) z * Y).trace.re := by
    intro Y hY
    rw [← sum_leviForm_frameMap hf2 Y]
    have hineq := integral_mul_frameLevi_ge hn hu hc hμ hR hball hY hχd hχc hχ0 hχsupp
    rw [hχ1, mul_one] at hineq
    refine hineq.trans (le_of_eq ?_)
    have hlev : ∀ v, leviForm (f j) z v =
        ∫ x, K.indicator u x * leviForm (S.kernel j) (x - z) v := fun v =>
      leviForm_translationPairing hg (S.kernel_hasCompactSupport j) hκ2 z v
    have hint : ∀ v, Integrable (fun x => K.indicator u x * leviForm (S.kernel j) (x - z) v) := by
      intro v
      have h1 := integrable_translationPairing_realHessian hg (S.kernel_hasCompactSupport j) hκ2 z
        v v
      have h2 := integrable_translationPairing_realHessian hg (S.kernel_hasCompactSupport j) hκ2 z
        (Complex.I • v) (Complex.I • v)
      refine ((h1.add h2).div_const 4).congr (ae_of_all _ fun x => ?_)
      simp only [leviForm, Pi.add_apply]
      ring
    simp only [hlev]
    rw [← integral_finsetSum _ (fun k _ => hint _)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [frameLevi, hχ, leviForm_comp_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · have hxs : x ∉ tsupport χ := fun h => hx (hχK h)
      have h0 : leviForm χ x (frameMap Y (coordinateVector k)) = 0 := by
        simp only [leviForm, realHessian_eq_zero_of_notMem_tsupport hxs, add_zero, zero_div]
      simp only [hχ, leviForm_comp_sub] at h0
      rw [h0]
      simp
  have := pow_le_det_of_forall_frame hn hpsd (Real.rpow_nonneg hc.le _) hframe
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hc.le, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
    Real.rpow_one] at this

theorem integral_le_of_measure_le_of_compactSupport {μ ν : Measure (ComplexModel n)} (hle : μ ≤ ν)
    {U : Set (ComplexModel n)} (hνU : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤)
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ z, 0 ≤ φ z) : ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν := by
  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hφc
  have hint : Integrable φ ν := by
    have hfin := hνU _ hφc.isCompact hφU
    have h1 : IntegrableOn φ (tsupport φ) ν := Measure.integrableOn_of_bounded hfin.ne
      hφ.aestronglyMeasurable (ae_of_all _ fun z => hB z)
    exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp h1
  exact integral_mono_measure hle (ae_of_all _ hφ0) hint

/-- **Dinew's inequality for bounded functions on a ball** (FPT
`cor:bounded-multifactor-continuous-density`, constant densities). -/
theorem mixedBedfordTaylor_ge_on_ball (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u) {c : Fin n → ℝ}
    (hc : ∀ i, 0 < c i)
    (hμ : ∀ i, ENNReal.ofReal (mongeAmpereConst n * c i) •
      volume.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω (u i) (hu i))
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω) :
    ENNReal.ofReal (mongeAmpereConst n * ∏ i, c i ^ ((n : ℝ)⁻¹)) •
        volume.restrict (Metric.ball x₀ (R / 4)) ≤
      (canonicalMixedBedfordTaylorMeasure Ω u hu).restrict (Metric.ball x₀ (R / 4)) := by
  choose f hf hdet using fun i =>
    exists_decreasingApproximation_det_ge hn (hu i) (hc i) (hμ i) hR hball
  set N : Opens (ComplexModel n) := ⟨Metric.ball x₀ (R / 4), Metric.isOpen_ball⟩ with hNdef
  set m : ℝ := mongeAmpereConst n * ∏ i, c i ^ ((n : ℝ)⁻¹) with hm
  set F : ℕ → Fin n → ComplexModel n → ℝ := fun j i => f i j with hFdef
  have hF : IsDecreasingMixedApproximation N u F :=
    ⟨fun j => isSmoothMixedPshOn_of_components (fun i => (hf i).1 j), fun i => (hf i).2.1,
      fun i => (hf i).2.2⟩
  have hNcl : closure (N : Set (ComplexModel n)) ⊆ Metric.closedBall x₀ (R / 4) :=
    Metric.closure_ball_subset_closedBall
  have hNrc : RelativelyCompactIn N Ω :=
    ⟨(isCompact_closedBall x₀ (R / 4)).of_isClosed_subset isClosed_closure hNcl,
      hNcl.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hball)⟩
  have hconv := canonicalMixedBedfordTaylorMeasure_tendsto hu hNrc hF
  -- the mixed density bound
  have hdens : ∀ j, ∀ z ∈ (N : Set (ComplexModel n)), m ≤ mixedDensity (F j) z := by
    intro j z hz
    set H : Fin n → Matrix (Fin n) (Fin n) ℂ := fun i => complexHessian (f i j) z with hH
    have hpd : ∀ i, (H i).PosDef := fun i => by
      have hpsd : (H i).PosSemidef := ((hf i).1 j).2.2 z hz
      refine (hpsd.posDef_iff_isUnit).mpr ?_
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h0
      have := hdet i j z hz
      have h0' : (complexHessian (f i j) z).det = 0 := h0
      rw [h0', Complex.zero_re] at this
      linarith [hc i]
    have hG := SGPT.NPP.LogConcavity.factorial_mul_prod_det_rpow_le_mixedCoefficient_re n H hpd
    have hprod : ∏ i, c i ^ ((n : ℝ)⁻¹) ≤ ∏ i, (H i).det.re ^ ((n : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hc i).le _) fun i _ => ?_
      exact Real.rpow_le_rpow (hc i).le (hdet i j z hz) (by positivity)
    simp only [mixedDensity, hm, mongeAmpereConst]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (pow_pos Real.pi_pos n)]
    have hfac : (0 : ℝ) ≤ n.factorial := by positivity
    calc (n.factorial : ℝ) * ∏ i, c i ^ ((n : ℝ)⁻¹)
        ≤ n.factorial * ∏ i, (H i).det.re ^ ((n : ℝ)⁻¹) := by gcongr
      _ ≤ _ := hG
  -- comparison of measures at each stage
  set ν : Measure (ComplexModel n) := ENNReal.ofReal m • volume.restrict (N : Set (ComplexModel n))
    with hν
  have hstage : ∀ j, ν ≤ smoothMixedMeasure N (F j) (hF.1 j) := by
    intro j
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [hν, Measure.smul_apply, smul_eq_mul, smoothMixedMeasure, withDensity_apply _ hs,
      ← setLIntegral_const]
    refine lintegral_mono_ae ?_
    have hmem : ∀ᵐ z ∂((volume.restrict (N : Set (ComplexModel n))).restrict s),
        z ∈ (N : Set (ComplexModel n)) := ae_restrict_of_ae (ae_restrict_mem N.isOpen.measurableSet)
    filter_upwards [hmem] with z hz
    exact ENNReal.ofReal_le_ofReal (hdens j z hz)
  have hνf : ∀ K, IsCompact K → K ⊆ (N : Set (ComplexModel n)) → ν K < ⊤ := fun K hK _ => by
    rw [hν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
  have hμf : ∀ K, IsCompact K → K ⊆ (N : Set (ComplexModel n)) →
      canonicalMixedBedfordTaylorMeasure Ω u hu K < ⊤ := fun K hK hKN =>
    canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hu hK (hKN.trans (subset_closure.trans hNrc.2))
  have htest : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (N : Set (ComplexModel n)) → (∀ z, 0 ≤ φ z) →
      ∫ z, φ z ∂ν ≤ ∫ z, φ z ∂(canonicalMixedBedfordTaylorMeasure Ω u hu) := by
    intro φ hφ hφc hφN hφ0
    refine ge_of_tendsto' (hconv φ hφ hφc hφN) fun j => ?_
    exact integral_le_of_measure_le_of_compactSupport (hstage j)
      (fun K hK hKN => smoothMixedMeasure_finiteOnCompacts (hF.1 j) hK hKN) hφ hφc hφN hφ0
  have hcpt : ∀ K, IsCompact K → K ⊆ (N : Set (ComplexModel n)) →
      ν K ≤ canonicalMixedBedfordTaylorMeasure Ω u hu K := fun K hK hKN =>
    BedfordTaylor.measure_le_of_testFunction_integral_le hνf hμf htest hK hKN
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, Measure.restrict_apply hs]
  have hsN : MeasurableSet (s ∩ Metric.ball x₀ (R / 4)) := hs.inter measurableSet_ball
  have hfin : volume (s ∩ Metric.ball x₀ (R / 4)) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  rw [hsN.measure_eq_iSup_isCompact_of_ne_top hfin, ENNReal.mul_iSup]
  refine iSup_le fun K => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hKs => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hK => ?_
  have hKN : K ⊆ (N : Set (ComplexModel n)) := hKs.trans inter_subset_right
  have := hcpt K hK hKN
  rw [hν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hK.measurableSet,
    inter_eq_left.mpr hKN] at this
  exact this.trans (measure_mono hKs)

end SGPT.NPP.LogConcavityDinew
