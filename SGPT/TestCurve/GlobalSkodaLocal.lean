import SGPT.Okounkov.TranscendentalSkodaTheorem

/-!
# Skoda's `L²` division on a convex domain with a smooth plurisubharmonic weight

Blueprint `claude-global-skoda.tex`, node `global-skoda:local`.

The global Skoda division theorem (`GlobalSkodaDivision`) is proved by gluing *quantitative*
local Skoda divisions on coordinate balls. On a ball, a section of `L^{d+k}` in the frame `e`
is a holomorphic function `f`, the sections `wⱼ` of `L^d` are holomorphic functions `Gⱼ`, and
the weights read `|f|² |G|^{-2(M+1)} e^{-ψ}` and `|H|² |G|^{-2M} e^{-ψ}` with
`ψ = (k - Md) (-log |e|²_h)` smooth and plurisubharmonic. The constant of the division must not
depend on `ψ` (hence not on `k`, `M`).

This file proves that version of Skoda's theorem (Demailly, *Analytic methods in algebraic
geometry*, Theorem 12.8, on a bounded convex domain, trivial bundles, with a smooth psh weight):
for `p > n`, `f` holomorphic on `D` with `∫_D |f|² e^{-(p+1) log |G|² - ψ} < ∞`, there are
holomorphic `Hᵢ` near a compact `K ⊆ D` with `f = ∑ Gᵢ Hᵢ` and
`∫_U |H|² e^{-p log |G|² - ψ} ≤ (R + 1) (2 + 2n/(p - n)) ∫_D |f|² e^{-(p+1) log |G|² - ψ}`.

## Route

* `weightedSurjectiveSkoda`: the tuple has no common zeros. The proof of the project's
  `surjectiveSkodaStatement_of_twisted` (kernel-bundle Hörmander estimate
  `twistedHormanderStatement` with the weight `p log |G|²`) goes through with the weight
  `p log |G|² + ψ`: the Levi form of `ψ` is nonnegative, so it only helps the curvature
  hypothesis, and the factor `e^{-ψ}` is carried along.
* `weightedLocalSkoda_pos`: arbitrary tuples, by the regularization `(G, √δ)` and Montel/Fatou
  as in `skodaDivisionStatement_of_surjective`, keeping the bound.
* `weightedLocalSkoda_zero`: dimension `0` (a point), by the explicit quotient `f Ḡ / |G|²`.
* **`weightedLocalSkoda`**: all dimensions.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open Filter MeasureTheory Set Metric SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Okounkov.TranscendentalSkoda
open scoped Topology ComplexConjugate ContDiff ENNReal

/-! ### Weighted Skoda division for tuples without common zeros -/

theorem contDiffAt_two_of_contDiffOn {n : ℕ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u D) {z : ComplexModel n} (hz : z ∈ D) :
    ContDiffAt ℝ 2 u z :=
  (hu.contDiffAt (hD.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- Adding a smooth function with nonnegative Levi form increases `vectorLevi`. -/
theorem vectorLevi_le_add {n R : ℕ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ ψ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D) (hψ : ContDiffOn ℝ ∞ ψ D)
    (hψL : ∀ z ∈ D, ∀ v, 0 ≤ leviForm ψ z v) {z : ComplexModel n} (hz : z ∈ D)
    (α : Fin R → Fin n → ℂ) :
    vectorLevi Φ z α ≤ vectorLevi (fun y => Φ y + ψ y) z α := by
  have h : vectorLevi (fun y => Φ y + ψ y) z α = vectorLevi Φ z α + vectorLevi ψ z α := by
    simp only [vectorLevi, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact leviForm_add (contDiffAt_two_of_contDiffOn hD hΦ hz)
      (contDiffAt_two_of_contDiffOn hD hψ hz) _
  rw [h]
  have h0 : 0 ≤ vectorLevi ψ z α := Finset.sum_nonneg fun i _ => hψL z hz _
  linarith

/-- **Skoda's `L²` division with a smooth plurisubharmonic weight, surjective case.** For a
bounded convex `D ⊆ ℂⁿ` (`n > 0`), `K ⊆ D` compact and `p > n` there is an open `U ⊇ K` such
that for every tuple `G` without common zeros on `D`, every smooth `ψ` with nonnegative Levi form
and every holomorphic `f` with `I = ∫_D |f|² |G|^{-2(p+1)} e^{-ψ} < ∞`, there are holomorphic
`H` on `U` with `f = ∑ Gᵢ Hᵢ` and `∫_U |H|² |G|^{-2p} e^{-ψ} ≤ (2 + 2n/(p - n)) I`. -/
theorem weightedSurjectiveSkoda {n : ℕ} (hn : 0 < n) {D : Set (ComplexModel n)}
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    (∀ z ∈ D, 0 < generatorNormSq G z) →
    ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D → (∀ z ∈ D, ∀ v, 0 ≤ leviForm ψ z v) →
    ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
      Real.exp (-ψ z))) ≠ ⊤ →
    ∃ H : Fin R → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
          Real.exp (-ψ z)) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) *
          ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
            Real.exp (-ψ z)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := (p - n) / (2 * n) with htdef
  have ht : 0 < t := div_pos (by linarith) (by positivity)
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'D, hUo, hKU, hUD', hlam₁, hlam₂, hlam, hlamU, hmain⟩ :=
    twistedHormanderStatement n D hDo hDc hDb K hK hKD t ht
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  refine ⟨U, hUo, hKU, hUD'.trans hD'sub, ?_⟩
  intro R G hG hpos ψ hψ hψL f hf hI
  set I : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
    Real.exp (-ψ z)) with hIdef
  set Φ₀ : ComplexModel n → ℝ := fun y => p * Real.log (generatorNormSq G y) with hΦ₀def
  set Φ : ComplexModel n → ℝ := fun y => Φ₀ y + ψ y with hΦdef
  have hΦ₀ : ContDiffOn ℝ ∞ Φ₀ D := contDiffOn_skodaWeight hDo hG hpos p
  have hΦ : ContDiffOn ℝ ∞ Φ D := hΦ₀.add hψ
  have hclc : IsCompact (closure D') :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hDb.subset hD'D)
  have hD'b : Bornology.IsBounded D' := hDb.subset hD'sub
  -- curvature hypothesis
  have hcurv : ∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      (1 + t) * secondFundamental G z α ≤ vectorLevi Φ z α := by
    intro z hz α hα
    have h := skodaWeight_curvature hDo hn hG hpos hp hz hα
    have hB0 : 0 ≤ secondFundamental G z α :=
      div_nonneg (sq_nonneg _) (generatorNormSq_nonneg G z)
    have hle := vectorLevi_le_add hDo hΦ₀ hψ hψL hz α
    nlinarith [mul_nonneg ht.le hB0]
  -- the form `v`
  have hvcont : ∀ i j, ContinuousOn (skodaForm G f i j) D := fun i j =>
    (contDiffOn_dbarDir hDo (contDiffOn_skodaLift hDo hG hpos hf i) _).continuousOn
  have hvbd : ∀ i j, ∃ C, ∀ x ∈ D', ‖skodaForm G f i j x‖ ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ := hclc.exists_bound_of_continuousOn ((hvcont i j).mono hD'D)
    exact ⟨C, fun x hx => hC x (subset_closure hx)⟩
  obtain ⟨B, hB⟩ := hclc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hD'D)
  have hw₂ : ContinuousOn (fun x => Φ x + lam₂ x) D' := (hΦ.continuousOn.mono hD'sub).add hlam₂
  have hw₁ : ContinuousOn (fun x => Φ x + lam₁ x) D' := (hΦ.continuousOn.mono hD'sub).add hlam₁
  have hv : ∀ i j, MemLp (skodaForm G f i j) 2 (weightedVolume D' fun x => Φ x + lam₂ x) := by
    intro i j
    obtain ⟨C, hC⟩ := hvbd i j
    refine memLp_weightedVolume_of_bounded hD'o hD'b hw₂ (B := B) (fun x hx => ?_)
      (((hvcont i j).mono hD'sub).aestronglyMeasurable hD'o.measurableSet) hC
    have h1 := hB x (subset_closure hx)
    rw [Real.norm_eq_abs] at h1
    linarith [(abs_le.mp h1).1, (hlam x hx).1, (hlam x hx).2]
  have hvker : ∀ z ∈ D', InKernel G z fun i j => skodaForm G f i j z :=
    fun z hz j => sum_mul_skodaForm hDo hG hpos hf (hD'sub hz) j
  have hvcl : ∀ i, WeakDbarClosed D' (skodaForm G f i) :=
    fun i => weakDbarClosed_skodaForm hDo hD'sub hG hpos hf i
  -- the function `g`
  set g : ComplexModel n → ℝ := fun z => ‖f z‖ ^ 2 / (t * generatorNormSq G z) with hgdef
  have hg0 : ∀ x ∈ D', 0 ≤ g x := fun x _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg ht.le (generatorNormSq_nonneg G x))
  have hgb : ∀ z ∈ D', ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      ‖∑ i, ∑ j, conj (α i j) * skodaForm G f i j z‖ ^ 2 ≤
        g z * (vectorLevi Φ z α - (1 + t) * secondFundamental G z α) := by
    intro z hz α hα
    refine (skodaForm_twisted_bound hDo hn hG hpos hf hp (hD'sub hz) hα).trans ?_
    have hle := vectorLevi_le_add hDo hΦ₀ hψ hψL (hD'sub hz) α
    exact mul_le_mul_of_nonneg_left (by linarith) (hg0 z hz)
  have hgle : ∀ x ∈ D', g x * Real.exp (-(Φ x + lam₁ x)) ≤
      ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) * Real.exp (-ψ x) / t := by
    intro x hx
    have hS := hpos x (hD'sub hx)
    have e1 : g x * Real.exp (-(Φ x + lam₁ x)) =
        (g x * Real.exp (-Φ₀ x)) * Real.exp (-ψ x) * Real.exp (-lam₁ x) := by
      rw [show -(Φ x + lam₁ x) = -Φ₀ x + -ψ x + -lam₁ x by simp only [hΦdef]; ring,
        Real.exp_add, Real.exp_add]
      ring
    have e2 : g x * Real.exp (-Φ₀ x) = ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t :=
      skoda_g_mul_exp hS
    rw [e1, e2]
    have hl : Real.exp (-lam₁ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [(hlam x hx).1])
    have h0 : 0 ≤ ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t * Real.exp (-ψ x) :=
      mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS.le _)) ht.le)
        (Real.exp_pos _).le
    calc ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t * Real.exp (-ψ x) * Real.exp (-lam₁ x)
        ≤ ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t * Real.exp (-ψ x) * 1 :=
          mul_le_mul_of_nonneg_left hl h0
      _ = _ := by ring
  have hIt : ∫⁻ x in D', ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) *
      Real.exp (-ψ x) / t) ≤ ENNReal.ofReal t⁻¹ * I := by
    calc ∫⁻ x in D', ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) *
          Real.exp (-ψ x) / t)
        = ∫⁻ x in D', ENNReal.ofReal t⁻¹ *
            ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) * Real.exp (-ψ x)) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), div_eq_inv_mul]
      _ = ENNReal.ofReal t⁻¹ * ∫⁻ x in D', ENNReal.ofReal
            (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) * Real.exp (-ψ x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t⁻¹ * I := by gcongr; exact lintegral_mono_set hD'sub
  have hgmeas : AEStronglyMeasurable (fun x => g x * Real.exp (-(Φ x + lam₁ x)))
      (volume.restrict D') := by
    have hgc : ContinuousOn g D' := by
      refine ContinuousOn.div ((hf.continuousOn.mono hD'sub).norm.pow 2)
        (continuousOn_const.mul ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono hD'sub))
        fun x hx => (mul_pos ht (hpos x (hD'sub hx))).ne'
    exact (hgc.mul (Real.continuous_exp.comp_continuousOn hw₁.neg)).aestronglyMeasurable
      hD'o.measurableSet
  have hgint : Integrable (fun x => g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') := by
    refine ⟨hgmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · refine lt_of_le_of_lt (setLIntegral_mono' hD'o.measurableSet fun x hx =>
        ENNReal.ofReal_le_ofReal (hgle x hx)) (lt_of_le_of_lt hIt ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hI)
    · filter_upwards [ae_restrict_mem hD'o.measurableSet] with x hx
      exact mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  obtain ⟨u, hu2, huker, hueq, hubd⟩ :=
    hmain R G hG hpos Φ hΦ hcurv (skodaForm G f) hv hvker hvcl g hg0 hgb hgint
  -- holomorphy of `H = h⁰ - u` (Weyl's lemma)
  have hLcont : ∀ i, ContinuousOn (skodaLift G f i) D := fun i =>
    (contDiffOn_skodaLift hDo hG hpos hf i).continuousOn
  have hHex : ∀ i, ∃ H : ComplexModel n → ℂ, DifferentiableOn ℂ H D' ∧
      ∀ᵐ x ∂(volume.restrict D'), skodaLift G f i x - u i x = H x := by
    intro i
    have hu₀loc : LocallyIntegrableOn (u i) D' :=
      SGPT.Foundations.Analysis.Pending.OTChen.locallyIntegrableOn_of_memLp_weightedVolume hD'o hw₁
        (hu2 i)
    have haloc : LocallyIntegrableOn (skodaLift G f i) D' :=
      ((hLcont i).mono hD'sub).locallyIntegrableOn hD'o.measurableSet
    have hFloc : LocallyIntegrableOn (fun z => skodaLift G f i z - u i z) D' := haloc.sub hu₀loc
    have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
        ∫ x, (skodaLift G f i x - u i x) * dbarDir (coordVec j) h x = 0 := by
      intro h hh j
      have hdc : Continuous (dbarDir (coordVec j) h) :=
        SGPT.Foundations.Analysis.Pending.OTChen.continuous_dbarDir'
          (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
      have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
      have hdts :=
        (SGPT.Foundations.Analysis.Pending.OTChen.tsupport_dbarDir_subset (coordVec j) h).trans
          hh.2.2
      have i1 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn
        haloc hdc hdcs hdts
      have i2 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn
        hu₀loc hdc hdcs hdts
      simp only [sub_mul]
      rw [integral_sub i1 i2, weakDbarEq_skodaLift hDo hD'sub hG hpos hf i h hh j, hueq i h hh j]
      ring
    exact SGPT.Foundations.Analysis.Pending.exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
      (SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  choose H hHhol hHae using hHex
  have hHae' : ∀ᵐ x ∂(volume.restrict D'), ∀ i, skodaLift G f i x - u i x = H i x :=
    ae_all_iff.mpr hHae
  -- `f = ∑ Gᵢ Hᵢ` on `D'`
  have hid : EqOn f (fun z => ∑ i, G i z * H i z) D' := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hD'o (hf.continuousOn.mono hD'sub) ?_
    · filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with x hx hxk hxD
      simp_rw [← hx, mul_sub, Finset.sum_sub_distrib, hxk, sub_zero]
      exact (sum_mul_skodaLift hpos f (hD'sub hxD)).symm
    · exact continuousOn_finsetSum _ fun i _ =>
        ((hG i).continuousOn.mono hD'sub).mul (hHhol i).continuousOn
  -- the pointwise Pythagoras identity
  have hpyth : ∀ᵐ x ∂(volume.restrict D'), ∑ i, ‖H i x‖ ^ 2 =
      ‖f x‖ ^ 2 / generatorNormSq G x + ∑ i, ‖u i x‖ ^ 2 := by
    filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with x hx hxk hxD
    have hS := hpos x (hD'sub hxD)
    simp_rw [← hx]
    exact skoda_pythagoras hS hxk
  -- the estimate
  refine ⟨H, fun i => (hHhol i).mono hUD', fun z hz => hid (hUD' hz), ?_⟩
  have hexpΦ : ∀ z ∈ D, Real.exp (-Φ z) = generatorNormSq G z ^ (-p) * Real.exp (-ψ z) := by
    intro z hz
    rw [Real.rpow_def_of_pos (hpos z hz), ← Real.exp_add]
    congr 1
    simp only [hΦdef, hΦ₀def]
    ring
  have hu_int : Integrable (fun x => (∑ i, ‖u i x‖ ^ 2) * Real.exp (-(Φ x + lam₁ x)))
      (volume.restrict D') := by
    have h := integrable_finsetSum Finset.univ fun i _ =>
      integrable_sq_mul_exp_of_memLp hD'o hw₁ (hu2 i)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Finset.sum_mul]
  have hgI : ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x)) ≤ t⁻¹ * I.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem hD'o.measurableSet] with x hx
      exact mul_nonneg (hg0 x hx) (Real.exp_pos _).le) hgmeas]
    have h1 : ∫⁻ x in D', ENNReal.ofReal (g x * Real.exp (-(Φ x + lam₁ x))) ≤
        ENNReal.ofReal t⁻¹ * I :=
      (setLIntegral_mono' hD'o.measurableSet fun x hx =>
        ENNReal.ofReal_le_ofReal (hgle x hx)).trans hIt
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)] at h2
  have hupart : ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
      Real.exp (-ψ z)) ≤ ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
    calc ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
          Real.exp (-ψ z))
        = ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) := by
          refine setLIntegral_congr_fun hUo.measurableSet fun z hz => ?_
          rw [(hlamU z hz).1, add_zero, hexpΦ z (hD'sub (hUD' hz)), mul_assoc]
      _ ≤ ∫⁻ z in D', ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
          lintegral_mono_set hUD'
      _ = ENNReal.ofReal (∫ z in D', (∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
          (ofReal_integral_eq_lintegral_ofReal hu_int (Filter.Eventually.of_forall fun x =>
            mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)).symm
      _ ≤ ENNReal.ofReal ((1 + t) * (t⁻¹ * I.toReal)) :=
          ENNReal.ofReal_le_ofReal (hubd.trans (mul_le_mul_of_nonneg_left hgI (by linarith)))
      _ = ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hI]
  have hfmeas : AEMeasurable (fun z => ENNReal.ofReal (‖f z‖ ^ 2 *
      generatorNormSq G z ^ (-(p + 1)) * Real.exp (-ψ z))) (volume.restrict U) := by
    have hc : ContinuousOn (fun z => ‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
        Real.exp (-ψ z)) U := by
      refine (((hf.continuousOn.mono (hUD'.trans hD'sub)).norm.pow 2).mul ?_).mul
        (Real.continuous_exp.comp_continuousOn (hψ.continuousOn.mono (hUD'.trans hD'sub)).neg)
      exact ContinuousOn.rpow_const ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono
        (hUD'.trans hD'sub)) fun z hz => Or.inl (hpos z (hD'sub (hUD' hz))).ne'
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hUo.measurableSet
  have hpythU := ae_restrict_of_ae_restrict_of_subset hUD' hpyth
  calc ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
        Real.exp (-ψ z))
      = ∫⁻ z in U, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
          Real.exp (-ψ z) + (∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
            Real.exp (-ψ z)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hpythU, ae_restrict_mem hUo.measurableSet] with z hz hzU
        have hS := hpos z (hD'sub (hUD' hzU))
        rw [hz]
        congr 1
        rw [Real.rpow_neg hS.le, Real.rpow_neg hS.le, Real.rpow_add hS, Real.rpow_one]
        field_simp
    _ ≤ ∫⁻ z in U, (ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
          Real.exp (-ψ z)) + ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p) *
            Real.exp (-ψ z))) :=
        lintegral_mono fun z => ENNReal.ofReal_add_le
    _ = (∫⁻ z in U, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) *
          Real.exp (-ψ z))) + ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) *
            generatorNormSq G z ^ (-p) * Real.exp (-ψ z)) :=
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

/-! ### Common zeros: the regularization `(G, √δ)` -/

/-- **Skoda's `L²` division with a smooth plurisubharmonic weight**, dimension `n > 0`, tuples
with common zeros allowed: the regularized tuples `(G, √δ)` have no common zeros, and a
subsequential limit (Montel, Fatou) of their quotients divides `f`, with the same bound
for each component. -/
theorem weightedLocalSkoda_pos {n : ℕ} (hn : 0 < n) {D : Set (ComplexModel n)}
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D → (∀ z ∈ D, ∀ v, 0 ≤ leviForm ψ z v) →
    ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
      ENNReal.ofReal (Real.exp (-ψ z))) ≠ ⊤ →
    ∃ H : Fin R → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * multiplierWeight p (generatorLog G z) *
          ENNReal.ofReal (Real.exp (-ψ z)) ≤
        ENNReal.ofReal ((R + 1) * (2 + 2 * n / (p - n))) *
          ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
            ENNReal.ofReal (Real.exp (-ψ z)) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  obtain ⟨U, hUo, hKU, hUD, hU⟩ := weightedSurjectiveSkoda hn hDo hDc hDb hK hKD hp
  refine ⟨U, hUo, hKU, hUD, ?_⟩
  intro R g hg ψ hψ hψL f hf hI
  set A₀ : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) *
    multiplierWeight (p + 1) (generatorLog g z) * ENNReal.ofReal (Real.exp (-ψ z)) with hA₀def
  set S := generatorNormSq g with hS
  have hS0 : ∀ z, 0 ≤ S z := fun z => generatorNormSq_nonneg g z
  have hScont : ContinuousOn S D := by
    rw [hS]
    have : generatorNormSq g = fun y => ∑ j, ‖g j y‖ ^ 2 := rfl
    rw [this]
    exact continuousOn_finsetSum _ fun j _ => ((hg j).continuousOn.norm).pow 2
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hIδ : ∀ k, (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 *
      generatorNormSq (regTuple g (δ k)) z ^ (-(p + 1)) * Real.exp (-ψ z))) ≤ A₀ := by
    intro k
    refine lintegral_mono fun z => ?_
    rw [generatorNormSq_regTuple g (hδpos k).le]
    have hb : 0 ≤ (S z + δ k) ^ (-(p + 1)) := Real.rpow_nonneg (by linarith [hS0 z, hδpos k]) _
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hb), ENNReal.ofReal_mul (sq_nonneg _)]
    gcongr
    exact ofReal_rpow_le_multiplierWeight g (by linarith) (hδpos k) z
  have hex : ∀ k, ∃ H : Fin (R + 1) → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, regTuple g (δ k) i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) *
        generatorNormSq (regTuple g (δ k)) z ^ (-p) * Real.exp (-ψ z)) ≤
        ENNReal.ofReal (2 + 2 * n / (p - n)) * A₀ := by
    intro k
    have hpos : ∀ z ∈ D, 0 < generatorNormSq (regTuple g (δ k)) z := fun z _ => by
      rw [generatorNormSq_regTuple g (hδpos k).le]
      exact add_pos_of_nonneg_of_pos (generatorNormSq_nonneg g z) (hδpos k)
    obtain ⟨H, hH, hHeq, hHb⟩ := hU (R + 1) (regTuple g (δ k))
      (differentiableOn_regTuple hg _) hpos ψ hψ hψL f hf (ne_top_of_le_ne_top hI (hIδ k))
    exact ⟨H, hH, hHeq, hHb.trans (by gcongr; exact hIδ k)⟩
  choose H hHhol hHeq hHbd using hex
  set C : ℝ≥0∞ := ENNReal.ofReal (2 + 2 * n / (p - n)) * A₀ with hC
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI
  set w : ℕ → ComplexModel n → ℝ≥0∞ := fun k z =>
    ENNReal.ofReal ((S z + δ k) ^ (-p) * Real.exp (-ψ z)) with hw
  have hwmono : ∀ z, Monotone fun k => w k z := by
    intro z k l hkl
    apply ENNReal.ofReal_le_ofReal
    have hδ : δ l ≤ δ k := by
      simp only [hδdef]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (hS0 z) (hδpos l))
      (by linarith) (by linarith)
  have hwcont : ∀ k, ContinuousOn (fun z => (S z + δ k) ^ (-p) * Real.exp (-ψ z)) D := by
    intro k
    refine (ContinuousOn.rpow_const (hScont.add continuousOn_const) fun z _ => Or.inl ?_).mul
      (Real.continuous_exp.comp_continuousOn hψ.continuousOn.neg)
    exact (add_pos_of_nonneg_of_pos (hS0 z) (hδpos k)).ne'
  have hwmeas : ∀ k, AEMeasurable (w k) (volume.restrict (⋃ _k : ℕ, U)) := by
    intro k
    rw [iUnion_const]
    exact (ENNReal.continuous_ofReal.comp_continuousOn ((hwcont k).mono hUD)).aemeasurable
      hUo.measurableSet
  have hlow : ∀ z ∈ ⋃ _k : ℕ, U, ∃ r > 0, ∃ δ' : ℝ, 0 < δ' ∧
      ∀ y ∈ ball z r, ENNReal.ofReal δ' ≤ w 0 y := by
    intro z hz
    rw [iUnion_const] at hz
    obtain ⟨r₀, hr₀, hr₀D⟩ := Metric.isOpen_iff.mp hDo z (hUD hz)
    have hcb : closedBall z (r₀ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hr₀D
    obtain ⟨B₁, hB₁⟩ :=
      (isCompact_closedBall z (r₀ / 2)).exists_bound_of_continuousOn (hScont.mono hcb)
    obtain ⟨B₂, hB₂⟩ :=
      (isCompact_closedBall z (r₀ / 2)).exists_bound_of_continuousOn (hψ.continuousOn.mono hcb)
    refine ⟨r₀ / 2, by positivity, (|B₁| + 1) ^ (-p) * Real.exp (-|B₂|), by positivity,
      fun y hy => ?_⟩
    apply ENNReal.ofReal_le_ofReal
    have hyc := ball_subset_closedBall hy
    have h1 := hB₁ y hyc
    have h2 := hB₂ y hyc
    rw [Real.norm_eq_abs] at h1 h2
    have hSy : S y ≤ |B₁| := (le_abs_self _).trans (h1.trans (le_abs_self _))
    have hψy : ψ y ≤ |B₂| := (le_abs_self _).trans (h2.trans (le_abs_self _))
    simp only [hδdef, Nat.cast_zero, zero_add, div_one]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (by linarith [hS0 y]) (by linarith)
      (by linarith)) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (Real.rpow_nonneg (by linarith [hS0 y]) _)
  have hbound : ∀ i k, ∫⁻ z in U, ENNReal.ofReal (‖H k i z‖ ^ 2) * w k z ≤ C := by
    intro i k
    refine le_trans (lintegral_mono fun z => ?_) (hHbd k)
    have hsum : ‖H k i z‖ ^ 2 ≤ ∑ j, ‖H k j z‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖H k j z‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hw0 : 0 ≤ (S z + δ k) ^ (-p) * Real.exp (-ψ z) :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hS0 z, hδpos k]) _) (Real.exp_pos _).le
    calc ENNReal.ofReal (‖H k i z‖ ^ 2) * w k z
        = ENNReal.ofReal (‖H k i z‖ ^ 2 * ((S z + δ k) ^ (-p) * Real.exp (-ψ z))) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ ENNReal.ofReal ((∑ j, ‖H k j z‖ ^ 2) * generatorNormSq (regTuple g (δ k)) z ^ (-p) *
            Real.exp (-ψ z)) := by
          rw [generatorNormSq_regTuple g (hδpos k).le, mul_assoc]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsum hw0)
  -- a common convergent subsequence for the first `R` components
  set P : Fin R → (ℕ → ℕ) → Prop := fun i φ => ∃ h : ComplexModel n → ℂ,
    DifferentiableOn ℂ h U ∧ TendstoLocallyUniformlyOn (fun k => H (φ k) i.castSucc) h atTop U ∧
    ∫⁻ z in U, ENNReal.ofReal (‖h z‖ ^ 2) * ⨆ k, w k z ≤ C with hPdef
  have hPsub : ∀ i (φ ψ : ℕ → ℕ), P i φ → StrictMono ψ → P i (φ ∘ ψ) := by
    rintro i φ ψ ⟨h, hh, hconv, hb⟩ hψ
    exact ⟨h, hh, tendstoLocallyUniformlyOn_comp_strictMono hconv hψ, hb⟩
  have hPex : ∀ i (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (φ ∘ ψ) := by
    intro i φ hφ
    have hwm' : ∀ z ∈ ⋃ _k : ℕ, U, Monotone fun k => w (φ k) z :=
      fun z _ _ _ hab => hwmono z (hφ.monotone hab)
    have hlow' : ∀ z ∈ ⋃ _k : ℕ, U, ∃ r > 0, ∃ δ' : ℝ, 0 < δ' ∧
        ∀ y ∈ ball z r, ENNReal.ofReal δ' ≤ w (φ 0) y := by
      intro z hz
      obtain ⟨r₀, hr₀, δ', hδ', hl⟩ := hlow z hz
      exact ⟨r₀, hr₀, δ', hδ', fun y hy => (hl y hy).trans (hwmono y (Nat.zero_le _))⟩
    obtain ⟨ψ, G₀, hψ, hG₀, hconv, -, hb⟩ :=
      SGPT.Foundations.Analysis.Pending.exists_subseq_differentiableOn_extension_of_weighted_bounds
        (α := Empty) (ι := Empty.elim) (g := Empty.elim) (U := fun _ => U) (fun _ => hUo)
        (fun _ _ _ => le_rfl) (w := fun k => w (φ k)) hwm' (fun k => hwmeas (φ k)) hlow'
        (F := fun k => H (φ k) i.castSucc) (fun k => hHhol (φ k) i.castSucc)
        (fun _ a => a.elim) hCtop (fun k => hbound i.castSucc (φ k))
    rw [iUnion_const] at hG₀ hconv hb
    refine ⟨ψ, hψ, G₀, hG₀, hconv, le_trans (lintegral_mono fun z => ?_) hb⟩
    gcongr
    exact hwmono z (hφ.id_le _)
  obtain ⟨φ, hφ, hPφ⟩ := exists_strictMono_forall_of_fintype P hPsub hPex
  choose h hhol hconv hhb using hPφ
  -- the limit identity
  have hlimit : ∀ z ∈ U, f z = ∑ i, g i z * h i z := by
    intro z hz
    have hk : ∀ k, f z = ∑ i : Fin R, g i z * H (φ k) i.castSucc z +
        ((Real.sqrt (δ (φ k)) : ℝ) : ℂ) * H (φ k) (Fin.last R) z := fun k => by
      rw [hHeq (φ k) z hz, sum_regTuple_mul]
    have h1 : Tendsto (fun k => ∑ i : Fin R, g i z * H (φ k) i.castSucc z) atTop
        (𝓝 (∑ i, g i z * h i z)) :=
      tendsto_finsetSum _ fun i _ => ((hconv i).tendsto_at hz).const_mul (g i z)
    obtain ⟨r₀, hr₀, δ', hδ', hl⟩ := hlow z (by rw [iUnion_const]; exact hz)
    obtain ⟨r₁, hr₁, M', hM'⟩ :=
      SGPT.Foundations.Analysis.Pending.exists_eventually_norm_le_of_weighted_bounds
        (U := fun _ => U) (fun _ => hUo) (fun _ _ _ => le_rfl) (w := w)
        (fun y _ => hwmono y) (F := fun k => H k (Fin.last R)) (fun k => hHhol k (Fin.last R))
        hCtop (fun k => hbound (Fin.last R) k) (by rw [iUnion_const]; exact hz) hr₀ hδ' hl
    have hbdd : IsBoundedUnder (· ≤ ·) atTop
        ((fun w => ‖w‖) ∘ fun k => H (φ k) (Fin.last R) z) := by
      refine ⟨M', ?_⟩
      have := hφ.tendsto_atTop.eventually hM'
      simp only [eventually_map]
      filter_upwards [this] with k hk
      exact hk.2 z (mem_ball_self hr₁)
    have hsq : Tendsto (fun k => ((Real.sqrt (δ (φ k)) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((Real.continuous_sqrt.tendsto 0).comp (hδ0.comp hφ.tendsto_atTop))
      rw [Real.sqrt_zero] at this
      have h' := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h'
      exact h'
    have h2 := hsq.zero_mul_isBoundedUnder_le hbdd
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact tendsto_nhds_unique (tendsto_const_nhds.congr hk) h3
  -- the estimate
  refine ⟨h, hhol, hlimit, ?_⟩
  have hsup : ∀ z, multiplierWeight p (generatorLog g z) * ENNReal.ofReal (Real.exp (-ψ z)) ≤
      ⨆ k, w k z := by
    intro z
    calc multiplierWeight p (generatorLog g z) * ENNReal.ofReal (Real.exp (-ψ z))
        ≤ (⨆ k : ℕ, ENNReal.ofReal ((generatorNormSq g z + 1 / ((k : ℝ) + 1)) ^ (-p))) *
            ENNReal.ofReal (Real.exp (-ψ z)) := by
          gcongr
          exact multiplierWeight_le_iSup g hp0 z
      _ = ⨆ k : ℕ, ENNReal.ofReal ((generatorNormSq g z + 1 / ((k : ℝ) + 1)) ^ (-p)) *
            ENNReal.ofReal (Real.exp (-ψ z)) := ENNReal.iSup_mul _ _
      _ = ⨆ k, w k z := by
          refine iSup_congr fun k => ?_
          simp only [hw, hδdef]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by
            linarith [generatorNormSq_nonneg g z, hδpos k]) _)]
  have hhm : ∀ i, AEMeasurable (fun z => ENNReal.ofReal (‖h i z‖ ^ 2) * ⨆ k, w k z)
      (volume.restrict U) := by
    intro i
    have hw' : ∀ k, AEMeasurable (w k) (volume.restrict U) := fun k => by
      simpa only [iUnion_const] using hwmeas k
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hhol i).continuousOn.aestronglyMeasurable hUo.measurableSet).norm.aemeasurable.pow_const
        2)).mul (AEMeasurable.iSup hw')
  have hc0 : (0 : ℝ) ≤ 2 + 2 * n / (p - n) := by
    have : (0 : ℝ) ≤ 2 * n / (p - n) := div_nonneg (by positivity) (by linarith)
    linarith
  calc ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖h i z‖ ^ 2) * multiplierWeight p (generatorLog g z) *
        ENNReal.ofReal (Real.exp (-ψ z))
      ≤ ∫⁻ z in U, ∑ i, ENNReal.ofReal (‖h i z‖ ^ 2) * ⨆ k, w k z := by
        refine lintegral_mono fun z => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), mul_assoc, Finset.sum_mul]
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsup z) zero_le
    _ = ∑ i, ∫⁻ z in U, ENNReal.ofReal (‖h i z‖ ^ 2) * ⨆ k, w k z :=
        lintegral_finsetSum' _ fun i _ => hhm i
    _ ≤ ∑ _i : Fin R, C := Finset.sum_le_sum fun i _ => hhb i
    _ = (R : ℝ≥0∞) * (ENNReal.ofReal (2 + 2 * n / (p - n)) * A₀) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((R + 1) * (2 + 2 * n / (p - n))) * A₀ := by
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (by linarith) hc0)) zero_le

/-! ### Dimension zero -/

/-- **Skoda's division in dimension `0`**: `ℂ⁰` is a point and the quotient `f Ḡ / |G|²` works
(at a common zero, finiteness of the weighted integral forces `f = 0`). -/
theorem weightedLocalSkoda_zero {n : ℕ} (hn : n = 0) {D : Set (ComplexModel n)}
    (hDo : IsOpen D) {K : Set (ComplexModel n)} (hKD : K ⊆ D) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D → (∀ z ∈ D, ∀ v, 0 ≤ leviForm ψ z v) →
    ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
      ENNReal.ofReal (Real.exp (-ψ z))) ≠ ⊤ →
    ∃ H : Fin R → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * multiplierWeight p (generatorLog G z) *
          ENNReal.ofReal (Real.exp (-ψ z)) ≤
        ENNReal.ofReal ((R + 1) * (2 + 2 * n / (p - n))) *
          ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
            ENNReal.ofReal (Real.exp (-ψ z)) := by
  subst hn
  have hp0 : (0 : ℝ) < p := by simpa using hp
  refine ⟨D, hDo, hKD, subset_rfl, ?_⟩
  intro R G _ ψ _ _ f _ hI
  have hconst : ∀ (F : ComplexModel 0 → ℂ) (y z : ComplexModel 0), F y = F z := fun F y z => by
    rw [Subsingleton.elim y z]
  have hdiff : ∀ F : ComplexModel 0 → ℂ, DifferentiableOn ℂ F D := by
    intro F z _
    have : F = fun _ => F z := funext fun y => hconst F y z
    rw [this]
    exact differentiableWithinAt_const _
  -- the integrand at a point of `D`
  set Fw : ComplexModel 0 → ℝ≥0∞ := fun z => ENNReal.ofReal (‖f z‖ ^ 2) *
    multiplierWeight (p + 1) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z)) with hFw
  have hvol : ∀ z ∈ D, volume D ≠ 0 := fun z hz => (hDo.measure_pos volume ⟨z, hz⟩).ne'
  have hint : ∀ z ∈ D, ∫⁻ y in D, Fw y = Fw z * volume D := by
    intro z _
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hDo.measurableSet fun y _ => ?_
    simp only [hFw]
    rw [Subsingleton.elim y z]
  have hfz : ∀ z ∈ D, generatorNormSq G z = 0 → f z = 0 := by
    intro z hz hS
    by_contra hf0
    have hG : ∀ j, G j z = 0 := by
      intro j
      have h1 : ‖G j z‖ ^ 2 ≤ generatorNormSq G z :=
        Finset.single_le_sum (f := fun j => ‖G j z‖ ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j)
      rw [hS] at h1
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (G j z)])
    have hbot : generatorLog G z = ⊥ := (generatorLog_eq_bot_iff G z).mpr hG
    have htop : Fw z = ⊤ := by
      simp only [hFw, hbot, multiplierWeight_bot (by linarith : (0 : ℝ) < p + 1)]
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne', ENNReal.top_mul
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
    apply hI
    change ∫⁻ y in D, Fw y = ⊤
    rw [hint z hz, htop, ENNReal.top_mul (hvol z hz)]
  refine ⟨skodaLift G f, fun i => hdiff _, fun z hz => ?_, ?_⟩
  · by_cases hS : generatorNormSq G z = 0
    · have hf0 := hfz z hz hS
      have hlift : ∀ i, skodaLift G f i z = 0 := fun i => by simp [skodaLift, hf0]
      simp [hlift, hf0]
    · have hpos : 0 < generatorNormSq G z := lt_of_le_of_ne (generatorNormSq_nonneg G z) (Ne.symm hS)
      exact (sum_mul_skodaLift (D := {z}) (fun y hy => by rw [hy]; exact hpos) f rfl).symm
  -- the estimate, pointwise
  have hc1 : (1 : ℝ) ≤ (R + 1) * (2 + 2 * ((0 : ℕ) : ℝ) / (p - ((0 : ℕ) : ℝ))) := by
    simp only [Nat.cast_zero, mul_zero, zero_div, add_zero]
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith
  have hpt : ∀ z, ENNReal.ofReal (∑ i, ‖skodaLift G f i z‖ ^ 2) *
      multiplierWeight p (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z)) ≤ Fw z := by
    intro z
    by_cases hS : generatorNormSq G z = 0
    · have hlift : ∀ i, skodaLift G f i z = 0 := fun i => by simp [skodaLift, hS]
      simp [hlift]
    · have hpos : 0 < generatorNormSq G z := lt_of_le_of_ne (generatorNormSq_nonneg G z) (Ne.symm hS)
      have hne : ∃ j, G j z ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hS (by simp [generatorNormSq, hall])
      have hsum : ∑ i, ‖skodaLift G f i z‖ ^ 2 = ‖f z‖ ^ 2 / generatorNormSq G z := by
        have := skoda_pythagoras (f := f) (u := fun _ _ => 0) hpos (by simp)
        simpa using this
      simp only [hFw]
      rw [hsum, generatorLog_of_nonzero hne, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) hpos.le),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_right (le_of_eq (congrArg ENNReal.ofReal ?_)) zero_le
      rw [show -((p + 1) * Real.log (generatorNormSq G z)) =
          -(p * Real.log (generatorNormSq G z)) + -Real.log (generatorNormSq G z) by ring,
        Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hpos]
      field_simp
  calc ∫⁻ z in D, ENNReal.ofReal (∑ i, ‖skodaLift G f i z‖ ^ 2) *
        multiplierWeight p (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z))
      ≤ ∫⁻ z in D, ENNReal.ofReal ((R + 1) * (2 + 2 * ((0 : ℕ) : ℝ) / (p - ((0 : ℕ) : ℝ)))) *
          Fw z := by
        refine lintegral_mono fun z => (hpt z).trans ?_
        calc Fw z = 1 * Fw z := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc1) zero_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Skoda's `L²` division with a smooth plurisubharmonic weight** (all dimensions;
Demailly, *Analytic methods in algebraic geometry*, Theorem 12.8 on a bounded convex domain with
trivial bundles and the weight `ψ`): for `D ⊆ ℂⁿ` bounded convex, `K ⊆ D` compact and `p > n`
there is an open `U`, `K ⊆ U ⊆ D`, such that for every holomorphic tuple `G` on `D` (common
zeros allowed), every smooth `ψ` with nonnegative Levi form on `D` and every holomorphic `f` on
`D` with `I = ∫_D |f|² e^{-(p+1) log |G|²} e^{-ψ} < ∞`, there are `H` holomorphic on `U` with
`f = ∑ Gᵢ Hᵢ` on `U` and `∫_U |H|² e^{-p log |G|²} e^{-ψ} ≤ (R + 1)(2 + 2n/(p - n)) I`. -/
theorem weightedLocalSkoda {n : ℕ} {D : Set (ComplexModel n)}
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
    ∀ (R : ℕ) (G : Fin R → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (G i) D) →
    ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ψ D → (∀ z ∈ D, ∀ v, 0 ≤ leviForm ψ z v) →
    ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    (∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
      ENNReal.ofReal (Real.exp (-ψ z))) ≠ ⊤ →
    ∃ H : Fin R → ComplexModel n → ℂ, (∀ i, DifferentiableOn ℂ (H i) U) ∧
      (∀ z ∈ U, f z = ∑ i, G i z * H i z) ∧
      ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * multiplierWeight p (generatorLog G z) *
          ENNReal.ofReal (Real.exp (-ψ z)) ≤
        ENNReal.ofReal ((R + 1) * (2 + 2 * n / (p - n))) *
          ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (p + 1) (generatorLog G z) *
            ENNReal.ofReal (Real.exp (-ψ z)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact weightedLocalSkoda_zero hn hDo hKD hp
  · exact weightedLocalSkoda_pos hn hDo hDc hDb hK hKD hp

end SGPT.TestCurve.GlobalSkoda
