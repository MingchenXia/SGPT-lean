import SGPT.Envelopes.MADirichletMeasure
import SGPT.PSH.BookDeepDomination
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasingCollar

/-!
# Linear elliptic inequalities and Monge–Ampère lower bounds with constant density

Xia, *Foundations of pluripotential theory* (FPT), `prop:bounded-monge-ampere-linear-density`,
the equivalence (1) ⇔ (3) for constant densities, in a form local on balls. For a complex frame
`Y` with `|det Y| = 1` let `L_Y χ = ∑ₖ leviForm χ (Y eₖ)` (`frameLevi`). We say that `u`
satisfies the *frame inequalities* with constant `m ≥ 0` on the ball `B(x₀, r)`
(`FrameIneqOnBall u m x₀ r`) if `n m ∫ χ ≤ ∫ u L_Y χ` for all such frames and all nonnegative
`C²` functions `χ` with compact support in `B(x₀, r)`; this is `L_Y u ≥ n m` in the sense of
distributions on the ball.

* (1) ⇒ (3): `frameIneqOnBall_of_ma_ge` (S57's `integral_mul_frameLevi_ge`), with the degenerate
  case `m = 0` for every locally bounded psh function (`frameIneqOnBall_zero`).
* (3) ⇒ (1): `ma_ge_on_ball_of_frameIneq`: the radial mollifications of `u` have complex Hessian
  determinant at least `mⁿ` (`exists_decreasingApproximation_det_ge_of_frameIneq`), and the
  canonical Bedford–Taylor measure is their vague limit, so `(ddᶜu)ⁿ ≥ mⁿ (n!/πⁿ) dV`. The mixed
  version `mixed_ge_on_ball_of_det_ge` is S57's `mixedBedfordTaylor_ge_on_ball` with the
  determinant bounds as input.
* The frame inequalities are *linear*: they are stable under sums and nonnegative multiples
  (`FrameIneqOnBall.add`, `FrameIneqOnBall.smul`), and `|z|²` satisfies them with `m = 1`
  (`frameIneqOnBall_normSq`). This is what makes Monge–Ampère subsolutions stable under convex
  combinations (`MADirichletSubsolution`).

Normalization: `(ddᶜu)ⁿ ≥ c · ηⁿ` with `η = ddᶜ|z|²` reads
`ENNReal.ofReal (mongeAmpereConst n * c) • volume ≤ canonicalBedfordTaylorMeasure`, where
`mongeAmpereConst n = n!/πⁿ` (FPT `eq:bt-determinant-normalization`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix TopologicalSpace
open scoped Topology ENNReal ComplexOrder ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- **The frame inequalities on a ball** (FPT `prop:bounded-monge-ampere-linear-density`, (3),
tested on `B(x₀, r)`): `L_Y u ≥ n m` in the sense of distributions for every frame `Y` with
`|det Y| = 1`. -/
def FrameIneqOnBall (u : ComplexModel n → ℝ) (m : ℝ) (x₀ : ComplexModel n) (r : ℝ) : Prop :=
  ∀ Y : Matrix (Fin n) (Fin n) ℂ, ‖Y.det‖ = 1 → ∀ χ : ComplexModel n → ℝ, ContDiff ℝ 2 χ →
    HasCompactSupport χ → (∀ x, 0 ≤ χ x) → tsupport χ ⊆ Metric.ball x₀ r →
    n * m * ∫ x, χ x ≤ ∫ x, u x * frameLevi Y χ x

/-! ### Elementary properties -/

theorem continuous_frameLevi (Y : Matrix (Fin n) (Fin n) ℂ) {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ 2 χ) : Continuous (frameLevi Y χ) :=
  continuous_finsetSum _ fun _ _ => continuous_leviForm hχ _

theorem frameLevi_eq_zero_of_notMem (Y : Matrix (Fin n) (Fin n) ℂ) {χ : ComplexModel n → ℝ}
    {x : ComplexModel n} (hx : x ∉ tsupport χ) : frameLevi Y χ x = 0 := by
  simp [frameLevi, leviForm, realHessian_eq_zero_of_notMem_tsupport hx]

theorem tsupport_frameLevi_subset (Y : Matrix (Fin n) (Fin n) ℂ) (χ : ComplexModel n → ℝ) :
    tsupport (frameLevi Y χ) ⊆ tsupport χ :=
  closure_minimal (fun x hx => by
    by_contra h
    exact hx (frameLevi_eq_zero_of_notMem Y h)) (isClosed_tsupport χ)

theorem hasCompactSupport_frameLevi (Y : Matrix (Fin n) (Fin n) ℂ) {χ : ComplexModel n → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (frameLevi Y χ) :=
  hχc.mono' ((subset_tsupport _).trans (tsupport_frameLevi_subset Y χ))

/-- `u · L_Y χ` is integrable for a locally bounded psh `u` and a test `χ` supported in `Ω`. -/
theorem integrable_mul_frameLevi {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (Y : Matrix (Fin n) (Fin n) ℂ) {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n))) :
    Integrable (fun x => u x * frameLevi Y χ x) := by
  have h := BedfordTaylor.integrable_test_mul_of_isLocallyBoundedPshOn hu
    (ν := volume) (fun K hK _ => hK.measure_lt_top) (continuous_frameLevi Y hχ)
    (hasCompactSupport_frameLevi Y hχc) ((tsupport_frameLevi_subset Y χ).trans hχΩ)
  simpa only [mul_comm] using h

theorem FrameIneqOnBall.mono {u : ComplexModel n → ℝ} {m m' : ℝ} {x₀ : ComplexModel n}
    {r r' : ℝ} (h : FrameIneqOnBall u m x₀ r) (hm : m' ≤ m) (hr : r' ≤ r) :
    FrameIneqOnBall u m' x₀ r' := by
  intro Y hY χ hχ hχc hχ0 hsupp
  refine le_trans ?_ (h Y hY χ hχ hχc hχ0 (hsupp.trans (Metric.ball_subset_ball hr)))
  have : 0 ≤ ∫ x, χ x := integral_nonneg hχ0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hm hn]

theorem FrameIneqOnBall.add {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) {m m' : ℝ}
    {x₀ : ComplexModel n} {r : ℝ} (hball : Metric.ball x₀ r ⊆ Ω)
    (h : FrameIneqOnBall u m x₀ r) (h' : FrameIneqOnBall v m' x₀ r) :
    FrameIneqOnBall (fun z => u z + v z) (m + m') x₀ r := by
  intro Y hY χ hχ hχc hχ0 hsupp
  have h1 := h Y hY χ hχ hχc hχ0 hsupp
  have h2 := h' Y hY χ hχ hχc hχ0 hsupp
  have hΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n)) := hsupp.trans hball
  have e : ∫ x, (u x + v x) * frameLevi Y χ x =
      (∫ x, u x * frameLevi Y χ x) + ∫ x, v x * frameLevi Y χ x := by
    have hadd := integral_add (integrable_mul_frameLevi hu Y hχ hχc hΩ)
      (integrable_mul_frameLevi hv Y hχ hχc hΩ)
    refine Eq.trans ?_ hadd
    exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring)
  rw [e]
  linarith

theorem FrameIneqOnBall.smul {u : ComplexModel n → ℝ} {m : ℝ} {x₀ : ComplexModel n} {r : ℝ}
    (h : FrameIneqOnBall u m x₀ r) {a : ℝ} (ha : 0 ≤ a) :
    FrameIneqOnBall (fun z => a * u z) (a * m) x₀ r := by
  intro Y hY χ hχ hχc hχ0 hsupp
  have h1 := h Y hY χ hχ hχc hχ0 hsupp
  have e : ∫ x, a * u x * frameLevi Y χ x = a * ∫ x, u x * frameLevi Y χ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 ha
  linarith

/-! ### (1) ⇒ (3) -/

/-- **(1) ⇒ (3)** (S57): `(ddᶜu)ⁿ ≥ mⁿ ηⁿ` on `Ω`, `m > 0`, gives the frame inequalities with
constant `m` on `B(x₀, R/2)` whenever `B̄(x₀, R) ⊆ Ω`. -/
theorem frameIneqOnBall_of_ma_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {m : ℝ} (hm : 0 < m)
    (hμ : ENNReal.ofReal (mongeAmpereConst n * m ^ n) •
        volume.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω u hu)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω) :
    FrameIneqOnBall u m x₀ (R / 2) := by
  intro Y hY χ hχ hχc hχ0 hsupp
  have h := integral_mul_frameLevi_ge hn hu (pow_pos hm n) hμ hR hball hY hχ hχc hχ0 hsupp
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hm.le, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),
    Real.rpow_one] at h

/-- `|z|²` satisfies the frame inequalities with constant `1` on every ball. -/
theorem frameIneqOnBall_normSq (hn : 0 < n) (x₀ : ComplexModel n) {r : ℝ} (hr : 0 < r) :
    FrameIneqOnBall (fun z : ComplexModel n => ‖z‖ ^ 2) 1 x₀ r := by
  have hb : IsLocallyBoundedPshOn ⊤ fun z : ComplexModel n => ‖z‖ ^ 2 := by
    simpa only [one_mul] using SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq ⊤ one_pos
  have hlim := SGPT.PSH.BookDeepDomination.isBTLimit_mul_normSq (n := n) ⊤ zero_le_one
  simp only [one_mul] at hlim
  have heq := (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure hb).unique hlim
  have hμ : ENNReal.ofReal (mongeAmpereConst n * 1 ^ n) •
      volume.restrict ((⊤ : Opens (ComplexModel n)) : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure ⊤ _ hb := by
    rw [heq]
    simp only [one_pow, mul_one, one_mul, mongeAmpereConst, ENNReal.ofReal_one, le_refl]
  exact frameIneqOnBall_of_ma_ge hn hb one_pos hμ (R := 2 * r) (by positivity)
    (fun _ _ => trivial) |>.mono le_rfl (by linarith)

/-- **The degenerate case `m = 0`**: every locally bounded psh function satisfies
`L_Y u ≥ 0` (perturb by `ε|z|²` and let `ε → 0`). -/
theorem frameIneqOnBall_zero (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x₀ R ⊆ Ω) : FrameIneqOnBall u 0 x₀ (R / 2) := by
  intro Y hY χ hχ hχc hχ0 hsupp
  have hΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n)) :=
    hsupp.trans (Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hball))
  set I : ℝ := ∫ x, ‖x‖ ^ 2 * frameLevi Y χ x with hI
  have hkey : ∀ ε : ℝ, 0 < ε → -(ε * I) ≤ ∫ x, u x * frameLevi Y χ x := by
    intro ε hε
    have hq := SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq Ω hε
    have hw := SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add hu hq
    have hle := SGPT.PSH.BookDeepDomination.le_of_isBTLimit_add hu hq
      (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure hw)
      (SGPT.PSH.BookDeepDomination.isBTLimit_mul_normSq Ω hε.le)
    have hμ : ENNReal.ofReal (mongeAmpereConst n * ε ^ n) •
        volume.restrict (Ω : Set (ComplexModel n)) ≤
        canonicalBedfordTaylorMeasure Ω (fun z => u z + ε * ‖z‖ ^ 2) hw := by
      refine le_trans (le_of_eq ?_) hle
      rw [ENNReal.ofReal_mul (le_of_lt (by unfold mongeAmpereConst; positivity)),
        ENNReal.ofReal_pow hε.le, mul_comm, mongeAmpereConst]
    have h := frameIneqOnBall_of_ma_ge hn hw hε hμ hR hball Y hY χ hχ hχc hχ0 hsupp
    have e : ∫ x, (u x + ε * ‖x‖ ^ 2) * frameLevi Y χ x =
        (∫ x, u x * frameLevi Y χ x) + ε * I := by
      have hint2 : Integrable (fun x => ‖x‖ ^ 2 * frameLevi Y χ x) :=
        ((continuous_norm.pow 2).mul (continuous_frameLevi Y hχ)).integrable_of_hasCompactSupport
          (hasCompactSupport_frameLevi Y hχc).mul_left
      have hadd := integral_add (integrable_mul_frameLevi hu Y hχ hχc hΩ) (hint2.const_mul ε)
      rw [hI, ← integral_const_mul]
      refine Eq.trans ?_ hadd
      exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring)
    rw [e] at h
    have : 0 ≤ n * ε * ∫ x, χ x := by
      have hint0 : (0 : ℝ) ≤ ∫ x, χ x := integral_nonneg hχ0
      positivity
    linarith
  rw [mul_zero, zero_mul]
  by_contra hneg
  push Not at hneg
  set J : ℝ := ∫ x, u x * frameLevi Y χ x
  -- `-(ε I) ≤ J < 0` for every `ε > 0` is impossible
  have hI0 : 0 < I := by
    by_contra hI0
    push Not at hI0
    have := hkey 1 one_pos
    nlinarith
  have := hkey (-J / (2 * I)) (div_pos (by linarith) (by linarith))
  rw [div_mul_eq_mul_div, mul_comm (2 : ℝ) I, ← div_div, mul_div_assoc, div_self hI0.ne',
    mul_one] at this
  linarith

/-! ### (3) ⇒ (1) -/

/-- **Mollifications with a determinant bound from the frame inequalities** (FPT
`prop:bounded-monge-ampere-linear-density`, (3) ⇒ (1), first half; S57's
`exists_decreasingApproximation_det_ge` with the frame inequalities as hypothesis). -/
theorem exists_decreasingApproximation_det_ge_of_frameIneq (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    {m : ℝ} (hm : 0 ≤ m) {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x₀ R ⊆ Ω) (hframe : FrameIneqOnBall u m x₀ (R / 2)) :
    ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation ⟨Metric.ball x₀ (R / 4), Metric.isOpen_ball⟩ u f ∧
      ∀ j, ∀ z ∈ Metric.ball x₀ (R / 4), m ^ n ≤ (complexHessian (f j) z).det.re := by
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
  have hframe' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ‖Y.det‖ = 1 →
      n * m ≤ (Yᴴ * complexHessian (f j) z * Y).trace.re := by
    intro Y hY
    rw [← sum_leviForm_frameMap hf2 Y]
    have hineq := hframe Y hY χ hχd hχc hχ0 hχsupp
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
  exact pow_le_det_of_forall_frame hn hpsd hm hframe'

/-- **Mixed Monge–Ampère lower bound from determinant bounds of decreasing approximations**
(the measure half of S57's `mixedBedfordTaylor_ge_on_ball`). -/
theorem mixed_ge_on_ball_of_det_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u) {c : Fin n → ℝ}
    (hc : ∀ i, 0 < c i) {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x₀ R ⊆ Ω) {f : Fin n → ℕ → ComplexModel n → ℝ}
    (hf : ∀ i, IsDecreasingApproximation ⟨Metric.ball x₀ (R / 4), Metric.isOpen_ball⟩ (u i) (f i))
    (hdet : ∀ i j, ∀ z ∈ Metric.ball x₀ (R / 4), c i ≤ (complexHessian (f i j) z).det.re) :
    ENNReal.ofReal (mongeAmpereConst n * ∏ i, c i ^ ((n : ℝ)⁻¹)) •
        volume.restrict (Metric.ball x₀ (R / 4)) ≤
      (canonicalMixedBedfordTaylorMeasure Ω u hu).restrict (Metric.ball x₀ (R / 4)) := by
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
    canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hu hK
      (hKN.trans (subset_closure.trans hNrc.2))
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
  have hres := restrict_le_of_isCompact_le (Ω := N) hνf hcpt
  have hνN : ν.restrict (N : Set (ComplexModel n)) = ν := by
    rw [hν, Measure.restrict_smul, Measure.restrict_restrict_of_subset subset_rfl]
  rw [hνN] at hres
  calc ν = ν.restrict (N : Set (ComplexModel n)) := hνN.symm
    _ ≤ _ := Measure.restrict_mono subset_rfl hres

/-- **(3) ⇒ (1) with constant density** (FPT `prop:bounded-monge-ampere-linear-density`): if `u`
satisfies the frame inequalities with constant `m ≥ 0` on `B(x₀, R/2)`, `B̄(x₀, R) ⊆ Ω`, then
`(ddᶜu)ⁿ ≥ mⁿ ηⁿ` on `B(x₀, R/4)`. -/
theorem ma_ge_on_ball_of_frameIneq (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {m : ℝ} (hm : 0 ≤ m)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω)
    (hframe : FrameIneqOnBall u m x₀ (R / 2)) :
    ENNReal.ofReal (mongeAmpereConst n * m ^ n) • volume.restrict (Metric.ball x₀ (R / 4)) ≤
      (canonicalBedfordTaylorMeasure Ω u hu).restrict (Metric.ball x₀ (R / 4)) := by
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow hn.ne', mul_zero, ENNReal.ofReal_zero, zero_smul]
    exact Measure.zero_le _
  obtain ⟨f, hf, hdet⟩ := exists_decreasingApproximation_det_ge_of_frameIneq hn hu hm hR hball
    hframe
  have h := mixed_ge_on_ball_of_det_ge hn (u := fun _ => u) (fun _ => hu) (c := fun _ => m ^ n)
    (fun _ => pow_pos hpos n) hR hball (f := fun _ => f) (fun _ => hf) (fun _ => hdet)
  rw [canonicalMixedBedfordTaylorMeasure_diagonal] at h
  have e : ∏ _i : Fin n, (m ^ n) ^ ((n : ℝ)⁻¹) = m ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.pow_rpow_inv_natCast hm hn.ne']
  rwa [e] at h

end SGPT.Envelopes.MADirichlet
