import SGPT.NPP.DNNefCompare

/-!
# Smooth approximants of envelopes in nef and big classes

Lane DN (`thm:DNT23_C11bar`, nef and big classes).  Source: Berman 2019
(`references/berman19-zero-temperature`), proof of Proposition 3.5 ("nef and big") and Remark 3.6,
for envelopes `P_θ(F)` with smooth obstacles `F`.

For a nef class `{θ}` (`NefWithRespectTo ω θ`) with a Kähler current `θ + ddᶜψ ≥ ω₀ ≥ c₀ ω`, and
for every `ε ∈ (0, 1]`, `δ ∈ (0, 1]` and smooth obstacle `F ≥ ψ` with `F ≤ B` and
`Δ_ω F + tr_ω(θ - ω₀) ≤ S`, we produce a smooth `v` with, at every point `y` where `ψ(y) = r` is
finite,

* `v - δ - (ε/c₀)(B - r) ≤ P_θ(F) ≤ v + δ`, and
* `0 ≤ Δ_ω v + tr_ω θ + εN ≤ 2(T + S) e^{a(B + 2 - r)}`,

with `a, T` independent of `ε, δ, F, S, B`.  The function `v = u + h` comes from a Kähler
representative `A = θ + εω + ddᶜh` (`exists_isKahler_of_nef`) and a β-solution `u` with reference
volume `ω^N` (`exists_refBetaSolution_close`); the second bound is the Tsuji-weighted trace
estimate (`tsuji_traceForm_le`) for the background `A`, the weight `ψ - h` and the form
`η = θ - ω₀ + ddᶜh`, for which `A - η = εω + ω₀`.

* `traceForm_add`, `traceForm_smul`, `traceForm_ddc`, `traceForm_self`: linearity of `tr_ω`.
* `exists_nef_approximants`: the approximants.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.NPP.DNNef

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open KahlerLaplacianChart AubinYauEstimate
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Linearity of the trace -/

theorem traceForm_add (w : KahlerBackground N Y) (α β : ClosedRealOneOneForm N Y) (y : Y) :
    traceForm w.form.val (α + β).val y =
      traceForm w.form.val α.val y + traceForm w.form.val β.val y := by
  unfold traceForm chartTrace
  rw [ClosedRealOneOneForm.coeff_add, normalizedHermitianMatrix_add,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem traceForm_smul (w : KahlerBackground N Y) (c : ℝ) (α : ClosedRealOneOneForm N Y)
    (y : Y) : traceForm w.form.val (c • α).val y = c * traceForm w.form.val α.val y := by
  unfold traceForm chartTrace
  rw [ClosedRealOneOneForm.coeff_smul, normalizedHermitianMatrix_smul,
    Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem traceForm_ddc (w : KahlerBackground N Y) {h : Y → ℝ} (hh : ChartSmooth (n := N) h)
    (y : Y) : traceForm w.form.val (ddcClosedForm h hh).val y = laplacian w.form.val h y := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  unfold traceForm chartTrace
  rw [laplacian_eq_trace, ddcClosedForm_coeff, normalizedHermitianMatrix_smoothDDC
    (contDiffAt_two_of_contDiffOn e.val.open_target (hh e) hz)]

theorem traceForm_self (w : KahlerBackground N Y) (y : Y) :
    traceForm w.form.val w.form.val y = N := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  unfold traceForm chartTrace
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (posDef_coeff w.isKahler.1 hz).det_pos.ne'), Matrix.trace_one]
  simp

theorem traceForm_sub (w : KahlerBackground N Y) (α β : ClosedRealOneOneForm N Y) (y : Y) :
    traceForm w.form.val (α - β).val y =
      traceForm w.form.val α.val y - traceForm w.form.val β.val y := by
  have h : α - β = α + (-1 : ℝ) • β := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, traceForm_add, traceForm_smul]
  ring

/-! ### The approximants -/

variable [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Smooth approximants of `P_θ(F)` for a nef class** (Berman 2019, Proposition 3.5, with the
Tsuji weight of a Kähler current).  See the module docstring. -/
theorem exists_nef_approximants (w ω₀ : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y)
    (hnef : NefWithRespectTo w θ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hω₀ : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
      c₀ * w.form.val.coeff e z ![v, Complex.I • v] ≤ ω₀.form.val.coeff e z ![v, Complex.I • v])
    {ψ : Y → EReal} (hψ : IsThetaPshPotential (θ - ω₀.form).val ψ) :
    ∃ a T : ℝ, 0 < a ∧ 0 ≤ T ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (F : Y → ℝ), ChartSmooth (n := N) F → ∀ (S : ℝ),
      (∀ y, laplacian w.form.val F y + traceForm w.form.val (θ - ω₀.form).val y ≤ S) →
      ∀ (B : ℝ), (∀ y, F y ≤ B) → (∀ y, ψ y ≤ (F y : EReal)) →
      ∃ v : Y → ℝ, ChartSmooth (n := N) v ∧ ∀ (y : Y) (r : ℝ), ψ y = (r : EReal) →
        ((v y - δ - ε / c₀ * (B - r) : ℝ) : EReal) ≤
          rooftopEnvelope θ.val (fun y => (F y : EReal)) y ∧
        rooftopEnvelope θ.val (fun y => (F y : EReal)) y ≤ ((v y + δ : ℝ) : EReal) ∧
        0 ≤ laplacian w.form.val v y + traceForm w.form.val θ.val y + ε * N ∧
        laplacian w.form.val v y + traceForm w.form.val θ.val y + ε * N ≤
          2 * (T + S) * Real.exp (a * (B + 2 - r)) := by
  classical
  obtain ⟨a, T, β₀, ha, hT, -, htsuji⟩ := tsuji_traceForm_le w ω₀
  refine ⟨a, T, ha, hT, fun ε hε0 hε1 δ hδ0 hδ1 F hF S hFS B hFB hψF => ?_⟩
  have hg : w.form.val.IsHermitian := w.isKahler.1
  have hFc : Continuous F := YauUniformEstimate.continuous_of_chartSmooth hF
  -- the Kähler representative of `{θ + εω}`
  obtain ⟨h, hh, hK⟩ := exists_isKahler_of_nef w hnef hε0
  set A : KahlerBackground N Y := ⟨θ + ε • w.form + ddcClosedForm h hh, hK⟩ with hAdef
  have hF' : ChartSmooth (n := N) (fun y => F y - h y) := fun e => (hF e).sub (hh e)
  obtain ⟨β, hβ, u, hu, huK, hdens, hfin, hclose⟩ :=
    exists_refBetaSolution_close A w hF' hδ0 β₀
  -- the weight form and the weight
  set η : ClosedRealOneOneForm N Y := (θ - ω₀.form) + ddcClosedForm h hh with hηdef
  have hψ' : IsThetaPshPotential η.val (fun y => ψ y - (h y : EReal)) :=
    thetaPshPotential_sub_smooth hh (fun e z hz => by
      rw [hηdef, ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]) hψ
  -- `ψ` is `θ`-psh and `(θ + εω)`-psh
  have hω₀semi : ω₀.form.val.IsSemipositive := KahlerBackground.isSemipositive ω₀
  have hψθ : IsThetaPshPotential θ.val ψ := by
    have := isThetaPshPotential_add_semipositive hω₀semi hψ
    rwa [sub_add_cancel] at this
  have hεw : (ε • w.form).val.IsSemipositive := by
    intro e z hz v
    rw [ClosedRealOneOneForm.coeff_smul]
    exact mul_nonneg hε0.le (KahlerBackground.isSemipositive w e z hz v)
  have hψθε : IsThetaPshPotential (θ + ε • w.form).val ψ :=
    isThetaPshPotential_add_semipositive hεw hψθ
  -- the envelope in the class `{θ + εω}`
  set V : Y → ℝ := fun y => envelopeReal A.form (fun y => F y - h y) y + h y with hVdef
  have hshift : ∀ y, rooftopEnvelope (θ + ε • w.form).val (fun y => (F y : EReal)) y =
      ((V y : ℝ) : EReal) := by
    intro y
    rw [rooftopEnvelope_shift (θ + ε • w.form) hh F y]
    have := hfin y
    simp only [hAdef] at this
    rw [this, ← EReal.coe_add]
  have hPε : IsThetaPshPotential (θ + ε • w.form).val
      (rooftopEnvelope (θ + ε • w.form).val fun y => (F y : EReal)) :=
    isThetaPshPotential_rooftopEnvelope_of_continuous w (θ + ε • w.form) hFc hψθε
  have hVpsh : IsThetaPshPotential (θ + ε • w.form).val (fun y => ((V y : ℝ) : EReal)) := by
    have hfun : (rooftopEnvelope (θ + ε • w.form).val fun y => (F y : EReal)) =
        fun y => ((V y : ℝ) : EReal) := funext hshift
    rwa [hfun] at hPε
  have hVF : ∀ y, V y ≤ F y := fun y => by
    have := rooftopEnvelope_le_of_isThetaPshPotential hFc hPε y
    rw [hshift] at this
    exact EReal.coe_le_coe_iff.mp this
  have hPθle : ∀ y, rooftopEnvelope θ.val (fun y => (F y : EReal)) y ≤ ((V y : ℝ) : EReal) :=
    fun y => by
      rw [← hshift]
      exact rooftopEnvelope_le_add_semipositive w θ (ε • w.form) hεw hψθ hFc y
  have hψPθ : ∀ y, ψ y ≤ rooftopEnvelope θ.val (fun y => (F y : EReal)) y :=
    le_rooftopEnvelope hψθ (quasiEverywhere_of_forall hψF)
  -- the trace bounds
  have hAη : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
      ω₀.form.val.coeff e z ![v, Complex.I • v] ≤
          A.form.val.coeff e z ![v, Complex.I • v] - η.val.coeff e z ![v, Complex.I • v] ∧
        A.form.val.coeff e z ![v, Complex.I • v] - η.val.coeff e z ![v, Complex.I • v] ≤
          ω₀.form.val.coeff e z ![v, Complex.I • v] + w.form.val.coeff e z ![v, Complex.I • v] := by
    intro e z hz v
    have hdiff : A.form.val.coeff e z ![v, Complex.I • v] - η.val.coeff e z ![v, Complex.I • v] =
        ε * w.form.val.coeff e z ![v, Complex.I • v] +
          ω₀.form.val.coeff e z ![v, Complex.I • v] := by
      rw [hAdef, hηdef]
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, sub_eq_add_neg,
        ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply, smul_eq_mul]
      ring
    have hw0 := KahlerBackground.isSemipositive w e z hz v
    rw [hdiff]
    constructor
    · nlinarith
    · nlinarith
  have hFS' : ∀ y, laplacian w.form.val (fun y => F y - h y) y + traceForm w.form.val η.val y ≤ S := by
    intro y
    rw [laplacian_sub w.form.val hF hh, hηdef, traceForm_add, traceForm_ddc]
    have := hFS y
    linarith
  -- the comparison and the bounds at a finite point of `ψ`
  refine ⟨fun y => u y + h y, fun e => (hu e).add (hh e), fun y r hr => ?_⟩
  have hcl := abs_le.mp (hclose y)
  have hr' : (ψ y - (h y : EReal)) = ((r - h y : ℝ) : EReal) := by
    rw [hr, EReal.coe_sub]
  -- the comparison
  have hcomp := sub_le_rooftopEnvelope_of_kahlerCurrent w ω₀ θ hc₀ hω₀ hψ hε0 hψF hVpsh hVF hr
  have hrV : r ≤ V y := by
    have := (hψPθ y).trans (hPθle y)
    rw [hr] at this
    exact EReal.coe_le_coe_iff.mp this
  have hVB : V y ≤ B := (hVF y).trans (hFB y)
  have hs : ε / (ε + c₀) * (V y - r) ≤ ε / c₀ * (B - r) := by
    have h1 : ε / (ε + c₀) ≤ ε / c₀ := div_le_div_of_nonneg_left hε0.le hc₀ (by linarith)
    have h2 : V y - r ≤ B - r := by linarith
    calc ε / (ε + c₀) * (V y - r) ≤ ε / c₀ * (V y - r) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ ε / c₀ * (B - r) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hε0.le hc₀.le)
  have hVu : V y = envelopeReal A.form (fun y => F y - h y) y + h y := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hcomp
    rw [hVu] at hs ⊢
    linarith
  · refine (hPθle y).trans (EReal.coe_le_coe_iff.mpr ?_)
    rw [hVu]
    linarith
  -- the Laplacian of `v = u + h`
  · have hsplit := traceForm_add_ddc w A hu y
    have hA : traceForm w.form.val A.form.val y =
        traceForm w.form.val θ.val y + ε * N + laplacian w.form.val h y := by
      rw [hAdef]
      show traceForm w.form.val (θ + ε • w.form + ddcClosedForm h hh).val y = _
      rw [traceForm_add, traceForm_add, traceForm_smul, traceForm_self, traceForm_ddc]
    rw [laplacian_add w.form.val hu hh]
    have h0 := traceForm_nonneg hg huK y
    linarith
  · have hsplit := traceForm_add_ddc w A hu y
    have hA : traceForm w.form.val A.form.val y =
        traceForm w.form.val θ.val y + ε * N + laplacian w.form.val h y := by
      rw [hAdef]
      show traceForm w.form.val (θ + ε • w.form + ddcClosedForm h hh).val y = _
      rw [traceForm_add, traceForm_add, traceForm_smul, traceForm_self, traceForm_ddc]
    rw [laplacian_add w.form.val hu hh]
    -- the Tsuji estimate
    have hm : ∀ y, (ψ y - (h y : EReal)) ≤ ((u y - (-1) : ℝ) : EReal) := by
      intro y'
      have hcl' := abs_le.mp (hclose y')
      have h1 := (hψPθ y').trans (hPθle y')
      by_cases hb : ψ y' = ⊥
      · rw [hb, EReal.bot_sub]; exact bot_le
      · have htop : ψ y' ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top y'
        rw [← EReal.coe_toReal htop hb] at h1 ⊢
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have := EReal.coe_le_coe_iff.mp h1
        simp only [hVdef] at this
        linarith
    have htr := htsuji η A hAη β hβ (fun y => F y - h y) hF' S hFS' u hu huK hdens
      (fun y => ψ y - (h y : EReal)) hψ'.1 ⟨y, by rw [hr']; exact EReal.coe_ne_bot _⟩ (-1) hm
      y (r - h y) hr'
    have hexp : Real.exp (a * (u y - (r - h y) - -1)) ≤ Real.exp (a * (B + 2 - r)) := by
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ ha.le)
      rw [hVu] at hVB
      linarith
    have hTS : 0 ≤ 2 * (T + S) := by
      by_contra hneg
      push Not at hneg
      have : 2 * (T + S) * Real.exp (a * (u y - (r - h y) - -1)) < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      have h0 := traceForm_nonneg hg huK y
      linarith
    have := mul_le_mul_of_nonneg_left hexp hTS
    linarith

end SGPT.NPP.DNNef
