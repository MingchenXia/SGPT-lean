import SGPT.Okounkov.TranscendentalWNRegC11bar
import SGPT.Okounkov.TranscendentalWNRegSingular
import SGPT.Foundations.Analysis.Pending.StokesCutoff
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization

/-!
# Rooftop envelopes of two smooth obstacles are `C^{1,1̄}` (Darvas–Rubinstein)

Lane NPP-DNT (`claude-npp-dnt`).  Source `prop:DR16_C11bar` (`author/chapter_npp.tex`,
lines 1221–1224): for a Kähler form `ω` and `f₁, f₂ ∈ C^{1,1̄}(X)`,
`P_ω(min{f₁, f₂}) ∈ C^{1,1̄}(X)`.  The book cites Darvas–Rubinstein, Theorem 2.5, whose proof
rests on the regularity of envelopes of a single obstacle.

This file proves the proposition for **chart-smooth** obstacles `f₁, f₂` on a compact connected
complex manifold with a Kähler form `ω`: the envelope `P_ω(min{f₁, f₂})` is real-valued and its
distributional complex Hessian is locally bounded in every chart (`IsCOneOneBar` of WN-REG), i.e.
`0 ≤ ω + ddᶜP_ω(min{f₁, f₂}) ≤ M ω` in the sense of currents.  This is the quasi-psh form of the
book's `C^{1,1̄}` (Darvas–Rubinstein remark that for `ω`-psh functions a bounded `ω`-Laplacian is
the same as a bounded complex Hessian).

## Proof

The minimum of two smooth functions is not smooth, so we smooth it from below:
`min_ε(f₁, f₂) = f₂ - ε · posPart((f₂ - f₁)/ε)` with TN's smooth convex positive part
(`SmoothMax.posPart`, `0 ≤ posPart' ≤ 1`).  Then

* `min{f₁, f₂} - ε ≤ min_ε(f₁, f₂) ≤ min{f₁, f₂}` (`smoothMin_le`, `min_sub_le_smoothMin`);
* by convexity of `posPart`, `ddᶜ min_ε(f₁, f₂) ≤ (1 - t) ddᶜf₂ + t ddᶜf₁ ≤ S ω` on every complex
  line, with `t = posPart'(…) ∈ [0, 1]` and `S` a common upper bound of `ddᶜf₁, ddᶜf₂`
  (`smoothMin_ddc_line_le`).

Berman's estimate for smooth obstacles (`bermanSmoothEnvelopeStatement`, WN-REG) applied to
`min_{1/(k+1)}(f₁, f₂)` gives line-bounded smooth approximations of the envelopes
`P_ω(min_{1/(k+1)})` with a bound `M` independent of `k`.  The envelope operator is
`1`-Lipschitz for the sup norm (`envelope_sandwich`), so these envelopes converge uniformly to
`P_ω(min{f₁, f₂})`, which is therefore real-valued; a diagonal argument
(`hasSmoothLineBoundApproximation_of_tendstoUniformly`) gives a line-bounded smooth
approximation of `P_ω(min{f₁, f₂})` itself, and `isCOneOneBar_of_hasSmoothLineBoundApproximation`
concludes.

## Main results

* `envelope_min_hasSmoothLineBoundApproximation`
* `isCOneOneBar_envelopeReal_min` (source `prop:DR16_C11bar`, smooth obstacles).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Envelopes.DNTReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg

/-! ### The smooth positive part -/

theorem smoothPosPart_nonneg (t : ℝ) : 0 ≤ SmoothMax.posPart t := by
  rcases le_total t (-1) with h | h
  · rw [SmoothMax.posPart_eq_zero h]
  · have := SmoothMax.posPart_monotone h
    rwa [SmoothMax.posPart_eq_zero le_rfl] at this

theorem max_le_smoothPosPart (t : ℝ) : max t 0 ≤ SmoothMax.posPart t :=
  max_le (le_smoothPosPart t) (smoothPosPart_nonneg t)

theorem smoothPosPart_le_max_add_one (t : ℝ) : SmoothMax.posPart t ≤ max t 0 + 1 := by
  rcases le_total 1 t with h | h
  · rw [SmoothMax.posPart_eq_self h]
    linarith [le_max_left t 0]
  · have := smoothPosPart_le_one h
    linarith [le_max_right t 0]

theorem max_le_mul_smoothPosPart {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    max s 0 ≤ ε * SmoothMax.posPart (s / ε) := by
  have h := mul_le_mul_of_nonneg_left (max_le_smoothPosPart (s / ε)) hε.le
  rwa [mul_max_of_nonneg _ _ hε.le, mul_div_cancel₀ s hε.ne', mul_zero] at h

theorem mul_smoothPosPart_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ε * SmoothMax.posPart (s / ε) ≤ max s 0 + ε := by
  have h := mul_le_mul_of_nonneg_left (smoothPosPart_le_max_add_one (s / ε)) hε.le
  rwa [mul_add, mul_max_of_nonneg _ _ hε.le, mul_div_cancel₀ s hε.ne', mul_zero,
    mul_one] at h

theorem min_eq_sub_max (a b : ℝ) : min a b = b - max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

/-! ### The smoothed minimum -/

section SmoothMin

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The smoothed minimum `min_ε(f₁, f₂) = f₂ - ε · posPart((f₂ - f₁)/ε)`. -/
def smoothMin (ε : ℝ) (f₁ f₂ : Y → ℝ) (y : Y) : ℝ :=
  f₂ y - ε * SmoothMax.posPart ((f₂ y - f₁ y) / ε)

omit [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] in
theorem smoothMin_le {ε : ℝ} (hε : 0 < ε) (f₁ f₂ : Y → ℝ) (y : Y) :
    smoothMin ε f₁ f₂ y ≤ min (f₁ y) (f₂ y) := by
  rw [min_eq_sub_max]
  unfold smoothMin
  linarith [max_le_mul_smoothPosPart hε (f₂ y - f₁ y)]

omit [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] in
theorem min_sub_le_smoothMin {ε : ℝ} (hε : 0 < ε) (f₁ f₂ : Y → ℝ) (y : Y) :
    min (f₁ y) (f₂ y) - ε ≤ smoothMin ε f₁ f₂ y := by
  rw [min_eq_sub_max]
  unfold smoothMin
  linarith [mul_smoothPosPart_le hε (f₂ y - f₁ y)]

omit [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] in
theorem abs_smoothMin_sub_le {ε : ℝ} (hε : 0 < ε) (f₁ f₂ : Y → ℝ) (y : Y) :
    |smoothMin ε f₁ f₂ y - min (f₁ y) (f₂ y)| ≤ ε := by
  rw [abs_le]
  constructor
  · linarith [min_sub_le_smoothMin hε f₁ f₂ y]
  · linarith [smoothMin_le hε f₁ f₂ y]

theorem chartSmooth_smoothMin (ε : ℝ) {f₁ f₂ : Y → ℝ} (h₁ : ChartSmooth (n := N) f₁)
    (h₂ : ChartSmooth (n := N) f₂) : ChartSmooth (n := N) (smoothMin ε f₁ f₂) := by
  intro e
  have hg : ContDiffOn ℝ ∞ (fun z => (f₂ (e.val.symm z) - f₁ (e.val.symm z)) / ε)
      e.val.target :=
    ((h₂ e).sub (h₁ e)).div_const ε
  exact (h₂ e).sub (contDiffOn_const.mul (SmoothMax.contDiff_posPart.comp_contDiffOn hg))

/-- **The smoothed minimum keeps a common upper bound of `ddᶜ`**: if `ddᶜf₁ ≤ S ω` and
`ddᶜf₂ ≤ S ω` on every complex line, then `ddᶜ min_ε(f₁, f₂) ≤ S ω` on every complex line. -/
theorem smoothMin_ddc_line_le {ε : ℝ} (hε : 0 < ε) (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : ChartSmooth (n := N) f₁) (h₂ : ChartSmooth (n := N) f₂) {S : ℝ}
    (hS₁ : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm f₁ h₁).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    (hS₂ : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm f₂ h₂).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    (e : ComplexChart N Y) (z : ComplexModel N) (hz : z ∈ e.val.target) (v : ComplexModel N) :
    (ddcClosedForm (smoothMin ε f₁ f₂) (chartSmooth_smoothMin ε h₁ h₂)).val.coeff e z
        ![v, Complex.I • v] ≤
      S * A.form.val.coeff e z ![v, Complex.I • v] := by
  have l1 := hS₁ e z hz v
  have l2 := hS₂ e z hz v
  rw [ddc_line_eq h₁ e hz v, div_le_iff₀ Real.pi_pos] at l1
  rw [ddc_line_eq h₂ e hz v, div_le_iff₀ Real.pi_pos] at l2
  rw [ddc_line_eq (chartSmooth_smoothMin ε h₁ h₂) e hz v, div_le_iff₀ Real.pi_pos]
  set F₁ : ComplexModel N → ℝ := fun w => f₁ (e.val.symm w) with hF₁def
  set F₂ : ComplexModel N → ℝ := fun w => f₂ (e.val.symm w) with hF₂def
  have hF₁ : ContDiffAt ℝ 2 F₁ z := contDiffAt_two_chart h₁ e hz
  have hF₂ : ContDiffAt ℝ 2 F₂ z := contDiffAt_two_chart h₂ e hz
  set g : ComplexModel N → ℝ := fun w => (F₂ w - F₁ w) / ε with hgdef
  have hg : ContDiffAt ℝ 2 g z := (hF₂.sub hF₁).div_const ε
  have hp : ContDiffAt ℝ 2 SmoothMax.posPart (g z) :=
    (SmoothMax.contDiff_posPart.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hpg : ContDiffAt ℝ 2 (fun w => SmoothMax.posPart (g w)) z :=
    hp.comp (f := g) z hg
  have hchain := StokesCutoff.mul_leviForm_le_leviForm_comp hp hg
    (deriv_deriv_smoothPosPart_nonneg _) v
  rw [SmoothMax.deriv_posPart] at hchain
  -- the Levi form of `g`
  have hlg : leviForm g z v = (leviForm F₂ z v - leviForm F₁ z v) / ε := by
    have hfun : g = ε⁻¹ • fun w => F₂ w - F₁ w := by
      funext w
      simp only [hgdef, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, leviForm_smul (hF₂.sub hF₁), leviForm_sub' hF₂ hF₁]
    ring
  -- the Levi form of the smoothed minimum
  have hlm : leviForm (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) z v =
      leviForm F₂ z v - ε * leviForm (fun w => SmoothMax.posPart (g w)) z v := by
    have hfun : (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) =
        F₂ + (-ε) • fun w => SmoothMax.posPart (g w) := by
      funext w
      simp only [smoothMin, hF₁def, hF₂def, hgdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, leviForm_add (v := (-ε) • fun w => SmoothMax.posPart (g w)) hF₂
      (hpg.const_smul (-ε)), leviForm_smul hpg]
    ring
  rw [hlm]
  rw [hlg] at hchain
  set t := SmoothMax.trans (g z) with ht
  have ht0 : 0 ≤ t := SmoothMax.trans_nonneg _
  have ht1 : t ≤ 1 := SmoothMax.trans_le_one _
  have hεchain : t * (leviForm F₂ z v - leviForm F₁ z v) ≤
      ε * leviForm (fun w => SmoothMax.posPart (g w)) z v := by
    have h := mul_le_mul_of_nonneg_left hchain hε.le
    have heq : ε * (t * ((leviForm F₂ z v - leviForm F₁ z v) / ε)) =
        t * (leviForm F₂ z v - leviForm F₁ z v) := by
      field_simp
    linarith
  have hc1 := mul_le_mul_of_nonneg_left l1 ht0
  have hc2 := mul_le_mul_of_nonneg_left l2 (sub_nonneg.mpr ht1)
  nlinarith

end SmoothMin

/-! ### Uniform comparison of envelopes -/

section Envelope

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem ereal_sandwich {a : EReal} {r c : ℝ} (h1 : a ≤ (r : EReal) + (c : EReal))
    (h2 : (r : EReal) ≤ a + (c : EReal)) :
    a = ((a.toReal : ℝ) : EReal) ∧ |a.toReal - r| ≤ c := by
  have hbot : a ≠ ⊥ := by
    rintro rfl
    rw [EReal.bot_add] at h2
    exact EReal.coe_ne_bot r (le_bot_iff.mp h2)
  have htop : a ≠ ⊤ := by
    rintro rfl
    rw [← EReal.coe_add] at h1
    exact EReal.coe_ne_top _ (top_le_iff.mp h1)
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, a = (b : EReal) := ⟨a.toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  refine ⟨by rw [EReal.toReal_coe], ?_⟩
  rw [EReal.toReal_coe, abs_le]
  constructor <;> linarith

/-- **The envelope is `1`-Lipschitz for the sup norm**: if `|F - G| ≤ c` and `P_θ(F)` is
real-valued, then so is `P_θ(G)`, and `|P_θ(G) - P_θ(F)| ≤ c`. -/
theorem envelope_sandwich (θ : ClosedRealOneOneForm N Y) {F G : Y → ℝ} {c : ℝ}
    (hFG : ∀ y, |F y - G y| ≤ c)
    (hF : ∀ x, rooftopEnvelope θ.val (fun y => (F y : EReal)) x =
      ((envelopeReal θ F x : ℝ) : EReal)) :
    (∀ x, rooftopEnvelope θ.val (fun y => (G y : EReal)) x =
      ((envelopeReal θ G x : ℝ) : EReal)) ∧
    ∀ x, |envelopeReal θ G x - envelopeReal θ F x| ≤ c := by
  have hup : ∀ x, rooftopEnvelope θ.val (fun y => (G y : EReal)) x ≤
      rooftopEnvelope θ.val (fun y => (F y : EReal)) x + (c : EReal) := by
    intro x
    have hmono := rooftopEnvelope_mono (θ := θ.val) (f := fun y => (G y : EReal))
      (g := fun y => (F y : EReal) + (c : EReal)) fun y => by
        show (G y : EReal) ≤ (F y : EReal) + (c : EReal)
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith [(abs_le.mp (hFG y)).1]
    rw [RooftopEnvelopeNormalization.rooftopEnvelope_add_const] at hmono
    exact hmono x
  have hlow : ∀ x, rooftopEnvelope θ.val (fun y => (F y : EReal)) x ≤
      rooftopEnvelope θ.val (fun y => (G y : EReal)) x + (c : EReal) := by
    intro x
    have hmono := rooftopEnvelope_mono (θ := θ.val) (f := fun y => (F y : EReal))
      (g := fun y => (G y : EReal) + (c : EReal)) fun y => by
        show (F y : EReal) ≤ (G y : EReal) + (c : EReal)
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith [(abs_le.mp (hFG y)).2]
    rw [RooftopEnvelopeNormalization.rooftopEnvelope_add_const] at hmono
    exact hmono x
  have key : ∀ x, rooftopEnvelope θ.val (fun y => (G y : EReal)) x =
        (((rooftopEnvelope θ.val (fun y => (G y : EReal)) x).toReal : ℝ) : EReal) ∧
      |(rooftopEnvelope θ.val (fun y => (G y : EReal)) x).toReal - envelopeReal θ F x| ≤ c := by
    intro x
    have h1 := hup x
    have h2 := hlow x
    rw [hF x] at h1 h2
    exact ereal_sandwich h1 h2
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

end Envelope

/-! ### A diagonal argument for line-bounded approximations -/

section Diagonal

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem one_div_succ_le_one_div_succ {k₀ k : ℕ} (h : k₀ ≤ k) :
    1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
  one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ h)

/-- **Diagonal argument**: a uniform limit of functions which have line-bounded smooth
approximations with a common bound `M` has a line-bounded smooth approximation with bound `M`. -/
theorem hasSmoothLineBoundApproximation_of_tendstoUniformly (A : KahlerBackground N Y)
    {w b : ℕ → Y → ℝ} {u : Y → ℝ} {M : ℝ}
    (hw : ∀ k, HasSmoothLineBoundApproximation A (w k) (b k)) (hb : ∀ k x, b k x ≤ M)
    (hconv : TendstoUniformly w u atTop) :
    HasSmoothLineBoundApproximation A u (fun _ => M) := by
  have hpick : ∀ k : ℕ, ∃ v : Y → ℝ, ∃ hv : ChartSmooth (n := N) v,
      (∀ x, dist (w k x) (v x) < 1 / ((k : ℝ) + 1)) ∧
      (A.form + ddcClosedForm v hv).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v' : ComplexModel N,
        (A.form + ddcClosedForm v hv).val.coeff e z ![v', Complex.I • v'] ≤
          (M + 1 / ((k : ℝ) + 1)) * A.form.val.coeff e z ![v', Complex.I • v'] := by
    intro k
    obtain ⟨uj, huj, hunif, hK, hline⟩ := hw k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h1 := (Metric.tendstoUniformly_iff.mp hunif) _ hpos
    have h2 := hline _ hpos
    obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
    refine ⟨uj j, huj j, hj1, hK j, fun e z hz v' => (hj2 e z hz v').trans ?_⟩
    have hA : 0 ≤ A.form.val.coeff e z ![v', Complex.I • v'] := A.isSemipositive e z hz v'
    exact mul_le_mul_of_nonneg_right (by linarith [hb k (e.val.symm z)]) hA
  choose v hv hdist hK hline using hpick
  refine ⟨v, hv, ?_, hK, fun ε hε => ?_⟩
  · rw [Metric.tendstoUniformly_iff] at hconv ⊢
    intro δ hδ
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (half_pos hδ)
    filter_upwards [hconv _ (half_pos hδ), eventually_ge_atTop k₀] with k hk hkk x
    have h1 := hk x
    have h2 := hdist k x
    have h3 := one_div_succ_le_one_div_succ hkk
    calc dist (u x) (v k x) ≤ dist (u x) (w k x) + dist (w k x) (v k x) := dist_triangle _ _ _
      _ < δ := by linarith
  · obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop k₀] with k hk e z hz v'
    refine (hline k e z hz v').trans (mul_le_mul_of_nonneg_right ?_ (A.isSemipositive e z hz v'))
    linarith [one_div_succ_le_one_div_succ hk]

end Diagonal

/-! ### `prop:DR16_C11bar` for smooth obstacles -/

section Main

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A common upper bound `ddᶜfᵢ ≤ S ω` for two chart-smooth functions on a compact manifold. -/
theorem exists_ddc_line_le_of_chartSmooth [CompactSpace Y] (A : KahlerBackground N Y)
    {f : Y → ℝ} (hf : ChartSmooth (n := N) f) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v] := by
  have hfn : ChartSmooth (n := N) (fun x => -f x) := fun e => (hf e).neg
  obtain ⟨S, hS0, hS⟩ := KahlerDomination.exists_isSemipositive_add_smul
    (ddcClosedForm (fun x => -f x) hfn).val A.form.val A.isKahler.1
  refine ⟨S, hS0.le, fun e z hz v => ?_⟩
  have h := hS e z hz v
  have hneg : leviForm (fun w => -f (e.val.symm w)) z v =
      -leviForm (fun w => f (e.val.symm w)) z v :=
    leviForm_neg (fun w => f (e.val.symm w)) z v
  rw [ddc_line_eq hfn e hz v, hneg] at h
  rw [ddc_line_eq hf e hz v]
  have : -leviForm (fun w => f (e.val.symm w)) z v / Real.pi =
      -(leviForm (fun w => f (e.val.symm w)) z v / Real.pi) := by ring
  linarith

/-- **`P_ω(min{f₁, f₂})` for smooth obstacles**: on a compact connected complex manifold with a
Kähler form `ω`, for chart-smooth `f₁, f₂` the envelope `P_ω(min{f₁, f₂})` is real-valued and is a
uniform limit of chart-smooth `u_j` with `ω + ddᶜu_j` Kähler and, for every `ε > 0` and large `j`,
`ω + ddᶜu_j ≤ (M + ε) ω` on every complex line, for one constant `M`. -/
theorem envelope_min_hasSmoothLineBoundApproximation [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : ChartSmooth (n := N) f₁)
    (h₂ : ChartSmooth (n := N) f₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    ∃ M : ℝ, HasSmoothLineBoundApproximation A
      (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) (fun _ => M) := by
  -- a common upper bound for `ddᶜfᵢ`
  obtain ⟨S₁, hS₁0, hS₁⟩ := exists_ddc_line_le_of_chartSmooth A h₁
  obtain ⟨S₂, hS₂0, hS₂⟩ := exists_ddc_line_le_of_chartSmooth A h₂
  set S := max S₁ S₂ with hSdef
  have hS0 : 0 ≤ S := le_max_of_le_left hS₁0
  have hup : ∀ (f : Y → ℝ) (hf : ChartSmooth (n := N) f) (S' : ℝ), S' ≤ S →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] ≤
          S' * A.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, (ddcClosedForm f hf).val.coeff e z ![v, Complex.I • v] ≤
          S * A.form.val.coeff e z ![v, Complex.I • v] := by
    intro f hf S' hS' h e z hz v
    exact (h e z hz v).trans (mul_le_mul_of_nonneg_right hS'
      (A.isSemipositive e z hz v))
  have hS₁' := hup f₁ h₁ S₁ (le_max_left _ _) hS₁
  have hS₂' := hup f₂ h₂ S₂ (le_max_right _ _) hS₂
  -- bounds for the obstacles
  obtain ⟨B₁, hB₁⟩ := YauContinuityMethod.exists_abs_le h₁
  obtain ⟨B₂, hB₂⟩ := YauContinuityMethod.exists_abs_le h₂
  set B := max B₁ B₂ with hBdef
  have hminlo : ∀ y, -B ≤ min (f₁ y) (f₂ y) := fun y =>
    le_min (by linarith [(abs_le.mp (hB₁ y)).1, le_max_left B₁ B₂])
      (by linarith [(abs_le.mp (hB₂ y)).1, le_max_right B₁ B₂])
  have hminup : ∀ y, min (f₁ y) (f₂ y) ≤ B := fun y =>
    (min_le_left _ _).trans (by linarith [(abs_le.mp (hB₁ y)).2, le_max_left B₁ B₂])
  -- Berman's estimate
  obtain ⟨a, Λ, ha, hΛ, hBer⟩ := bermanSmoothEnvelopeStatement N Y A
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    simp only [hεdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set F : ℕ → Y → ℝ := fun k => smoothMin (ε k) f₁ f₂ with hFdef
  have hF : ∀ k, ChartSmooth (n := N) (F k) := fun k => chartSmooth_smoothMin (ε k) h₁ h₂
  have hFlo : ∀ k y, -B - 1 ≤ F k y := fun k y => by
    have := min_sub_le_smoothMin (hε k) f₁ f₂ y
    linarith [hminlo y, hε1 k]
  have hFup : ∀ k y, F k y ≤ B := fun k y =>
    (smoothMin_le (hε k) f₁ f₂ y).trans (hminup y)
  have hber := fun k => hBer (F k) (hF k) S hS0
    (smoothMin_ddc_line_le (hε k) A h₁ h₂ hS₁' hS₂') (-B - 1) (hFlo k)
  -- the envelopes of the smoothed minima converge uniformly
  have hsand := fun k => envelope_sandwich A.form (F := F k)
    (G := fun y => min (f₁ y) (f₂ y)) (c := ε k)
    (fun y => abs_smoothMin_sub_le (hε k) f₁ f₂ y) (hber k).1
  refine ⟨(hsand 0).1, (1 + S) * Λ * Real.exp (a * (B + (B + 1))), ?_⟩
  refine hasSmoothLineBoundApproximation_of_tendstoUniformly A
    (w := fun k => envelopeReal A.form (F k)) (fun k => (hber k).2) (fun k x => ?_) ?_
  · have h1S : 0 ≤ (1 + S) * Λ := by
      have : 0 ≤ 1 + S := by linarith
      positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ?_ ha)) h1S
    linarith [hFup k x]
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop k₀] with k hk x
    rw [Real.dist_eq]
    have h1 := (hsand k).2 x
    have h2 := one_div_succ_le_one_div_succ hk
    simp only [hεdef] at h1
    linarith

/-- **Source `prop:DR16_C11bar` (Darvas–Rubinstein), smooth obstacles.**  On a compact connected
complex manifold with a Kähler form `ω`, for chart-smooth `f₁, f₂` the envelope
`P_ω(min{f₁, f₂})` is real-valued and lies in `C^{1,1̄}(X)`: in every holomorphic chart its
distributional complex Hessian is locally bounded (`IsCOneOneBar`). -/
theorem isCOneOneBar_envelopeReal_min [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : ChartSmooth (n := N) f₁)
    (h₂ : ChartSmooth (n := N) f₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  obtain ⟨hreal, M, h⟩ := envelope_min_hasSmoothLineBoundApproximation A h₁ h₂
  exact ⟨hreal, isCOneOneBar_of_hasSmoothLineBoundApproximation A h fun _ => le_rfl⟩

end Main

end SGPT.Envelopes.DNTReg
