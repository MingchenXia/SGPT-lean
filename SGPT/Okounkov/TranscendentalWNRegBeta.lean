import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound
import SGPT.Foundations.Analysis.Pending.HessianLocalExtremum

/-!
# Berman's β-family of complex Monge–Ampère equations: existence and comparison

Package WN-REG of the Witt Nyström chapter (`claude-tok-wn-reg`, nodes `tok-wn-reg:beta-existence`,
`tok-wn-reg:beta-upper`, `tok-wn-reg:beta-lower`, `tok-wn-reg:beta-monotone`), the first step of
Berman's Laplacian estimate for envelopes (`tok-wn:berman`): R. Berman, *From Monge–Ampère
equations to envelopes and geodesic rays in the zero temperature limit*, Math. Z. 291 (2019),
arXiv:1307.3008v3 (`references/berman19-zero-temperature`), §2.1.2, equation (2.4) and
Proposition 2.3, and Lemmas 2.4 and 3.1.

Let `Y` be a compact connected complex manifold of dimension `N` with a Kähler background `A`
(a Kähler form; Berman's `ω`), `β > 0` and `F` chart-smooth.  A **β-solution** is a chart-smooth
`u` with `A + ddᶜu` Kähler and

`(A + ddᶜu)^N = e^{β(u - F)} A^N`   (chart densities; Berman's equation (2.4) with `dV = ω^n`).

* `exists_betaSolution` (Aubin–Yau, the "negative" case): a β-solution exists for every `β > 0`.
  It is TN's continuity method for Yau's theorem at `ε = 1`
  (`YauContinuityMethod.exists_smooth_of_mem_Icc`, with the uniform `C^{2,r}` estimate
  `YauHolderBound.exists_norm_ofChartSmooth_le`) applied to the Kähler background `βA` and the
  datum `-βF`, followed by the rescaling `u = φ/β`.
* `betaSolution_le_add` (upper bound of Prop. 2.3): if `ddᶜF ≤ S·A` on complex lines (`S ≥ 0`),
  then `u ≤ F + N log(1 + S)/β`.  Maximum principle at a maximum point of `u - F`.
* `le_betaSolution_of_subsolution` (lower bound of Prop. 2.3, smooth subsolutions): if `w` is
  chart-smooth with `A + ddᶜw ≥ δ·A` on complex lines (`δ > 0`) and `w ≤ F + η`, then
  `w - η + N log δ / β ≤ u`.  Maximum principle at a minimum point of `u - w`.
* `le_betaSolution_of_le` (Lemma 3.1, monotonicity and contraction of `P_β`): for β-solutions
  `u₁, u₂` of `F₁ ≤ F₂ + η`, `u₁ ≤ u₂ + η`; in particular β-solutions are unique.

All statements are for smooth data and smooth solutions; no envelope appears in this file.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A **β-solution** for the Kähler background `A`, the parameter `β` and the datum `F`
(Berman 2019, equation (2.4) with `dV = ω^n`): a chart-smooth `u` with `A + ddᶜu` Kähler and
`(A + ddᶜu)^N = e^{β(u - F)} A^N` in every chart. -/
structure BetaSolution (A : KahlerBackground N Y) (β : ℝ) (F : Y → ℝ) where
  /-- The solution. -/
  u : Y → ℝ
  /-- It is smooth in every holomorphic chart. -/
  smooth : ChartSmooth (n := N) u
  /-- `A + ddᶜu` is a Kähler form. -/
  isKahler : (A.form + ddcClosedForm u smooth).val.IsKahler
  /-- The Monge–Ampère equation `(A + ddᶜu)^N = e^{β(u - F)} A^N`, in chart densities. -/
  density : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
    actualTopPowerDensity ((A.form + ddcClosedForm u smooth).val.coeff e z) =
      Real.exp (β * (u (e.val.symm z) - F (e.val.symm z))) *
        actualTopPowerDensity (A.form.val.coeff e z)

/-! ### Pointwise tools -/

/-- At a local maximum the Levi form is nonpositive. -/
theorem leviForm_nonpos_of_isLocalMax {g : ComplexModel N → ℝ} {z : ComplexModel N}
    (hg : ContDiffAt ℝ 2 g z) (hmax : IsLocalMax g z) (v : ComplexModel N) :
    leviForm g z v ≤ 0 := by
  rw [leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv]
  have h1 := hmax.fderiv_fderiv_nonpos hg v
  have h2 := hmax.fderiv_fderiv_nonpos hg (Complex.I • v)
  linarith

/-- The Levi form of a difference. -/
theorem leviForm_sub' {f g : ComplexModel N → ℝ} {z : ComplexModel N}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v : ComplexModel N) :
    leviForm (fun w => f w - g w) z v = leviForm f z v - leviForm g z v := by
  have hfun : (fun w => f w - g w) = f + (-g) := by
    funext w; simp [sub_eq_add_neg]
  rw [hfun, leviForm_add (v := -g) hf hg.neg, leviForm_neg]
  ring

theorem contDiffAt_two_chart {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    ContDiffAt ℝ 2 (fun w => φ (e.val.symm w)) z :=
  ((hφ e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- `ddᶜφ` on a complex line is the Levi form of the chart representative, divided by `π`. -/
theorem ddc_line_eq {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    (ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] =
      leviForm (fun w => φ (e.val.symm w)) z v / Real.pi :=
  quad_ddcClosedForm_coeff hφ e hz v

/-- At a maximum point `y₀` of `f - g` (`f, g` chart-smooth), in the chart at `y₀`,
`ddᶜf ≤ ddᶜg` on every complex line. -/
theorem ddc_line_le_of_isMax {f g : Y → ℝ} (hf : ChartSmooth (n := N) f)
    (hg : ChartSmooth (n := N) g) {y₀ : Y} (hmax : ∀ y, f y - g y ≤ f y₀ - g y₀)
    (v : ComplexModel N) :
    (ddcClosedForm f hf).val.coeff (complexChartAt (n := N) y₀)
        ((complexChartAt (n := N) y₀).val y₀) ![v, Complex.I • v] ≤
      (ddcClosedForm g hg).val.coeff (complexChartAt (n := N) y₀)
        ((complexChartAt (n := N) y₀).val y₀) ![v, Complex.I • v] := by
  set e := complexChartAt (n := N) y₀
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  have hf2 := contDiffAt_two_chart hf e hz
  have hg2 := contDiffAt_two_chart hg e hz
  have hloc : IsLocalMax (fun w => f (e.val.symm w) - g (e.val.symm w)) (e.val y₀) :=
    Eventually.of_forall fun w => by
      change f (e.val.symm w) - g (e.val.symm w) ≤
        f (e.val.symm (e.val y₀)) - g (e.val.symm (e.val y₀))
      rw [e.val.left_inv hy]
      exact hmax _
  have h := leviForm_nonpos_of_isLocalMax (hf2.sub hg2) hloc v
  rw [leviForm_sub' hf2 hg2] at h
  rw [ddc_line_eq hf e hz, ddc_line_eq hg e hz]
  exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le

/-- The coefficient of `A + ddᶜu` on a line splits. -/
theorem add_ddc_line (A : KahlerBackground N Y) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    (e : ComplexChart N Y) (z : ComplexModel N) (v : ComplexModel N) :
    (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] =
      A.form.val.coeff e z ![v, Complex.I • v] +
        (ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] := by
  rw [ClosedRealOneOneForm.coeff_add]
  rfl

/-- A Kähler coefficient is semipositive on lines. -/
theorem coefficientSemipositive_of_isKahler {a : SmoothRealForm N Y 2} (ha : a.IsKahler)
    {e : ComplexChart N Y} {z : ComplexModel N} (hz : z ∈ e.val.target) :
    CoefficientSemipositive (a.coeff e z) := by
  intro v
  by_cases hv : v = 0
  · subst v
    rw [(a.coeff e z).map_coord_zero (0 : Fin 2) rfl]
  · exact ((ha.1 e z hz).2 v hv).le

/-- The density of a Kähler background is positive. -/
theorem density_pos (A : KahlerBackground N Y) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) : 0 < actualTopPowerDensity (A.form.val.coeff e z) :=
  YauContinuityMethod.actualTopPowerDensity_pos A hz

/-! ### Existence (Aubin–Yau) -/

/-- The coefficients of `A + ddᶜ(β⁻¹φ)` are `β⁻¹` times those of `βA + ddᶜφ`. -/
theorem coeff_add_ddc_inv_smul (A : KahlerBackground N Y) {β : ℝ} (hβ : 0 < β) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hu : ChartSmooth (n := N) (fun y => β⁻¹ * φ y))
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) :
    (A.form + ddcClosedForm (fun y => β⁻¹ * φ y) hu).val.coeff e z =
      β⁻¹ • ((KahlerBackground.smul hβ A).form + ddcClosedForm φ hφ).val.coeff e z := by
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
    ddcClosedForm_coeff, KahlerBackground.smul_form, ClosedRealOneOneForm.coeff_smul]
  have h := smoothDDC_smul e.val.open_target (hφ e) β⁻¹ hz
  simp only [smul_eq_mul] at h
  rw [h, smul_add, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]

/-- **Existence of β-solutions** (Aubin–Yau; Berman 2019, §2.1.2): on a compact connected
complex manifold with a Kähler background `A`, for every `β > 0` and chart-smooth `F` there is a
β-solution `u`: `A + ddᶜu` Kähler and `(A + ddᶜu)^N = e^{β(u - F)} A^N`. -/
theorem exists_betaSolution [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y)
    {β : ℝ} (hβ : 0 < β) {F : Y → ℝ} (hF : ChartSmooth (n := N) F) :
    Nonempty (BetaSolution A β F) := by
  obtain ⟨HA⟩ := HolderAtlas.nonempty (n := N) (M := Y)
  have hr0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ≥0) < 1 := by
    rw [← NNReal.coe_lt_coe]; norm_num
  set A' := KahlerBackground.smul hβ A with hA'
  have hF' : ChartSmooth (n := N) (fun y => -β * F y) := fun e => contDiffOn_const.mul (hF e)
  obtain ⟨φ, hφ, hK, hd⟩ := YauContinuityMethod.exists_smooth_of_mem_Icc A' HA hr0 hr1 hF'
    (YauHolderBound.exists_norm_ofChartSmooth_le A' HA hr0 hr1 hF') one_pos le_rfl
    (right_mem_Icc.2 zero_le_one)
  have hu : ChartSmooth (n := N) (fun y => β⁻¹ * φ y) := fun e => contDiffOn_const.mul (hφ e)
  have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
  refine ⟨⟨fun y => β⁻¹ * φ y, hu, ⟨fun e z hz => ?_, (A.form + ddcClosedForm _ hu).property.1⟩,
    fun e z hz => ?_⟩⟩
  · rw [coeff_add_ddc_inv_smul A hβ hφ hu e hz]
    exact ⟨isOneOne_smul _ (hK.1 e z hz).1, isStrictlyPositive_smul hβi (hK.1 e z hz).2⟩
  · rw [coeff_add_ddc_inv_smul A hβ hφ hu e hz, TopPowerDensityUpperBound.actualTopPowerDensity_smul,
      hd e z hz, hA', KahlerBackground.smul_form, ClosedRealOneOneForm.coeff_smul,
      TopPowerDensityUpperBound.actualTopPowerDensity_smul]
    have hexp : Real.exp (1 * (-β * F (e.val.symm z)) + 1 * φ (e.val.symm z)) =
        Real.exp (β * (β⁻¹ * φ (e.val.symm z) - F (e.val.symm z))) := by
      congr 1
      field_simp
      ring
    rw [hexp]
    have hpow : β⁻¹ ^ N * β ^ N = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hβ.ne', one_pow]
    calc β⁻¹ ^ N * (Real.exp (β * (β⁻¹ * φ (e.val.symm z) - F (e.val.symm z))) *
          (β ^ N * actualTopPowerDensity (A.form.val.coeff e z)))
        = (β⁻¹ ^ N * β ^ N) * (Real.exp (β * (β⁻¹ * φ (e.val.symm z) - F (e.val.symm z))) *
          actualTopPowerDensity (A.form.val.coeff e z)) := by ring
      _ = _ := by rw [hpow, one_mul]

/-! ### Comparison -/

section Comparison

variable [CompactSpace Y] {A : KahlerBackground N Y} {β : ℝ} {F : Y → ℝ}

/-- A chart-smooth function on a compact manifold attains its maximum. -/
theorem exists_isMax_of_chartSmooth [Nonempty Y] {g : Y → ℝ} (hg : ChartSmooth (n := N) g) :
    ∃ y₀, ∀ y, g y ≤ g y₀ := by
  obtain ⟨y₀, -, h⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (YauUniformEstimate.continuous_of_chartSmooth hg).continuousOn
  exact ⟨y₀, fun y => h (mem_univ y)⟩

/-- **Upper bound** (Berman 2019, Proposition 2.3, first step): if `ddᶜF ≤ S·A` on complex lines
with `S ≥ 0`, a β-solution satisfies `u ≤ F + N log(1 + S)/β`. -/
theorem betaSolution_le_add (hβ : 0 < β) (hF : ChartSmooth (n := N) F) {S : ℝ} (hS : 0 ≤ S)
    (hFS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    (U : BetaSolution A β F) (y : Y) :
    U.u y ≤ F y + N * Real.log (1 + S) / β := by
  have : Nonempty Y := ⟨y⟩
  have hg : ChartSmooth (n := N) (fun x => U.u x - F x) := fun e => (U.smooth e).sub (hF e)
  obtain ⟨y₀, hy₀⟩ := exists_isMax_of_chartSmooth hg
  set e := complexChartAt (n := N) y₀
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  have hle : ∀ v : ComplexModel N,
      (A.form + ddcClosedForm U.u U.smooth).val.coeff e (e.val y₀) ![v, Complex.I • v] ≤
        (1 + S) * A.form.val.coeff e (e.val y₀) ![v, Complex.I • v] := by
    intro v
    rw [add_ddc_line]
    have h1 := ddc_line_le_of_isMax U.smooth hF hy₀ v
    have h2 := hFS e (e.val y₀) hz v
    linarith
  have hdens := TopPowerDensityUpperBound.actualTopPowerDensity_le_pow_mul (k := N)
    (U.isKahler.1 e _ hz).1 (coefficientSemipositive_of_isKahler U.isKahler hz)
    (A.isKahler.1 e _ hz).1 hle
  rw [U.density e _ hz, e.val.left_inv hy] at hdens
  have hA0 := density_pos A hz
  have h1 : Real.exp (β * (U.u y₀ - F y₀)) ≤ (1 + S) ^ N := le_of_mul_le_mul_right hdens hA0
  have h1S : 0 < 1 + S := by linarith
  have h2 : β * (U.u y₀ - F y₀) ≤ N * Real.log (1 + S) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp, Real.log_pow] at this
  have h3 : U.u y - F y ≤ U.u y₀ - F y₀ := hy₀ y
  have h4 : U.u y₀ - F y₀ ≤ N * Real.log (1 + S) / β := by
    rw [le_div_iff₀ hβ]; linarith
  linarith

/-- **Lower bound by smooth subsolutions** (Berman 2019, Proposition 2.3, second step): if `w` is
chart-smooth with `A + ddᶜw ≥ δ·A` on complex lines (`δ > 0`) and `w ≤ F + η`, a β-solution
satisfies `w - η + N log δ / β ≤ u`. -/
theorem le_betaSolution_of_subsolution (hβ : 0 < β) {w : Y → ℝ} (hw : ChartSmooth (n := N) w)
    {δ η : ℝ} (hδ : 0 < δ)
    (hwδ : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, δ * A.form.val.coeff e z ![v, Complex.I • v] ≤
        (A.form + ddcClosedForm w hw).val.coeff e z ![v, Complex.I • v])
    (hwF : ∀ y, w y ≤ F y + η) (U : BetaSolution A β F) (y : Y) :
    w y - η + N * Real.log δ / β ≤ U.u y := by
  have : Nonempty Y := ⟨y⟩
  have hg : ChartSmooth (n := N) (fun x => w x - U.u x) := fun e => (hw e).sub (U.smooth e)
  obtain ⟨y₀, hy₀⟩ := exists_isMax_of_chartSmooth hg
  set e := complexChartAt (n := N) y₀
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  have hle : ∀ v : ComplexModel N,
      (δ • A.form.val.coeff e (e.val y₀)) ![v, Complex.I • v] ≤
        1 * (A.form + ddcClosedForm U.u U.smooth).val.coeff e (e.val y₀) ![v, Complex.I • v] := by
    intro v
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, one_mul, add_ddc_line]
    have h1 := ddc_line_le_of_isMax hw U.smooth hy₀ v
    have h2 := hwδ e (e.val y₀) hz v
    rw [add_ddc_line] at h2
    linarith
  have hδpos : CoefficientSemipositive (δ • A.form.val.coeff e (e.val y₀)) :=
    coefficientSemipositive_smul hδ.le (coefficientSemipositive_of_isKahler A.isKahler hz)
  have hdens := TopPowerDensityUpperBound.actualTopPowerDensity_le_pow_mul (k := N)
    (isOneOne_smul δ (A.isKahler.1 e _ hz).1) hδpos (U.isKahler.1 e _ hz).1 hle
  rw [TopPowerDensityUpperBound.actualTopPowerDensity_smul, one_pow, one_mul,
    U.density e _ hz, e.val.left_inv hy] at hdens
  have hA0 := density_pos A hz
  have h1 : δ ^ N ≤ Real.exp (β * (U.u y₀ - F y₀)) := le_of_mul_le_mul_right hdens hA0
  have h2 : N * Real.log δ ≤ β * (U.u y₀ - F y₀) := by
    have := Real.log_le_log (pow_pos hδ N) h1
    rwa [Real.log_exp, Real.log_pow] at this
  have h3 : N * Real.log δ / β ≤ U.u y₀ - F y₀ := by
    rw [div_le_iff₀ hβ]; linarith
  have h4 := hy₀ y
  have h5 := hwF y₀
  linarith

omit [CompactSpace Y] in
/-- `A + ddᶜ(c) = A` on lines. -/
theorem add_ddc_const_line (A : KahlerBackground N Y) (c : ℝ)
    (hc : ChartSmooth (n := N) (fun _ : Y => c)) (e : ComplexChart N Y) (z : ComplexModel N)
    (v : ComplexModel N) :
    (A.form + ddcClosedForm (fun _ : Y => c) hc).val.coeff e z ![v, Complex.I • v] =
      A.form.val.coeff e z ![v, Complex.I • v] := by
  rw [add_ddc_line, ddcClosedForm_coeff]
  have : smoothDDC (fun _ : ComplexModel N => c) z = 0 :=
    GlobalPotentialTransforms.smoothDDC_const c z
  rw [this]
  simp

/-- **Lower bound by the infimum**: `F ≥ c` everywhere forces `u ≥ c` everywhere. -/
theorem le_betaSolution_of_le (hβ : 0 < β) {c : ℝ} (hc : ∀ y, c ≤ F y)
    (U : BetaSolution A β F) (y : Y) : c ≤ U.u y := by
  have hcs : ChartSmooth (n := N) (fun _ : Y => c) := fun e => contDiffOn_const
  have h := le_betaSolution_of_subsolution hβ hcs (δ := 1) (η := 0) one_pos
    (fun e z _ v => by rw [add_ddc_const_line A c hcs e z v, one_mul])
    (fun y => by rw [add_zero]; exact hc y) U y
  simpa using h

/-- **Monotonicity and contraction** (Berman 2019, Lemma 3.1): β-solutions `u₁`, `u₂` of data
`F₁ ≤ F₂ + η` satisfy `u₁ ≤ u₂ + η`. -/
theorem betaSolution_le_of_le (hβ : 0 < β) {F₁ F₂ : Y → ℝ} {η : ℝ}
    (hF : ∀ y, F₁ y ≤ F₂ y + η) (U₁ : BetaSolution A β F₁) (U₂ : BetaSolution A β F₂) (y : Y) :
    U₁.u y ≤ U₂.u y + η := by
  have : Nonempty Y := ⟨y⟩
  have hg : ChartSmooth (n := N) (fun x => U₁.u x - U₂.u x) := fun e =>
    (U₁.smooth e).sub (U₂.smooth e)
  obtain ⟨y₀, hy₀⟩ := exists_isMax_of_chartSmooth hg
  set e := complexChartAt (n := N) y₀
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  have hle : ∀ v : ComplexModel N,
      (A.form + ddcClosedForm U₁.u U₁.smooth).val.coeff e (e.val y₀) ![v, Complex.I • v] ≤
        1 * (A.form + ddcClosedForm U₂.u U₂.smooth).val.coeff e (e.val y₀)
          ![v, Complex.I • v] := by
    intro v
    rw [one_mul, add_ddc_line, add_ddc_line]
    have h1 := ddc_line_le_of_isMax U₁.smooth U₂.smooth hy₀ v
    linarith
  have hdens := TopPowerDensityUpperBound.actualTopPowerDensity_le_pow_mul (k := N)
    (U₁.isKahler.1 e _ hz).1 (coefficientSemipositive_of_isKahler U₁.isKahler hz)
    (U₂.isKahler.1 e _ hz).1 hle
  rw [one_pow, one_mul, U₁.density e _ hz, U₂.density e _ hz, e.val.left_inv hy] at hdens
  have hA0 := density_pos A hz
  have h1 := le_of_mul_le_mul_right hdens hA0
  have h2 : β * (U₁.u y₀ - F₁ y₀) ≤ β * (U₂.u y₀ - F₂ y₀) := Real.exp_le_exp.mp h1
  have h3 : U₁.u y₀ - F₁ y₀ ≤ U₂.u y₀ - F₂ y₀ := le_of_mul_le_mul_left h2 hβ
  have h4 := hy₀ y
  have h5 := hF y₀
  linarith

/-- **Uniqueness** of β-solutions. -/
theorem betaSolution_u_eq (hβ : 0 < β) (U₁ U₂ : BetaSolution A β F) : U₁.u = U₂.u := by
  funext y
  apply le_antisymm
  · simpa using betaSolution_le_of_le hβ (η := 0) (fun y => by simp) U₁ U₂ y
  · simpa using betaSolution_le_of_le hβ (η := 0) (fun y => by simp) U₂ U₁ y

end Comparison

end SGPT.Okounkov.TranscendentalWNReg
