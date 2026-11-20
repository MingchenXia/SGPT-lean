import SGPT.NPP.DN2StageOne
import SGPT.NPP.DN2Competitor

/-!
# The first-order smoothing bound (FPT, `big-first-smoothing-error`)

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, "A first-order smoothing
bound".  On a compact Kähler manifold with a joint smoothing (`IsJointSmoothing`), for the envelope
`u = P_θ(f)` of a continuous obstacle `0 ≤ f ≤ B` and a Kähler current `θ + ddᶜφ ≥ ω`, `φ ≤ 0`,
finite and continuous off an analytic set `A` with empty interior, there are `δ₀ > 0`, `a₀ ≥ 0`
such that for `x ∉ A`, `R(x) = a₀ (1 + B + |φ(x)|)` and `0 < r ≤ δ₀ e^{-R(x)}`:

  `H_u(x, r) ≤ u(x) + R(x) e^{R(x)} r`.

The proof is FPT's: the Kiselman minimum `ψ_{δ,δ}` of `H_u(x, t) + t - δ log t` over `t ≤ δ`
(`stageOne_logRadiusData`), the competitor `(1 - ν)(ψ - Cδ²) + νφ` (`competitor_le_envelope`),
the evaluation at the minimizing radius `t₀`, and the monotonicity of `H_u` in the radius.

## Main results

* `obstacle_smoothing_le`: `Ψ_f ≤ f + K_f t²` from `psh` applied to `-f`.
* `thetaPshOff_add_const`, `thetaPshOff_add_smul_kahler`: shifts of potentials psh off `A`.
* `first_order_bound`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A smooth function with nonnegative Levi form on an open set is psh there. -/
theorem plurisubharmonicOn_of_levi_nonneg' {W : Set (ComplexModel N)} (hW : IsOpen W)
    {g : ComplexModel N → ℝ} (hg : ContDiffOn ℝ ∞ g W) (hL : ∀ z ∈ W, ∀ v, 0 ≤ leviForm g z v) :
    PlurisubharmonicOn (fun z => (g z : EReal)) W := by
  intro x hx
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hW x hx
  set r := ρ / 8 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall x (4 * r) ⊆ W :=
    (closedBall_subset_ball (by rw [hr]; linarith)).trans hball
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_eqOn_ball' hW hg hr0 (by linarith) hsub
  have hballW : ball x r ⊆ W := (ball_subset_ball (by linarith)).trans
    (ball_subset_closedBall.trans hsub)
  have hGL : ∀ y ∈ ball x r, ∀ v, 0 ≤ leviForm G y v := by
    intro y hy v
    have hloc : G =ᶠ[𝓝 y] g := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) hGeq
    rw [leviForm_congr' hloc]
    exact hL y (hballW hy) v
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr0, ?_⟩
  refine discPshOn_of_circleAverage_of_continuousOn (hg.continuousOn.mono hballW) ?_
  intro y v ρ' hρ' hD
  have h := le_circleAverage_of_levi_nonneg (hG.of_le two_le_infty) hGL hρ' hD
  have hy : G y = g y := hGeq (hD (center_mem_affineClosedDisc y v hρ'.le))
  have hcirc : Real.circleAverage (fun z : ℂ => G (y + z • v)) 0 ρ' =
      Real.circleAverage (fun z : ℂ => g (y + z • v)) 0 ρ' := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact hGeq (hD (mem_affineClosedDisc_of_norm_eq (by simpa [abs_of_pos hρ'] using hz)))
  rw [← hy, ← hcirc]
  exact h

/-- Adding a constant preserves `θ`-plurisubharmonicity off `A`. -/
theorem thetaPshOff_add_const {θ : ClosedRealOneOneForm N Y} {A : Set Y} {g : Y → ℝ}
    (hg : ThetaPshOff θ.val A (fun y => (g y : EReal))) (a : ℝ) :
    ThetaPshOff θ.val A (fun y => ((g y + a : ℝ) : EReal)) := by
  intro e z hz hzA
  obtain ⟨W, ρ, hzW, hp, hs⟩ := hg e z hz hzA
  refine ⟨W, ρ, hzW, hp, ?_⟩
  have hc : PlurisubharmonicOn (fun _ : ComplexModel N => ((a : ℝ) : EReal)) W :=
    fun x hx => ⟨W, hp.1, hx, discPshOn_const _ (EReal.coe_ne_top a) W⟩
  refine plurisubharmonicOn_congr_of_isOpen hp.1 (hs.add hc) fun y _ => ?_
  simp only [chartFunction]
  rw [EReal.coe_add, add_right_comm]

/-- Increasing the multiple of the Kähler form preserves psh-ness off `A`. -/
theorem thetaPshOff_add_smul_kahler (wY : KahlerBackground N Y) {θ : ClosedRealOneOneForm N Y}
    {A : Set Y} (hA : IsClosed A) {g : Y → ℝ}
    (hg : ThetaPshOff θ.val A (fun y => (g y : EReal))) {b : ℝ} (hb : 0 < b) :
    ThetaPshOff (θ + b • wY.form).val A (fun y => (g y : EReal)) := by
  have h0 : ThetaPshOff wY.form.val A (fun _ => ((0 : ℝ) : EReal)) := by
    intro e z hz _
    obtain ⟨W, ρ, hzW, hp⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials wY.form e z hz
    refine ⟨W, ρ, hzW, hp, ?_⟩
    have hpsh := plurisubharmonicOn_of_levi_nonneg' hp.1 hp.2.2.1 fun y hy v => by
      rw [leviForm_eq_pi_mul_coeff' hp hy]
      exact mul_nonneg Real.pi_pos.le (kahler_coeff_nonneg wY (hp.2.1 hy) v)
    refine plurisubharmonicOn_congr_of_isOpen hp.1 hpsh fun y _ => ?_
    simp [chartFunction]
  have := thetaPshOff_combination (θ₁ := θ) (θ₂ := wY.form) hA hg h0 one_pos hb
    (by rw [one_smul])
  simpa using this

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The obstacle error** (one-sided FPT `eq:chern-regular-obstacle-error`): if `-f` is a
`θ_f`-psh potential, then `Ψ_f ≤ f + K_f t²`. -/
theorem obstacle_smoothing_le {wY : KahlerBackground N Y} {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    (hJ : IsJointSmoothing wY r₀ Ψ) {θf : ClosedRealOneOneForm N Y} {f : Y → ℝ}
    (hf : IsThetaPshPotential θf.val (fun y => ((-f y : ℝ) : EReal))) :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ f x t ≤ f x + Kf * t ^ 2 := by
  obtain ⟨K, -, -, -, hK, -, -, -, hge, -⟩ := hJ.psh θf _ hf
  refine ⟨K, hK, fun x t ht htr => ?_⟩
  have h := hge x t ht htr
  simp only [correctedSmoothing, EReal.toReal_coe] at h
  rw [EReal.coe_le_coe_iff, hJ.neg f x t] at h
  linarith


/-- The smoothing of a potential along a fibre is smooth in the log radius. -/
theorem contDiffOn_fibre_smoothing {wY : KahlerBackground N Y} {r₀ : ℝ}
    {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ) {g : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (K : ℝ) (x : Y) :
    ContDiffOn ℝ ∞ (fun s => Ψ g x (Real.exp s) + K * Real.exp s ^ 2) (Iio (Real.log r₀)) := by
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hxe : e.val.symm (e.val x) = x := e.val.left_inv hx
  have hmaps : MapsTo (fun s : ℝ => ((e.val x, Real.exp s) : ComplexModel N × ℝ))
      (Iio (Real.log r₀)) (e.val.target ×ˢ Ioo 0 r₀) := by
    intro s hs
    refine ⟨e.val.map_source hx, Real.exp_pos _, ?_⟩
    calc Real.exp s < Real.exp (Real.log r₀) := Real.exp_lt_exp.mpr hs
      _ = r₀ := Real.exp_log hJ.r₀_pos
  have h := (hJ.contDiffOn g hg e).comp (contDiff_const.prodMk Real.contDiff_exp).contDiffOn hmaps
  have h' : ContDiffOn ℝ ∞ (fun s => Ψ g x (Real.exp s)) (Iio (Real.log r₀)) := by
    simpa only [Function.comp_def, hxe] using h
  exact h'.add (contDiffOn_const.mul (Real.contDiff_exp.pow 2).contDiffOn)

/-- **The corrected smoothing is nondecreasing in the radius.** -/
theorem correctedSmoothing_mono {wY : KahlerBackground N Y} {r₀ : ℝ}
    {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ) {u : Y → EReal}
    (hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY)) {K : ℝ}
    (hconv : ∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s)
    (x : Y) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) (ht : t < r₀) :
    correctedSmoothing Ψ u K x r ≤ correctedSmoothing Ψ u K x t := by
  have hsm := contDiffOn_fibre_smoothing hJ hint K x
  have hmono : MonotoneOn (fun s => correctedSmoothing Ψ u K x (Real.exp s)) (Iio (Real.log r₀)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iio _) hsm.continuousOn
      (fun s hs => ((hsm.contDiffAt (isOpen_Iio.mem_nhds
        (interior_subset hs : s ∈ Iio (Real.log r₀)))).differentiableAt
        (by simp)).differentiableWithinAt) fun s hs =>
          (hconv x s (interior_subset hs : s ∈ Iio (Real.log r₀))).1
  have htpos : 0 < t := lt_of_lt_of_le hr hrt
  have hlr : Real.log r < Real.log r₀ := Real.log_lt_log hr (lt_of_le_of_lt hrt ht)
  have hlt : Real.log t < Real.log r₀ := Real.log_lt_log htpos ht
  have := hmono hlr hlt (Real.log_le_log hr hrt)
  simpa only [Real.exp_log hr, Real.exp_log htpos] using this

theorem toReal_le_of_le_coe {a : EReal} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ (b : EReal)) :
    a.toReal ≤ b := by
  by_cases ha : a = ⊥
  · simp [ha, hb]
  · have := EReal.toReal_le_toReal h ha (EReal.coe_ne_top b)
    simpa using this

/-- **The first-order smoothing bound** (FPT `big-first-smoothing-error`). -/
theorem first_order_bound {wY : KahlerBackground N Y} {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    (hJ : IsJointSmoothing wY r₀ Ψ) {θ : ClosedRealOneOneForm N Y}
    {f : Y → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) {B : ℝ} (hB0 : 0 ≤ B)
    (hfB : ∀ y, f y ≤ B)
    {Kf : ℝ} (hKf : 0 ≤ Kf) (hΨf : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ f x t ≤ f x + Kf * t ^ 2)
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    (hudef : u = rooftopEnvelope θ.val (fun y => (f y : EReal))) (hule : ∀ y, u y ≤ (f y : EReal))
    {K A C : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hge : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal))
    (hconv : ∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s)
    (hlevi : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₀ →
          JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
            (A * logSlope (correctedSmoothing Ψ u K) (e.val.symm z) ‖w‖ + C * ‖w‖) C C)
    {φ : Y → EReal} (hφ : ThetaPlurisubharmonic (θ - wY.form).val φ)
    (hφθ : IsThetaPshPotential θ.val φ) (hφ0 : ∀ y, φ y ≤ 0)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := N) Z) (hZi : interior Z = ∅)
    (hφZ : ∀ y ∉ Z, φ y ≠ ⊥) (hφc : ContinuousOn (fun y => (φ y).toReal) Zᶜ) :
    ∃ δ₀ a₀ : ℝ, 0 < δ₀ ∧ δ₀ < r₀ ∧ 1 ≤ a₀ ∧ ∀ x ∉ Z, ∀ r : ℝ, 0 < r →
      r ≤ δ₀ * Real.exp (-(a₀ * (1 + B + |(φ x).toReal|))) →
      correctedSmoothing Ψ u K x r ≤ (u x).toReal +
        (a₀ * (1 + B + |(φ x).toReal|)) * Real.exp (a₀ * (1 + B + |(φ x).toReal|)) * r := by
  classical
  have hr₀ := hJ.r₀_pos
  have hZc : IsClosed Z := hZ.isClosed
  have hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh _
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  have hfint : Integrable f (kahlerVolume wY) :=
    SGPT.Envelopes.LapClass.integral_continuous hf (kahlerVolume wY)
  -- `φ ≤ u`
  have hφu : ∀ y, φ y ≤ u y := by
    have := le_rooftopEnvelope hφθ (quasiEverywhere_of_forall (n := N)
      fun y => (hφ0 y).trans (EReal.coe_nonneg.mpr (hf0 y)))
    intro y; rw [hudef]; exact this y
  have hufin : ∀ y ∉ Z, u y = ((u y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hule y))
      (ne_bot_of_le_ne_bot (hφZ y hy) (hφu y))).symm
  have hφfin : ∀ y ∉ Z, φ y = ((φ y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hφ0 y)) (hφZ y hy)).symm
  -- local lower bound of `u` off `Z`
  have hloc : ∀ x ∈ Zᶜ, ∃ V ∈ 𝓝 x, ∃ m : ℝ, ∀ y ∈ V, (m : EReal) ≤ u y := by
    intro x hx
    have hcx : ContinuousAt (fun y => (φ y).toReal) x :=
      hφc.continuousAt (hZc.isOpen_compl.mem_nhds hx)
    refine ⟨Zᶜ ∩ {y | (φ x).toReal - 1 < (φ y).toReal},
      inter_mem (hZc.isOpen_compl.mem_nhds hx)
        (hcx.eventually (lt_mem_nhds (by linarith : (φ x).toReal - 1 < (φ x).toReal))),
      (φ x).toReal - 1, fun y hy => ?_⟩
    calc (((φ x).toReal - 1 : ℝ) : EReal) ≤ (((φ y).toReal : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr hy.2.out.le
      _ = φ y := (hφfin y hy.1).symm
      _ ≤ u y := hφu y
  -- constants
  set δ₀ := min (r₀ / 2) (1 / (8 * C + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by linarith) (by positivity)
  have hδ₀r : δ₀ < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hCδ₀ : 8 * C * δ₀ ≤ 1 := by
    have h1 : δ₀ ≤ 1 / (8 * C + 1) := min_le_right _ _
    have h2 : 8 * C * δ₀ ≤ 8 * C * (1 / (8 * C + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 8 * C * (1 / (8 * C + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  set a₁ := (A + C + 2 * C ^ 2) / Real.pi + 1 with ha₁
  have ha₁0 : 0 ≤ a₁ := by positivity
  set a₀ := (K + Kf) * δ₀ + a₁ + 1 with ha₀
  have ha₀0 : 0 ≤ a₀ := by positivity
  have ha₀1 : 1 ≤ a₀ := by
    have : 0 ≤ (K + Kf) * δ₀ := by positivity
    rw [ha₀]; linarith
  refine ⟨δ₀, a₀, hδ₀pos, hδ₀r, ha₀1, ?_⟩
  intro x hx r hr hrle
  set φx := (φ x).toReal with hφx
  have hφx0 : φx ≤ 0 := EReal.toReal_nonpos (hφ0 x)
  set R := a₀ * (1 + B + |φx|) with hR
  have hR0 : 0 ≤ R := by positivity
  set δ := r * Real.exp R with hδdef
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ δ₀ := by
    rw [hδdef]
    have := mul_le_mul_of_nonneg_right hrle (Real.exp_pos R).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
  have hδr : δ < r₀ := lt_of_le_of_lt hδle hδ₀r
  have hCδ : 8 * C * δ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hδle (by positivity)) hCδ₀
  -- the Kiselman data and the minimum `ψ`
  have P := stageOne_logRadiusData (C₁ := 0) hJ θ hu hK hA hC hge hconv hlevi hZc.isOpen_compl hloc
    (c := δ) hδpos hδpos hδr hCδ
  set e := (A * δ + C * δ + 2 * C ^ 2 * δ) / Real.pi with he
  have he0 : 0 ≤ e := by positivity
  set ψ := logRadiusInf (stageOneF Ψ u K) (fun _ => Real.log δ) δ with hψ
  have hψoff := P.thetaPshOff
  rw [compl_compl] at hψoff
  set E := (K + Kf) * δ ^ 2 with hE
  set Q : Y → ℝ := fun y => ψ y + (-δ + δ * Real.log δ - E) with hQ
  have hQoff : ThetaPshOff ((1 : ℝ) • θ + (e + δ) • wY.form).val Z (fun y => (Q y : EReal)) := by
    have h1 := thetaPshOff_add_smul_kahler wY hZc
      (thetaPshOff_add_const hψoff (-δ + δ * Real.log δ - E)) hδpos
    have hform : θ + e • wY.form + (δ * 0) • wY.form + δ • wY.form =
        (1 : ℝ) • θ + (e + δ) • wY.form := by
      rw [mul_zero, zero_smul, add_zero, one_smul, add_smul, add_assoc]
    rw [hform] at h1
    exact h1
  -- `Q ≤ f` off `Z`
  have hQf : ∀ y ∉ Z, Q y ≤ f y := by
    intro y hy
    have h1 := P.logRadiusInf_le (x := y) hy (s := Real.log δ) le_rfl
    rw [Real.exp_log hδpos] at h1
    have hmono : Ψ (fun y => (u y).toReal) y δ ≤ Ψ f y δ :=
      hJ.mono _ _ hint hfint (ae_of_all _ fun y => toReal_le_of_le_coe (hf0 y) (hule y)) y δ
        hδpos hδr
    have h2 := hΨf y δ hδpos hδr
    simp only [hQ, hψ, stageOneF, correctedSmoothing] at h1 ⊢
    nlinarith
  -- the competitor
  have he' : 0 < e + δ := by linarith
  have hcomp := competitor_le_envelope wY hf hf0 hφ hφ0 hZ hZi hφZ (κ := 1) le_rfl he' hQoff hQf
    x hx
  rw [← hudef, hufin x hx, EReal.coe_le_coe_iff] at hcomp
  set ν := (e + δ) / (1 + (e + δ)) with hν
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ e + δ := by
    rw [hν, div_le_iff₀ (by linarith)]; nlinarith
  -- the minimizing radius
  obtain ⟨s₀, hs₀, -, hψeq, -⟩ := P.exists_isMinOn hx
  set t₀ := Real.exp s₀ with ht₀
  have ht₀pos : 0 < t₀ := Real.exp_pos _
  have ht₀δ : t₀ ≤ δ := by
    rw [ht₀]; calc Real.exp s₀ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hs₀
      _ = δ := Real.exp_log hδpos
  have hHge : (u x).toReal ≤ correctedSmoothing Ψ u K x t₀ := by
    have := hge x t₀ ht₀pos (lt_of_le_of_lt ht₀δ hδr)
    rw [hufin x hx, EReal.coe_le_coe_iff] at this
    exact this
  -- the algebra
  set ux := (u x).toReal with hux
  set H₀ := correctedSmoothing Ψ u K x t₀ with hH₀
  have hQx : Q x = H₀ + t₀ - δ * s₀ + (-δ + δ * Real.log δ - E) := by
    have hψx : ψ x = stageOneF Ψ u K x (Real.exp s₀) - δ * s₀ := hψeq
    show ψ x + (-δ + δ * Real.log δ - E) = _
    rw [hψx]
    rfl
  have hQB : Q x ≤ B := (hQf x hx).trans (hfB x)
  have hcomp' : (1 - ν) * Q x + ν * φx ≤ ux := by
    have : (1 - ν) / 1 = 1 - ν := div_one _
    rw [this] at hcomp
    exact hcomp
  have hkey : Q x - ux ≤ ν * (B - φx) := by
    have h1 : ν * Q x ≤ ν * B := mul_le_mul_of_nonneg_left hQB hν0
    linarith
  have hE' : E ≤ (K + Kf) * δ₀ * δ := by
    calc E = (K + Kf) * δ * δ := by rw [hE]; ring
      _ ≤ (K + Kf) * δ₀ * δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδle (by positivity)) hδpos.le
  have hνB : ν * (B - φx) ≤ δ * (a₁ * (B + |φx|)) := by
    have h1 : B - φx = B + |φx| := by rw [abs_of_nonpos hφx0]; ring
    have h2 : e + δ = δ * a₁ := by rw [he, ha₁]; field_simp
    rw [h1]
    have h3 : 0 ≤ B + |φx| := by positivity
    calc ν * (B + |φx|) ≤ (e + δ) * (B + |φx|) := mul_le_mul_of_nonneg_right hν1 h3
      _ = δ * (a₁ * (B + |φx|)) := by rw [h2]; ring
  have hsum : (H₀ - ux) + δ * (Real.log δ - s₀) ≤ δ * R := by
    have hRexp : (K + Kf) * δ₀ + a₁ * (B + |φx|) + 1 ≤ R := by
      rw [hR, ha₀]
      have h1 : 0 ≤ (K + Kf) * δ₀ := by positivity
      have h2 : 0 ≤ B + |φx| := by positivity
      have h3 : 0 ≤ (K + Kf) * δ₀ * (B + |φx|) := mul_nonneg h1 h2
      have h4 : 0 ≤ |φx| := abs_nonneg _
      linarith
    have := mul_le_mul_of_nonneg_left hRexp hδpos.le
    rw [hQx] at hkey
    linarith
  have hH0 : 0 ≤ H₀ - ux := by linarith
  have hlog0 : 0 ≤ δ * (Real.log δ - s₀) := mul_nonneg hδpos.le (by
    have := Real.log_le_log ht₀pos ht₀δ; rw [ht₀, Real.log_exp] at this; linarith)
  -- the radius bound `t₀ ≥ r`
  have hs₀R : Real.log δ - s₀ ≤ R := by
    have : δ * (Real.log δ - s₀) ≤ δ * R := by linarith
    exact le_of_mul_le_mul_left this hδpos
  have hrt₀ : r ≤ t₀ := by
    have h1 : Real.log δ - R ≤ s₀ := by linarith
    have h2 : Real.exp (Real.log δ - R) = r := by
      rw [Real.exp_sub, Real.exp_log hδpos, hδdef, mul_div_assoc, div_self (Real.exp_pos R).ne',
        mul_one]
    rw [ht₀, ← h2]
    exact Real.exp_le_exp.mpr h1
  have hmono := correctedSmoothing_mono hJ hint hconv x hr hrt₀ (lt_of_le_of_lt ht₀δ hδr)
  have hfin : H₀ - ux ≤ δ * R := by linarith
  calc correctedSmoothing Ψ u K x r ≤ H₀ := hmono
    _ ≤ ux + δ * R := by linarith
    _ = ux + R * Real.exp R * r := by rw [hδdef]; ring

end SGPT.NPP.DN2
