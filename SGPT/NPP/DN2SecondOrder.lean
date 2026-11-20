import SGPT.NPP.DN2StageTwo
import SGPT.NPP.DN2FirstOrder

/-!
# The second-order smoothing bound (FPT, `big-quadratic-smoothing-error`)

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, "A second-order smoothing
bound".  Under the hypotheses of `first_order_bound`, and if moreover `φ` is smooth off the analytic
set `Z` with `i∂∂̄φ ≤ C_φ ω` there (a divisorial Kähler current on a log resolution), there are
`δ₂ > 0`, `b₀ ≥ 0` such that, with `R₂(x) = b₀ (1 + B + |φ(x)|)`,

  `H_u(x, r) ≤ u(x) + R₂ e^{2R₂} r²`   for `x ∉ Z`, `0 < r ≤ δ₂ e^{-R₂(x)}`.

Proof (FPT): the Kiselman minimum `ψ` over `t ≤ δ e^{-2R(x)}` of `H_u(x, t) + t² - δ² log t`
(`stageTwo_logRadiusData`), the competitor `(1 - ν) Q + ν(1 + a)φ` with
`Q = ψ + δ² log δ - 2a₀δ²(1 + B) + aφ - Cδ²`, `a = 2a₀δ²` (`competitor_le_envelope` with
`κ = 1 + a`), evaluation at the minimizing radius and monotonicity in the radius.
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
  [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]


set_option maxHeartbeats 1000000 in
/-- **The second-order smoothing bound** (FPT `big-quadratic-smoothing-error`, pointwise form). -/
theorem second_order_bound {wY : KahlerBackground N Y} {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    (hJ : IsJointSmoothing wY r₀ Ψ) {θ : ClosedRealOneOneForm N Y}
    {f : Y → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) {B : ℝ} (hB0 : 0 ≤ B)
    (hfB : ∀ y, f y ≤ B)
    {Kf : ℝ} (hKf : 0 ≤ Kf) (hΨf : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ f x t ≤ f x + Kf * t ^ 2)
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    (hudef : u = rooftopEnvelope θ.val (fun y => (f y : EReal))) (hule : ∀ y, u y ≤ (f y : EReal))
    {K A C C₁ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 < C₁)
    (hge : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal))
    (hconv : ∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s)
    (himp : ∀ (x : Y) (a : ℝ), u x = (a : EReal) → ∀ L : ℝ, 0 ≤ L → ∀ r : ℝ, 0 < r →
        C₁ * r < r₀ → (∀ t : ℝ, 0 < t → t ≤ C₁ * r → correctedSmoothing Ψ u K x t ≤ a + L * t) →
        ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → e.val.symm z = x →
          ∀ w : ℂ, ‖w‖ = r →
            JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
              (A * logSlope (correctedSmoothing Ψ u K) x r + C * (1 + L) * r ^ 2)
              (C * (1 + L) * r) (C * (1 + L) * r))
    {φ : Y → EReal} (hφ : ThetaPlurisubharmonic (θ - wY.form).val φ)
    (hφθ : IsThetaPshPotential θ.val φ) (hφ0 : ∀ y, φ y ≤ 0)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := N) Z) (hZi : interior Z = ∅)
    (hφZ : ∀ y ∉ Z, φ y ≠ ⊥) (hφc : ContinuousOn (fun y => (φ y).toReal) Zᶜ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞ (fun z => (φ (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' Zᶜ))
    (hφL : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      e.val.symm z ∈ Zᶜ → ∀ v : ComplexModel N,
        leviForm (fun z => (φ (e.val.symm z)).toReal) z v ≤
          Cφ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v]))
    {δ₀ a₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ < r₀) (ha₀ : 1 ≤ a₀)
    (hfirst : ∀ x ∉ Z, ∀ r : ℝ, 0 < r → r ≤ δ₀ * Real.exp (-(a₀ * (1 + B + |(φ x).toReal|))) →
      correctedSmoothing Ψ u K x r ≤ (u x).toReal +
        (a₀ * (1 + B + |(φ x).toReal|)) * Real.exp (a₀ * (1 + B + |(φ x).toReal|)) * r) :
    ∃ δ₂ b₀ : ℝ, 0 < δ₂ ∧ 0 ≤ b₀ ∧ ∀ x ∉ Z, ∀ r : ℝ, 0 < r →
      r ≤ δ₂ * Real.exp (-(b₀ * (1 + B + |(φ x).toReal|))) →
      correctedSmoothing Ψ u K x r ≤ (u x).toReal +
        (b₀ * (1 + B + |(φ x).toReal|)) * Real.exp (2 * (b₀ * (1 + B + |(φ x).toReal|))) *
          r ^ 2 := by
  classical
  have hr₀ := hJ.r₀_pos
  have hZc : IsClosed Z := hZ.isClosed
  have ha₀0 : 0 ≤ a₀ := by linarith
  have hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh _
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  have hfint : Integrable f (kahlerVolume wY) :=
    SGPT.Envelopes.LapClass.integral_continuous hf (kahlerVolume wY)
  have hφu : ∀ y, φ y ≤ u y := by
    have := le_rooftopEnvelope hφθ (quasiEverywhere_of_forall (n := N)
      fun y => (hφ0 y).trans (EReal.coe_nonneg.mpr (hf0 y)))
    intro y; rw [hudef]; exact this y
  have hufin : ∀ y ∉ Z, u y = ((u y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hule y))
      (ne_bot_of_le_ne_bot (hφZ y hy) (hφu y))).symm
  have hφfin : ∀ y ∉ Z, φ y = ((φ y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top (hφ0 y)) (hφZ y hy)).symm
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
  set φr : Y → ℝ := fun y => (φ y).toReal with hφr
  have hφr0 : ∀ y, φr y ≤ 0 := fun y => EReal.toReal_nonpos (hφ0 y)
  have hφoff := thetaPshOff_toReal hZc hφ hφZ
  -- constants
  set δ₂ := min (min 1 (r₀ / 2)) (min (1 / (8 * C + 1)) (δ₀ / (C₁ + 1))) with hδ₂
  have hδ₂pos : 0 < δ₂ := lt_min (lt_min one_pos (by linarith)) (lt_min (by positivity)
    (by positivity))
  have hδ₂1 : δ₂ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂r : δ₂ < r₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hδ₂C : δ₂ ≤ 1 / (8 * C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₂C₁ : δ₂ ≤ δ₀ / (C₁ + 1) := (min_le_right _ _).trans (min_le_right _ _)
  set c₁ := (A + 2 * C + 4 * C ^ 2) / Real.pi + 2 * a₀ * Cφ + 1 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set b₀ := 4 * a₀ + c₁ * (1 + 2 * a₀) + K + Kf + 1 with hb₀
  have hb₀0 : 0 ≤ b₀ := by positivity
  refine ⟨δ₂, b₀, hδ₂pos, hb₀0, ?_⟩
  intro x hx r hr hrle
  set R₂ := b₀ * (1 + B + |φr x|) with hR₂
  have hR₂0 : 0 ≤ R₂ := by positivity
  set δ := r * Real.exp R₂ with hδdef
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ δ₂ := by
    rw [hδdef]
    have := mul_le_mul_of_nonneg_right hrle (Real.exp_pos R₂).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
  have hδ1 : δ ≤ 1 := hδle.trans hδ₂1
  have hδr : δ < r₀ := lt_of_le_of_lt hδle hδ₂r
  have hCδ : 8 * C * δ ≤ 1 := by
    have h1 : 8 * C * δ ≤ 8 * C * (1 / (8 * C + 1)) :=
      mul_le_mul_of_nonneg_left (hδle.trans hδ₂C) (by positivity)
    have h2 : 8 * C * (1 / (8 * C + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hC₁δ : C₁ * δ ≤ δ₀ := by
    have h1 : C₁ * δ ≤ C₁ * (δ₀ / (C₁ + 1)) :=
      mul_le_mul_of_nonneg_left (hδle.trans hδ₂C₁) hC₁.le
    have h2 : C₁ * (δ₀ / (C₁ + 1)) ≤ δ₀ := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  -- the Kiselman data
  have P := stageTwo_logRadiusData hJ θ hu hK hA hC hC₁ hge hconv himp hZc hloc hufin
    (φr := φr) (fun y _ => hφr0 y) hCφ hφs hφL hB0 ha₀0 hfirst hδpos hδr hCδ hC₁δ hδ₀r
  set β : Y → ℝ := fun y => Real.log δ - 2 * (a₀ * (1 + B)) + 2 * a₀ * φr y with hβ
  set e₂ := (A + 2 * C + 4 * C ^ 2) * δ ^ 2 / Real.pi with he₂
  set ψ := logRadiusInf (stageTwoF Ψ u K) β (δ ^ 2) with hψ
  have hψoff := P.thetaPshOff
  rw [compl_compl] at hψoff
  set a := 2 * a₀ * δ ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set E₂ := (K + Kf + 1) * δ ^ 2 with hE₂
  set k₀ := δ ^ 2 * Real.log δ - δ ^ 2 * (2 * (a₀ * (1 + B))) - E₂ with hk₀
  set Q : Y → ℝ := fun y => 1 * (ψ y + k₀) + a * φr y with hQ
  set C₀ := e₂ + δ ^ 2 * (2 * a₀ * Cφ) + δ ^ 2 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hQoff : ThetaPshOff ((1 + a) • θ + C₀ • wY.form).val Z (fun y => (Q y : EReal)) := by
    have h1 := thetaPshOff_combination hZc (thetaPshOff_add_const hψoff k₀) hφoff one_pos ha0
      (θ := (1 + a) • θ + (e₂ + δ ^ 2 * (2 * a₀ * Cφ) - a) • wY.form) (by module)
    have h2 := thetaPshOff_add_smul_kahler wY hZc h1 (b := a + δ ^ 2) (by positivity)
    have hform : (1 + a) • θ + (e₂ + δ ^ 2 * (2 * a₀ * Cφ) - a) • wY.form + (a + δ ^ 2) • wY.form =
        (1 + a) • θ + C₀ • wY.form := by rw [hC₀]; module
    rw [hform] at h2
    exact h2
  -- `Q ≤ f` off `Z`
  have hβle : ∀ y ∉ Z, β y ≤ Real.log δ := by
    intro y _
    have : 0 ≤ 2 * (a₀ * (1 + B)) - 2 * a₀ * φr y := by
      have := hφr0 y; nlinarith
    rw [hβ]; linarith
  have hQf : ∀ y ∉ Z, Q y ≤ f y := by
    intro y hy
    have h1 := P.logRadiusInf_le (x := y) hy (s := β y) le_rfl
    set ρ := Real.exp (β y) with hρ
    have hρpos : 0 < ρ := Real.exp_pos _
    have hρδ : ρ ≤ δ := by
      rw [hρ]; calc Real.exp (β y) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (hβle y hy)
        _ = δ := Real.exp_log hδpos
    have hmono : Ψ (fun y => (u y).toReal) y ρ ≤ Ψ f y ρ :=
      hJ.mono _ _ hint hfint (ae_of_all _ fun y => toReal_le_of_le_coe (hf0 y) (hule y)) y ρ
        hρpos (lt_of_le_of_lt hρδ hδr)
    have h2 := hΨf y ρ hρpos (lt_of_le_of_lt hρδ hδr)
    have hρ2 : ρ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hρpos.le hρδ 2
    have h3 : (K + Kf) * ρ ^ 2 ≤ (K + Kf) * δ ^ 2 :=
      mul_le_mul_of_nonneg_left hρ2 (by positivity)
    have hψy : ψ y ≤ Ψ (fun y => (u y).toReal) y ρ + K * ρ ^ 2 + ρ ^ 2 -
        δ ^ 2 * (Real.log δ - 2 * (a₀ * (1 + B)) + 2 * a₀ * φr y) := h1
    show 1 * (ψ y + k₀) + a * φr y ≤ f y
    rw [hk₀, hE₂, ha]
    linarith only [hψy, hmono, h2, h3, hρ2]
  -- the competitor
  have hκ : (1 : ℝ) ≤ 1 + a := by linarith
  have hcomp := competitor_le_envelope wY hf hf0 hφ hφ0 hZ hZi hφZ hκ hC₀pos hQoff hQf x hx
  rw [← hudef, hufin x hx, EReal.coe_le_coe_iff] at hcomp
  set ν := C₀ / (1 + a + C₀) with hν
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ C₀ := by
    rw [hν, div_le_iff₀ (by linarith)]
    have h1 := mul_pos hC₀pos ha0
    have h2 := mul_pos hC₀pos hC₀pos
    have h3 : C₀ * (1 + a + C₀) = C₀ + C₀ * a + C₀ * C₀ := by ring
    rw [h3]; linarith
  have hνc : C₀ ≤ c₁ * δ ^ 2 := le_of_eq (by rw [hC₀, he₂, hc₁]; ring)
  -- the minimizing radius
  obtain ⟨s₀, hs₀, -, hψeq, -⟩ := P.exists_isMinOn hx
  set t₀ := Real.exp s₀ with ht₀
  have ht₀pos : 0 < t₀ := Real.exp_pos _
  have hs₀' : s₀ ≤ Real.log δ := hs₀.trans (hβle x hx)
  have ht₀δ : t₀ ≤ δ := by
    rw [ht₀]; calc Real.exp s₀ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hs₀'
      _ = δ := Real.exp_log hδpos
  have hHge : (u x).toReal ≤ correctedSmoothing Ψ u K x t₀ := by
    have := hge x t₀ ht₀pos (lt_of_le_of_lt ht₀δ hδr)
    rw [hufin x hx, EReal.coe_le_coe_iff] at this
    exact this
  -- the algebra
  set ux := (u x).toReal with hux
  have huxB : ux ≤ B := (toReal_le_of_le_coe (hf0 x) (hule x)).trans (hfB x)
  set H₀ := correctedSmoothing Ψ u K x t₀ with hH₀
  set px := φr x with hpx
  have hpx0 : px ≤ 0 := hφr0 x
  have habs : |px| = -px := abs_of_nonpos hpx0
  have hQx : Q x = H₀ + t₀ ^ 2 - δ ^ 2 * s₀ + k₀ + a * px := by
    have hψx : ψ x = stageTwoF Ψ u K x (Real.exp s₀) - δ ^ 2 * s₀ := hψeq
    show 1 * (ψ x + k₀) + a * φr x = _
    rw [hψx]
    change 1 * ((H₀ + t₀ ^ 2) - δ ^ 2 * s₀ + k₀) + a * px = _
    ring
  have hQB : Q x ≤ B := (hQf x hx).trans (hfB x)
  have hκ0 : 0 < 1 + a := by linarith
  have hcomp' : (1 - ν) * Q x + ν * (1 + a) * px ≤ (1 + a) * ux := by
    have h := mul_le_mul_of_nonneg_left hcomp hκ0.le
    have hq : (1 + a) * ((1 - ν) / (1 + a)) = 1 - ν := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hκ0.ne'
    have h' : (1 + a) * ((1 - ν) / (1 + a) * Q x + ν * px) =
        (1 - ν) * Q x + ν * (1 + a) * px := by
      rw [mul_add, ← mul_assoc, hq]; ring
    linarith
  have hkey : Q x - ux ≤ a * B + ν * (1 + a) * |px| + ν * B := by
    have h1 : a * ux ≤ a * B := mul_le_mul_of_nonneg_left huxB ha0.le
    have h2 : ν * Q x ≤ ν * B := mul_le_mul_of_nonneg_left hQB hν0
    rw [habs]
    linarith only [hcomp', h1, h2]
  have hνκ : ν * (1 + a) ≤ c₁ * δ ^ 2 * (1 + 2 * a₀) := by
    have h1 : 1 + a ≤ 1 + 2 * a₀ := by
      have h0 : δ ^ 2 ≤ 1 := pow_le_one₀ hδpos.le hδ1
      have : 2 * a₀ * δ ^ 2 ≤ 2 * a₀ := mul_le_of_le_one_right (by positivity) h0
      rw [ha]; linarith only [this]
    have h2 : ν ≤ c₁ * δ ^ 2 := hν1.trans hνc
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  have hsum : (H₀ - ux) + δ ^ 2 * (Real.log δ - s₀) ≤ δ ^ 2 * R₂ := by
    have hνB : ν * B ≤ c₁ * δ ^ 2 * B := mul_le_mul_of_nonneg_right (hν1.trans hνc) hB0
    have hνp : ν * (1 + a) * |px| ≤ c₁ * δ ^ 2 * (1 + 2 * a₀) * |px| :=
      mul_le_mul_of_nonneg_right hνκ (abs_nonneg _)
    have hR₂exp : δ ^ 2 * R₂ = δ ^ 2 * b₀ * (1 + B + |px|) := by rw [hR₂]; ring
    have hc₁a : 0 ≤ c₁ * a₀ := mul_nonneg hc₁0 ha₀0
    have hb₀B : (4 * a₀ + c₁) * B ≤ b₀ * B := by
      apply mul_le_mul_of_nonneg_right _ hB0
      rw [hb₀]; linarith only [hc₁a, hK, hKf]
    have hb₀p : (c₁ * (1 + 2 * a₀) + 2 * a₀) * |px| ≤ b₀ * |px| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [hb₀]; linarith only [ha₀0, hK, hKf]
    have hb₀1 : 2 * a₀ + K + Kf + 1 ≤ b₀ := by
      rw [hb₀]; linarith only [hc₁a, hc₁0, ha₀0]
    have hd2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    have h3 := mul_le_mul_of_nonneg_left hb₀B hd2
    have h4 := mul_le_mul_of_nonneg_left hb₀p hd2
    have h5 := mul_le_mul_of_nonneg_left hb₀1 hd2
    have hkey' := hkey
    rw [hQx, hk₀, hE₂] at hkey'
    rw [habs] at hνp h4 hkey' hR₂exp
    rw [ha] at hkey' hνp
    rw [hR₂exp]
    linarith only [hkey', hνB, hνp, h3, h4, h5, sq_nonneg t₀]
  have hH0 : 0 ≤ H₀ - ux := by linarith
  have hlog0 : 0 ≤ δ ^ 2 * (Real.log δ - s₀) := mul_nonneg (sq_nonneg δ) (by
    have := Real.log_le_log ht₀pos ht₀δ; rw [ht₀, Real.log_exp] at this; linarith)
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hs₀R : Real.log δ - s₀ ≤ R₂ := by
    have : δ ^ 2 * (Real.log δ - s₀) ≤ δ ^ 2 * R₂ := by linarith
    exact le_of_mul_le_mul_left this hδ2pos
  have hrt₀ : r ≤ t₀ := by
    have h1 : Real.log δ - R₂ ≤ s₀ := by linarith
    have h2 : Real.exp (Real.log δ - R₂) = r := by
      rw [Real.exp_sub, Real.exp_log hδpos, hδdef, mul_div_assoc,
        div_self (Real.exp_pos R₂).ne', mul_one]
    rw [ht₀, ← h2]
    exact Real.exp_le_exp.mpr h1
  have hmono := correctedSmoothing_mono hJ hint hconv x hr hrt₀ (lt_of_le_of_lt ht₀δ hδr)
  have hfin : H₀ - ux ≤ δ ^ 2 * R₂ := by linarith
  calc correctedSmoothing Ψ u K x r ≤ H₀ := hmono
    _ ≤ ux + δ ^ 2 * R₂ := by linarith
    _ = ux + R₂ * Real.exp (2 * R₂) * r ^ 2 := by
      rw [hδdef, mul_pow, ← Real.exp_nat_mul]; push_cast; ring

end SGPT.NPP.DN2
