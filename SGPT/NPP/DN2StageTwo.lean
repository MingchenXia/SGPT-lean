import SGPT.NPP.DN2StageOne

/-!
# The second Kiselman minimum of the smoothing (FPT, second-order smoothing bound)

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, "Uniform joint estimates in
divisor coordinates" and "A second-order smoothing bound".  Working in the log radius `s = log t`
(`w = e^ζ`) the divisor coordinates `w = G(x) ξ` of FPT are not needed: with the varying end point

  `β(x) = log δ - 2R(x)`, `R(x) = a₀ (1 + B + |φ(x)|)`,

the improved joint estimate of the smoothing (valid at `x` because of the first-order bound
`H_u(x, t) ≤ u(x) + R e^R t`), whose constant is `M = C(1 + R e^R)`, satisfies `M t ≤ 2C δ` for
`t ≤ e^{β(x)} = δ e^{-2R}`; adding `K₂ t² = t²` absorbs the vertical and mixed terms, and the
minimum

  `ψ(x) = min_{t ≤ e^{β(x)}} (H_u(x, t) + t² - δ² log t)`

is `(θ + e₂ ω + δ² C_β ω)`-psh off the divisor, `e₂ = (A + 2C + 4C²) δ²/π`, `C_β = 2a₀ C_φ`, where
`i∂∂̄φ ≤ C_φ ω` off the divisor (`stageTwo_logRadiusData`).

## Main results

* `stageTwoF`: `F(x, t) = H_u(x, t) + t²`.
* `leviForm_exp_two_re`: the Levi form of `e^{2 Re ζ}`.
* `stageTwo_logRadiusData`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.IntegrationCurrent

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The profile of the second Kiselman minimum: `F(x, t) = H_u(x, t) + t²`. -/
def stageTwoF (Ψ : (Y → ℝ) → Y → ℝ → ℝ) (u : Y → EReal) (K : ℝ) : Y → ℝ → ℝ :=
  fun x t => correctedSmoothing Ψ u K x t + t ^ 2

/-- The Levi form of `(z, ζ) ↦ e^{2 Re ζ}`. -/
theorem leviForm_exp_two_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (x : E) (s : ℝ)
    (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => Real.exp (2 * p.2.re)) (x, (s : ℂ)) (v, η) =
      Real.exp (2 * s) * ‖η‖ ^ 2 := by
  have hf : ContDiffAt ℝ 2 (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) :=
    (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)).contDiff.contDiffAt
  have hθ : ContDiffAt ℝ 2 (fun t : ℝ => Real.exp (2 * t)) ((fun p : E × ℂ => p.2.re) (x, (s : ℂ))) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hc := SGPT.Foundations.Analysis.Pending.StokesCutoff.realHessian_comp
    (θ := fun t : ℝ => Real.exp (2 * t)) (f := fun p : E × ℂ => p.2.re) (z := (x, (s : ℂ))) hθ hf
  beta_reduce at hc
  have hL : ∀ a b : E × ℂ, realHessian (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) a b = 0 :=
    fun a b => realHessian_clm (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)) _ a b
  have hD : ∀ a : E × ℂ, fderiv ℝ (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) a = a.2.re := fun a => by
    rw [show (fun p : E × ℂ => p.2.re) =
      fun p => (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)) p from rfl,
      ContinuousLinearMap.fderiv]
    simp
  have hd1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t :=
    fun t => (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2 |>.congr_deriv
      (by simp))
  have hdd1 : deriv (fun t : ℝ => Real.exp (2 * t)) = fun t => Real.exp (2 * t) * 2 :=
    funext fun t => (hd1 t).deriv
  have hdd2 : deriv (deriv (fun t : ℝ => Real.exp (2 * t))) s = Real.exp (2 * s) * 2 * 2 := by
    rw [hdd1]
    exact ((hd1 s).mul_const 2).deriv
  unfold leviForm
  rw [hc, hc, hL, hL, hD, hD]
  simp only [Complex.ofReal_re, mul_zero, zero_add]
  rw [hdd2]
  simp only [Prod.smul_snd, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_sub]
  have hn : ‖η‖ ^ 2 = η.re * η.re + η.im * η.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hn]
  ring


variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem one_add_mul_exp_mul_exp_neg_two_le (R : ℝ) (hR : 0 ≤ R) :
    (1 + R * Real.exp R) * Real.exp (-(2 * R)) ≤ 2 := by
  have h1 : Real.exp (-(2 * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : R * Real.exp R * Real.exp (-(2 * R)) ≤ 1 := by
    rw [mul_assoc, ← Real.exp_add, show R + -(2 * R) = -R by ring]
    have h3 : R + 1 ≤ Real.exp R := Real.add_one_le_exp R
    have h4 : R * Real.exp (-R) ≤ Real.exp R * Real.exp (-R) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h4
    exact h4
  nlinarith

/-- **The hypotheses of the manifold Kiselman lemma for the second minimum.** -/
theorem stageTwo_logRadiusData {wY : KahlerBackground N Y} {r₀ : ℝ}
    {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ) (θ : ClosedRealOneOneForm N Y)
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) {K A C C₁ : ℝ} (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 < C₁)
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
    {Z : Set Y} (hZc : IsClosed Z)
    (hloc : ∀ x ∈ Zᶜ, ∃ V ∈ 𝓝 x, ∃ m : ℝ, ∀ y ∈ V, (m : EReal) ≤ u y)
    (hufin : ∀ x ∉ Z, u x = ((u x).toReal : EReal))
    {φr : Y → ℝ} (hφ0 : ∀ x ∉ Z, φr x ≤ 0) {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞ (fun z => φr (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' Zᶜ))
    (hφL : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      e.val.symm z ∈ Zᶜ → ∀ v : ComplexModel N,
        leviForm (fun z => φr (e.val.symm z)) z v ≤
          Cφ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v]))
    {B δ₀ a₀ : ℝ} (hB : 0 ≤ B) (ha₀ : 0 ≤ a₀)
    (hfirst : ∀ x ∉ Z, ∀ r : ℝ, 0 < r → r ≤ δ₀ * Real.exp (-(a₀ * (1 + B + |φr x|))) →
      correctedSmoothing Ψ u K x r ≤ (u x).toReal +
        (a₀ * (1 + B + |φr x|)) * Real.exp (a₀ * (1 + B + |φr x|)) * r)
    {δ : ℝ} (hδ : 0 < δ) (hδr : δ < r₀) (hCδ : 8 * C * δ ≤ 1) (hC₁δ : C₁ * δ ≤ δ₀)
    (hδ₀r : δ₀ < r₀) :
    LogRadiusData wY (θ + ((A + 2 * C + 4 * C ^ 2) * δ ^ 2 / Real.pi) • wY.form) Zᶜ
      (stageTwoF Ψ u K) r₀
      (fun x => Real.log δ - 2 * (a₀ * (1 + B)) + 2 * a₀ * φr x) (δ ^ 2) (2 * a₀ * Cφ) := by
  have hr₀ : 0 < r₀ := hJ.r₀_pos
  have hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh _
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  set H := correctedSmoothing Ψ u K with hHdef
  set β : Y → ℝ := fun x => Real.log δ - 2 * (a₀ * (1 + B)) + 2 * a₀ * φr x with hβ
  -- on the complement of `Z`, `β = log δ - 2R`
  have hβR : ∀ x ∉ Z, β x = Real.log δ - 2 * (a₀ * (1 + B + |φr x|)) := by
    intro x hx
    rw [hβ, abs_of_nonpos (hφ0 x hx)]; ring
  have hRnn : ∀ x, 0 ≤ a₀ * (1 + B + |φr x|) := fun x => by positivity
  have hβlt : ∀ x ∉ Z, β x ≤ Real.log δ := by
    intro x hx; rw [hβR x hx]; linarith [hRnn x]
  have hlogδ : Real.log δ < Real.log r₀ := Real.log_lt_log hδ hδr
  -- chart smoothness of `H`
  have hHs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞
      (fun p : ComplexModel N × ℝ => H (e.val.symm p.1) p.2) (e.val.target ×ˢ Ioo 0 r₀) := by
    intro e
    have h1 := hJ.contDiffOn _ hint e
    exact h1.add (contDiffOn_const.mul (contDiff_snd.pow 2).contDiffOn)
  have hFs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞
      (fun p : ComplexModel N × ℝ => stageTwoF Ψ u K (e.val.symm p.1) p.2)
      (e.val.target ×ˢ Ioo 0 r₀) := fun e => (hHs e).add (contDiff_snd.pow 2).contDiffOn
  have hfib : ∀ x : Y, ContDiffOn ℝ ∞ (fun s => H x (Real.exp s)) (Iio (Real.log r₀)) := by
    intro x
    set e := complexChartAt (n := N) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    have hxe : e.val.symm (e.val x) = x := e.val.left_inv hx
    have hmaps : MapsTo (fun s : ℝ => ((e.val x, Real.exp s) : ComplexModel N × ℝ))
        (Iio (Real.log r₀)) (e.val.target ×ˢ Ioo 0 r₀) := by
      intro s hs
      refine ⟨e.val.map_source hx, Real.exp_pos _, ?_⟩
      calc Real.exp s < Real.exp (Real.log r₀) := Real.exp_lt_exp.mpr hs
        _ = r₀ := Real.exp_log hr₀
    have h := (hHs e).comp (contDiff_const.prodMk Real.contDiff_exp).contDiffOn hmaps
    simpa only [Function.comp_def, hxe] using h
  have hexp2 : ∀ s : ℝ, HasDerivAt (fun s => Real.exp s ^ 2) (2 * Real.exp s ^ 2) s := by
    intro s
    have h := (Real.hasDerivAt_exp s).mul (Real.hasDerivAt_exp s)
    have e1 : (fun y => Real.exp y ^ 2) = fun y => Real.exp y * Real.exp y := by
      funext y; ring
    rw [e1, show 2 * Real.exp s ^ 2 = Real.exp s * Real.exp s + Real.exp s * Real.exp s by ring]
    exact h
  have hderivF : ∀ x : Y, ∀ s < Real.log r₀,
      deriv (fun s => stageTwoF Ψ u K x (Real.exp s)) s =
        deriv (fun s => H x (Real.exp s)) s + 2 * Real.exp s ^ 2 := by
    intro x s hs
    have hd : DifferentiableAt ℝ (fun s => H x (Real.exp s)) s :=
      ((hfib x).contDiffAt (isOpen_Iio.mem_nhds hs)).differentiableAt (by simp)
    exact (hd.hasDerivAt.add (hexp2 s)).deriv
  have hderiv2F : ∀ x : Y, ∀ s < Real.log r₀,
      deriv (deriv (fun s => stageTwoF Ψ u K x (Real.exp s))) s =
        deriv (deriv (fun s => H x (Real.exp s))) s + 4 * Real.exp s ^ 2 := by
    intro x s hs
    have hev : deriv (fun s => stageTwoF Ψ u K x (Real.exp s)) =ᶠ[𝓝 s]
        fun s => deriv (fun s => H x (Real.exp s)) s + 2 * Real.exp s ^ 2 := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
      exact hderivF x t ht
    have hd2c : ContDiffOn ℝ ∞ (deriv fun s => H x (Real.exp s)) (Iio (Real.log r₀)) :=
      (hfib x).deriv_of_isOpen isOpen_Iio (by simp)
    have hd2 : DifferentiableAt ℝ (deriv fun s => H x (Real.exp s)) s :=
      (hd2c.contDiffAt (isOpen_Iio.mem_nhds hs)).differentiableAt (by simp)
    rw [hev.deriv_eq]
    have h3 : HasDerivAt (fun s => deriv (fun s => H x (Real.exp s)) s + 2 * Real.exp s ^ 2)
        (deriv (deriv fun s => H x (Real.exp s)) s + 2 * (2 * Real.exp s ^ 2)) s :=
      hd2.hasDerivAt.add ((hexp2 s).const_mul 2)
    rw [h3.deriv]; ring
  have hβs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞ (fun z => β (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' Zᶜ) := fun e =>
    contDiffOn_const.add (contDiffOn_const.mul (hφs e))
  refine ⟨hZc.isOpen_compl, hr₀, by positivity, by positivity, hFs,
    fun x hx => lt_of_le_of_lt (hβlt x hx) hlogδ, hβs, ?_, ?_, ?_, ?_, ?_⟩
  · -- the curvature of the end point
    intro e z hz hzU v
    have hφ2 : ContDiffAt ℝ 2 (fun z => φr (e.val.symm z)) z :=
      (((hφs e).contDiffAt (((e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target
        hZc.isOpen_compl)).mem_nhds ⟨hz, hzU⟩)).of_le two_le_infty)
    have h1 : leviForm (fun z => β (e.val.symm z)) z v =
        2 * a₀ * leviForm (fun z => φr (e.val.symm z)) z v := by
      have hfun : (fun z => β (e.val.symm z)) = (fun _ => Real.log δ - 2 * (a₀ * (1 + B))) +
          (fun z => (2 * a₀) • φr (e.val.symm z)) := by
        funext z; simp [hβ]
      have h0 : ContDiffAt ℝ 2 (fun _ : ComplexModel N => Real.log δ - 2 * (a₀ * (1 + B))) z :=
        contDiffAt_const
      have hc2 : ContDiffAt ℝ 2 (fun z => (2 * a₀) • φr (e.val.symm z)) z := hφ2.const_smul _
      rw [hfun, leviForm_add h0 hc2, leviForm_const, zero_add,
        show (fun z => (2 * a₀) • φr (e.val.symm z)) = (2 * a₀) • (fun z => φr (e.val.symm z))
          from rfl, leviForm_smul hφ2]
    rw [h1]
    have := mul_le_mul_of_nonneg_left (hφL e z hz hzU v) (by positivity : 0 ≤ 2 * a₀)
    linarith
  · intro x hx s hs
    rw [hderivF x s (lt_of_le_of_lt (hs.trans (hβlt x hx)) hlogδ)]
    have := (hconv x s (lt_of_le_of_lt (hs.trans (hβlt x hx)) hlogδ)).1
    positivity
  · intro x hx s hs
    rw [hderiv2F x s (lt_of_le_of_lt (hs.trans (hβlt x hx)) hlogδ)]
    have := (hconv x s (lt_of_le_of_lt (hs.trans (hβlt x hx)) hlogδ)).2
    positivity
  · intro x hx
    obtain ⟨V, hV, m, hm⟩ := hloc x hx
    refine ⟨V, hV, m, fun y hy hyU s hs => ?_⟩
    have ht : Real.exp s < r₀ := by
      calc Real.exp s ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (hs.trans (hβlt y hyU))
        _ = δ := Real.exp_log hδ
        _ < r₀ := hδr
    have h1 := (hm y hy).trans (hge y (Real.exp s) (Real.exp_pos s) ht)
    rw [EReal.coe_le_coe_iff] at h1
    show m ≤ H y (Real.exp s) + Real.exp s ^ 2
    nlinarith [Real.exp_pos s]
  · -- the joint Levi form
    intro e z hz hzU s hs hslope W ρ hzW hρ v η
    set x := e.val.symm z with hx
    have hxZ : x ∉ Z := hzU
    set R := a₀ * (1 + B + |φr x|) with hR
    have hR0 : 0 ≤ R := hRnn x
    set r := Real.exp s with hr
    have hrpos : 0 < r := Real.exp_pos s
    have hrβ : r ≤ δ * Real.exp (-(2 * R)) := by
      rw [hr]
      calc Real.exp s ≤ Real.exp (β x) := Real.exp_le_exp.mpr hs
        _ = δ * Real.exp (-(2 * R)) := by
          rw [hβR x hxZ, sub_eq_add_neg, Real.exp_add, Real.exp_log hδ]
    have hexpR1 : Real.exp (-(2 * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hrδ : r ≤ δ := hrβ.trans (by nlinarith)
    have hsr : s < Real.log r₀ := lt_of_le_of_lt (hs.trans (hβlt x hxZ)) hlogδ
    have hHd : DifferentiableAt ℝ (H x) r := by
      have hmaps : MapsTo (fun t : ℝ => ((z, t) : ComplexModel N × ℝ)) (Ioo 0 r₀)
          (e.val.target ×ˢ Ioo 0 r₀) := fun t ht => ⟨hz, ht⟩
      have h := (hHs e).comp (contDiff_const.prodMk contDiff_id).contDiffOn hmaps
      exact ((h.contDiffAt (isOpen_Ioo.mem_nhds ⟨hrpos, lt_of_le_of_lt hrδ hδr⟩)).differentiableAt
        (by simp))
    have hlam : logSlope H x r ≤ δ ^ 2 := by
      have h1 := hderivF x s hsr
      rw [deriv_comp_exp_eq_logSlope hHd] at h1
      have : 0 ≤ 2 * Real.exp s ^ 2 := by positivity
      linarith
    -- the improved estimate at `x`
    set L := R * Real.exp R with hL
    have hL0 : 0 ≤ L := by positivity
    have hC₁r : C₁ * r ≤ δ₀ * Real.exp (-R) := by
      have h1 : C₁ * r ≤ C₁ * (δ * Real.exp (-(2 * R))) := mul_le_mul_of_nonneg_left hrβ hC₁.le
      have h2 : Real.exp (-(2 * R)) ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
      have h3 : C₁ * δ * Real.exp (-(2 * R)) ≤ δ₀ * Real.exp (-R) :=
        mul_le_mul hC₁δ h2 (Real.exp_pos _).le (le_trans (by positivity) hC₁δ)
      nlinarith
    have hC₁r₀ : C₁ * r < r₀ := by
      have : δ₀ * Real.exp (-R) ≤ δ₀ := by
        have h1 : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have h2 : 0 ≤ δ₀ := le_trans (by positivity) hC₁δ
        nlinarith
      linarith
    have hlin : ∀ t : ℝ, 0 < t → t ≤ C₁ * r → H x t ≤ (u x).toReal + L * t := by
      intro t ht htle
      have := hfirst x hxZ t ht (htle.trans hC₁r)
      rw [← hR] at this
      linarith
    obtain ⟨W', ρθ, hzW', hρθ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
    have hwn : ‖Complex.exp (s : ℂ)‖ = r := Complex.norm_exp_ofReal s
    have hI := himp x (u x).toReal (hufin x hxZ) L hL0 r hrpos hC₁r₀ hlin e z hz rfl
      (Complex.exp (s : ℂ)) hwn W' ρθ hzW' hρθ v (Complex.exp (s : ℂ) * η)
    rw [norm_mul, hwn] at hI
    -- the three pieces
    set g₁ : ComplexModel N × ℂ → ℝ := fun p => chartJoint H e ρθ (p.1, Complex.exp p.2)
    set g₂ : ComplexModel N × ℂ → ℝ := fun p => Real.exp (2 * p.2.re)
    set g₃ : ComplexModel N × ℂ → ℝ := fun p => ρ p.1 - ρθ p.1
    have hsplit : (fun p : ComplexModel N × ℂ =>
        stageTwoF Ψ u K (e.val.symm p.1) (Real.exp p.2.re) + ρ p.1) = g₁ + g₂ + g₃ := by
      funext p
      simp only [stageTwoF, Pi.add_apply, g₁, g₂, g₃, chartJoint, Complex.norm_exp]
      rw [← Real.exp_nat_mul]
      push_cast
      ring
    set p₀ : ComplexModel N × ℂ := (z, (s : ℂ))
    have hJs : ContDiffAt ℝ ∞ (chartJoint H e ρθ) (z, Complex.exp (s : ℂ)) := by
      have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) (Complex.exp (s : ℂ)) :=
        contDiffAt_norm ℝ (Complex.exp_ne_zero _)
      have hmem : ((z, ‖Complex.exp (s : ℂ)‖) : ComplexModel N × ℝ) ∈
          e.val.target ×ˢ Ioo 0 r₀ := by
        refine ⟨hz, ?_, ?_⟩ <;> rw [hwn] <;> [exact hrpos; exact lt_of_le_of_lt hrδ hδr]
      have h1 : ContDiffAt ℝ ∞ (fun p : ComplexModel N × ℝ => H (e.val.symm p.1) p.2)
          (z, ‖Complex.exp (s : ℂ)‖) :=
        (hHs e).contDiffAt (((e.val.open_target).prod isOpen_Ioo).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℂ => ((q.1, ‖q.2‖) : ComplexModel N × ℝ))
          (z, Complex.exp (s : ℂ)) :=
        contDiffAt_fst.prodMk (hn.comp (z, Complex.exp (s : ℂ)) contDiffAt_snd)
      have h3 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℂ => ρθ q.1) (z, Complex.exp (s : ℂ)) :=
        (hρθ.2.2.1.contDiffAt (hρθ.1.mem_nhds hzW')).comp _ contDiffAt_fst
      exact (h1.comp (z, Complex.exp (s : ℂ)) h2).add h3
    have hg₁ : ContDiffAt ℝ 2 g₁ p₀ := by
      have hΦ : ContDiffAt ℝ ∞ (fun p : ComplexModel N × ℂ => ((p.1, Complex.exp p.2) :
          ComplexModel N × ℂ)) p₀ :=
        (contDiffAt_fst.prodMk ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp _
          contDiffAt_snd))
      exact (hJs.comp p₀ hΦ).of_le two_le_infty
    have hg₂ : ContDiffAt ℝ 2 g₂ p₀ :=
      ((Real.contDiff_exp.comp (contDiff_const.mul (Complex.reCLM.comp
        (ContinuousLinearMap.snd ℝ (ComplexModel N) ℂ)).contDiff)).contDiffAt).of_le two_le_infty
    have hρz : ContDiffAt ℝ ∞ ρ z := hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hzW)
    have hρθz : ContDiffAt ℝ ∞ ρθ z := hρθ.2.2.1.contDiffAt (hρθ.1.mem_nhds hzW')
    have hg₃ : ContDiffAt ℝ 2 g₃ p₀ :=
      ((hρz.sub hρθz).comp p₀ contDiffAt_fst).of_le two_le_infty
    have h12 : ContDiffAt ℝ 2 (g₁ + g₂) p₀ := hg₁.add hg₂
    rw [hsplit, leviForm_add h12 hg₃, leviForm_add hg₁ hg₂]
    have hL1 : leviForm g₁ p₀ (v, η) = leviForm (chartJoint H e ρθ) (z, Complex.exp (s : ℂ))
        (v, Complex.exp (s : ℂ) * η) :=
      leviForm_comp_expProd (hJs.of_le two_le_infty) v η
    have hL2 : leviForm g₂ p₀ (v, η) = r ^ 2 * ‖η‖ ^ 2 := by
      rw [leviForm_exp_two_re z s v η, hr, ← Real.exp_nat_mul]; push_cast; ring_nf
    have hL3 : leviForm g₃ p₀ (v, η) =
        Real.pi * ((A + 2 * C + 4 * C ^ 2) * δ ^ 2 / Real.pi) * chartNormSq wY e z v := by
      have h := realHessian_comp_clm (ContinuousLinearMap.fst ℝ (ComplexModel N) ℂ)
        (u := fun y => ρ y - ρθ y) (p := p₀) ((hρz.sub hρθz).of_le two_le_infty)
      have hdiff : leviForm (fun y => ρ y - ρθ y) z v = leviForm ρ z v - leviForm ρθ z v := by
        have h1 : (fun y => ρ y - ρθ y) = ρ + (fun x => -ρθ x) := by
          funext y; simp [sub_eq_add_neg]
        rw [h1, leviForm_add (hρz.of_le two_le_infty) ((hρθz.neg).of_le two_le_infty),
          show (fun x => -ρθ x) = -ρθ from rfl, leviForm_neg]
        ring
      have h3 : leviForm g₃ p₀ (v, η) = leviForm (fun y => ρ y - ρθ y) z v := by
        unfold leviForm
        rw [show g₃ = fun q => (fun y => ρ y - ρθ y)
          ((ContinuousLinearMap.fst ℝ (ComplexModel N) ℂ) q) from rfl, h, h]
        simp [p₀, Prod.smul_mk]
      rw [h3, hdiff, leviForm_eq_pi_mul_coeff' hρ hzW, leviForm_eq_pi_mul_coeff' hρθ hzW']
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
        ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
        chartNormSq]
      ring
    have hpi : Real.pi * ((A + 2 * C + 4 * C ^ 2) * δ ^ 2 / Real.pi) =
        (A + 2 * C + 4 * C ^ 2) * δ ^ 2 := by field_simp
    rw [hL2, hL3, hpi, hL1]
    -- the algebra
    set N2 := chartNormSq wY e z v with hN2def
    have hN2 : 0 ≤ N2 := kahler_coeff_nonneg wY hz v
    set nn := Real.sqrt N2 with hnn
    have hnn2 : nn * nn = N2 := Real.mul_self_sqrt hN2
    have hnn0 : 0 ≤ nn := Real.sqrt_nonneg _
    set x' := ‖η‖ with hx'
    have hx0 : 0 ≤ x' := norm_nonneg _
    set lam := logSlope H x r with hlamdef
    set P := C * (1 + L) * r with hP
    have hP0 : 0 ≤ P := by positivity
    have h1Lr : (1 + L) * r ≤ 2 * δ := by
      have h1 := mul_le_mul_of_nonneg_left hrβ (by positivity : (0 : ℝ) ≤ 1 + L)
      have h2 := one_add_mul_exp_mul_exp_neg_two_le R hR0
      calc (1 + L) * r ≤ (1 + L) * (δ * Real.exp (-(2 * R))) := h1
        _ = δ * ((1 + R * Real.exp R) * Real.exp (-(2 * R))) := by rw [hL]; ring
        _ ≤ δ * 2 := mul_le_mul_of_nonneg_left h2 hδ.le
        _ = 2 * δ := by ring
    have hPδ : P ≤ 2 * C * δ := by
      calc P = C * ((1 + L) * r) := by rw [hP]; ring
        _ ≤ C * (2 * δ) := mul_le_mul_of_nonneg_left h1Lr hC
        _ = 2 * C * δ := by ring
    have hP14 : P ≤ 1 / 4 := by linarith
    have hyoung : P * nn * (r * x') ≤ (r * x') ^ 2 / 4 + P ^ 2 * N2 := by
      have h1 := sq_nonneg (r * x' / 2 - P * nn)
      have h2 : (r * x' / 2 - P * nn) ^ 2 = (r * x') ^ 2 / 4 - P * nn * (r * x') +
          P ^ 2 * (nn * nn) := by ring
      rw [h2, hnn2] at h1
      linarith
    have hvert : P * (r * x') ^ 2 ≤ (r * x') ^ 2 / 4 := by
      have := mul_le_mul_of_nonneg_right hP14 (sq_nonneg (r * x'))
      linarith
    have hP2 : P ^ 2 ≤ 4 * C ^ 2 * δ ^ 2 := by
      have := pow_le_pow_left₀ hP0 hPδ 2
      calc P ^ 2 ≤ (2 * C * δ) ^ 2 := this
        _ = 4 * C ^ 2 * δ ^ 2 := by ring
    have hPr : C * (1 + L) * r ^ 2 ≤ 2 * C * δ ^ 2 := by
      have := mul_le_mul hPδ hrδ hrpos.le (by positivity)
      calc C * (1 + L) * r ^ 2 = P * r := by rw [hP]; ring
        _ ≤ 2 * C * δ * δ := this
        _ = 2 * C * δ ^ 2 := by ring
    have hAlam : A * lam ≤ A * δ ^ 2 := mul_le_mul_of_nonneg_left hlam hA
    have hprod : (A * lam + C * (1 + L) * r ^ 2) * N2 ≤ (A * δ ^ 2 + 2 * C * δ ^ 2) * N2 :=
      mul_le_mul_of_nonneg_right (by linarith) hN2
    have hP2N : P ^ 2 * N2 ≤ 4 * C ^ 2 * δ ^ 2 * N2 := mul_le_mul_of_nonneg_right hP2 hN2
    have hsq : r ^ 2 * x' ^ 2 = (r * x') ^ 2 := by ring
    rw [hsq]
    linarith [hI, hyoung, hvert, hprod, hP2N, sq_nonneg (r * x')]

end SGPT.NPP.DN2
