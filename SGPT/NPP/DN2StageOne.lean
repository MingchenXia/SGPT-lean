import SGPT.NPP.DN2SmoothingInterface
import SGPT.NPP.DN2KiselmanManifold
import SGPT.NPP.DN2LogChart
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# The first Kiselman minimum of the smoothing (FPT, first-order smoothing bound)

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, "A first-order smoothing
bound", eq. `big-first-corrected-joint`: adding `K₁ t` (here `K₁ = 1`) to the corrected smoothing
`H_u` absorbs the mixed and vertical terms of the initial joint estimate, and the minimum

  `ψ_{c,δ}(x) = min_{0 < t ≤ δ} (H_u(x, t) + t - c log t)`

is `(θ + e ω)`-psh on `U` with `e = (A c + C δ + 2C² δ)/π`, provided `8 C δ ≤ 1`
(`stageOne_logRadiusData` and `LogRadiusData.thetaPshOff`; in log radii `s = log t`).

## Main results

* `stageOneF`: `F(x, t) = H_u(x, t) + t`.
* `stageOne_logRadiusData`: the hypotheses of the manifold Kiselman lemma.
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

/-- The profile of the first Kiselman minimum: `F(x, t) = H_u(x, t) + t`. -/
def stageOneF (Ψ : (Y → ℝ) → Y → ℝ → ℝ) (u : Y → EReal) (K : ℝ) : Y → ℝ → ℝ :=
  fun x t => correctedSmoothing Ψ u K x t + t

/-- The fibre derivative of `s ↦ H(x, eˢ)` is the logarithmic slope. -/
theorem deriv_comp_exp_eq_logSlope {H : Y → ℝ → ℝ} {x : Y} {s : ℝ}
    (hd : DifferentiableAt ℝ (H x) (Real.exp s)) :
    deriv (fun s => H x (Real.exp s)) s = logSlope H x (Real.exp s) := by
  rw [logSlope, mul_comm]
  exact (hd.hasDerivAt.comp s (Real.hasDerivAt_exp s)).deriv

section Levi

/-- The Levi form of `(z, ζ) ↦ e^{Re ζ}`. -/
theorem leviForm_exp_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (x : E) (s : ℝ)
    (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => Real.exp p.2.re) (x, (s : ℂ)) (v, η) =
      Real.exp s * ‖η‖ ^ 2 / 4 := by
  have hf : ContDiffAt ℝ 2 (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) :=
    (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)).contDiff.contDiffAt
  have hθ : ContDiffAt ℝ 2 Real.exp ((fun p : E × ℂ => p.2.re) (x, (s : ℂ))) :=
    Real.contDiff_exp.contDiffAt
  have hc := SGPT.Foundations.Analysis.Pending.StokesCutoff.realHessian_comp
    (θ := Real.exp) (f := fun p : E × ℂ => p.2.re) (z := (x, (s : ℂ))) hθ hf
  beta_reduce at hc
  have hL : ∀ a b : E × ℂ, realHessian (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) a b = 0 :=
    fun a b => realHessian_clm (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)) _ a b
  have hD : ∀ a : E × ℂ, fderiv ℝ (fun p : E × ℂ => p.2.re) (x, (s : ℂ)) a = a.2.re := fun a => by
    rw [show (fun p : E × ℂ => p.2.re) =
      fun p => (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)) p from rfl,
      ContinuousLinearMap.fderiv]
    simp
  have hdd : deriv (deriv Real.exp) = Real.exp := by simp
  unfold leviForm
  rw [hc, hc, hL, hL, hD, hD, hdd, Real.deriv_exp]
  simp only [Complex.ofReal_re, Prod.smul_snd, smul_eq_mul, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, mul_zero, zero_add]
  have hn : ‖η‖ ^ 2 = η.re * η.re + η.im * η.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hn]
  ring

end Levi

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The hypotheses of the manifold Kiselman lemma for the first minimum** (FPT
`big-first-corrected-joint`). -/
theorem stageOne_logRadiusData {wY : KahlerBackground N Y} {r₀ : ℝ}
    {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ) (θ : ClosedRealOneOneForm N Y)
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) {K A C C₁ : ℝ} (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hge : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal))
    (hconv : ∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s)
    (hlevi : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₀ →
          JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
            (A * logSlope (correctedSmoothing Ψ u K) (e.val.symm z) ‖w‖ + C * ‖w‖) C C)
    {U : Set Y} (hU : IsOpen U)
    (hloc : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ m : ℝ, ∀ y ∈ V, (m : EReal) ≤ u y)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδr : δ < r₀) (hCδ : 8 * C * δ ≤ 1) :
    LogRadiusData wY (θ + ((A * c + C * δ + 2 * C ^ 2 * δ) / Real.pi) • wY.form) U
      (stageOneF Ψ u K) r₀ (fun _ => Real.log δ) c 0 := by
  have hr₀ : 0 < r₀ := hJ.r₀_pos
  have hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh _
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  set H := correctedSmoothing Ψ u K with hHdef
  -- chart smoothness of `H`
  have hHs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞
      (fun p : ComplexModel N × ℝ => H (e.val.symm p.1) p.2) (e.val.target ×ˢ Ioo 0 r₀) := by
    intro e
    have h1 := hJ.contDiffOn _ hint e
    exact h1.add (contDiffOn_const.mul (contDiff_snd.pow 2).contDiffOn)
  have hFs : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞
      (fun p : ComplexModel N × ℝ => stageOneF Ψ u K (e.val.symm p.1) p.2)
      (e.val.target ×ˢ Ioo 0 r₀) := fun e => (hHs e).add contDiff_snd.contDiffOn
  -- the fibres
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
  have hderivF : ∀ x : Y, ∀ s < Real.log r₀,
      deriv (fun s => stageOneF Ψ u K x (Real.exp s)) s =
        deriv (fun s => H x (Real.exp s)) s + Real.exp s := by
    intro x s hs
    have hd : DifferentiableAt ℝ (fun s => H x (Real.exp s)) s :=
      ((hfib x).contDiffAt (isOpen_Iio.mem_nhds hs)).differentiableAt (by simp)
    exact (hd.hasDerivAt.add (Real.hasDerivAt_exp s)).deriv
  have hderiv2F : ∀ x : Y, ∀ s < Real.log r₀,
      deriv (deriv (fun s => stageOneF Ψ u K x (Real.exp s))) s =
        deriv (deriv (fun s => H x (Real.exp s))) s + Real.exp s := by
    intro x s hs
    have hev : deriv (fun s => stageOneF Ψ u K x (Real.exp s)) =ᶠ[𝓝 s]
        fun s => deriv (fun s => H x (Real.exp s)) s + Real.exp s := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
      exact hderivF x t ht
    have hd2c : ContDiffOn ℝ ∞ (deriv fun s => H x (Real.exp s)) (Iio (Real.log r₀)) :=
      (hfib x).deriv_of_isOpen isOpen_Iio (by simp)
    have hd2 : DifferentiableAt ℝ (deriv fun s => H x (Real.exp s)) s :=
      (hd2c.contDiffAt (isOpen_Iio.mem_nhds hs)).differentiableAt (by simp)
    rw [hev.deriv_eq]
    exact (hd2.hasDerivAt.add (Real.hasDerivAt_exp s)).deriv
  have hlogδ : Real.log δ < Real.log r₀ := Real.log_lt_log hδ hδr
  refine ⟨hU, hr₀, hc, le_rfl, hFs, fun _ _ => hlogδ, fun e => contDiffOn_const,
    fun e z _ _ v => by simp, ?_, ?_, ?_, ?_⟩
  · intro x _ s hs
    rw [hderivF x s (lt_of_le_of_lt hs hlogδ)]
    have := (hconv x s (lt_of_le_of_lt hs hlogδ)).1
    positivity
  · intro x _ s hs
    rw [hderiv2F x s (lt_of_le_of_lt hs hlogδ)]
    have := (hconv x s (lt_of_le_of_lt hs hlogδ)).2
    positivity
  · intro x hx
    obtain ⟨V, hV, m, hm⟩ := hloc x hx
    refine ⟨V, hV, m, fun y hy _ s hs => ?_⟩
    have ht : Real.exp s < r₀ := by
      calc Real.exp s ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hs
        _ = δ := Real.exp_log hδ
        _ < r₀ := hδr
    have h1 := (hm y hy).trans (hge y (Real.exp s) (Real.exp_pos s) ht)
    rw [EReal.coe_le_coe_iff] at h1
    show m ≤ H y (Real.exp s) + Real.exp s
    linarith [Real.exp_pos s]
  · -- the joint Levi form
    intro e z hz hzU s hs hslope W ρ hzW hρ v η
    set x := e.val.symm z with hx
    set r := Real.exp s with hr
    have hrpos : 0 < r := Real.exp_pos s
    have hrδ : r ≤ δ := by
      rw [hr]; calc Real.exp s ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hs
        _ = δ := Real.exp_log hδ
    have hsr : s < Real.log r₀ := lt_of_le_of_lt hs hlogδ
    -- the slope bound `λ ≤ c`
    have hHd : DifferentiableAt ℝ (H x) r := by
      have hmaps : MapsTo (fun t : ℝ => ((z, t) : ComplexModel N × ℝ)) (Ioo 0 r₀)
          (e.val.target ×ˢ Ioo 0 r₀) := fun t ht => ⟨hz, ht⟩
      have h := (hHs e).comp (contDiff_const.prodMk contDiff_id).contDiffOn hmaps
      exact ((h.contDiffAt (isOpen_Ioo.mem_nhds ⟨hrpos, lt_of_le_of_lt hrδ hδr⟩)).differentiableAt
        (by simp))
    have hlam : logSlope H x r ≤ c := by
      have h1 := hderivF x s hsr
      rw [deriv_comp_exp_eq_logSlope hHd] at h1
      linarith [Real.exp_pos s]
    -- a local potential of `θ` at `z`
    obtain ⟨W', ρθ, hzW', hρθ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
    -- the three pieces
    set g₁ : ComplexModel N × ℂ → ℝ := fun p => chartJoint H e ρθ (p.1, Complex.exp p.2)
    set g₂ : ComplexModel N × ℂ → ℝ := fun p => Real.exp p.2.re
    set g₃ : ComplexModel N × ℂ → ℝ := fun p => ρ p.1 - ρθ p.1
    have hsplit : (fun p : ComplexModel N × ℂ =>
        stageOneF Ψ u K (e.val.symm p.1) (Real.exp p.2.re) + ρ p.1) = g₁ + g₂ + g₃ := by
      funext p
      simp only [stageOneF, Pi.add_apply, g₁, g₂, g₃, chartJoint, Complex.norm_exp]
      ring
    set p₀ : ComplexModel N × ℂ := (z, (s : ℂ))
    -- smoothness of the pieces
    have hJs : ContDiffAt ℝ ∞ (chartJoint H e ρθ) (z, Complex.exp (s : ℂ)) := by
      have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) (Complex.exp (s : ℂ)) :=
        contDiffAt_norm ℝ (Complex.exp_ne_zero _)
      have hmem : ((z, ‖Complex.exp (s : ℂ)‖) : ComplexModel N × ℝ) ∈ e.val.target ×ˢ Ioo 0 r₀ := by
        refine ⟨hz, ?_, ?_⟩ <;> rw [Complex.norm_exp_ofReal] <;> [exact hrpos;
          exact lt_of_le_of_lt hrδ hδr]
      have h1 : ContDiffAt ℝ ∞ (fun p : ComplexModel N × ℝ => H (e.val.symm p.1) p.2)
          (z, ‖Complex.exp (s : ℂ)‖) :=
        (hHs e).contDiffAt (((e.val.open_target).prod isOpen_Ioo).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℂ => ((q.1, ‖q.2‖) : ComplexModel N × ℝ))
          (z, Complex.exp (s : ℂ)) := contDiffAt_fst.prodMk (hn.comp (z, Complex.exp (s : ℂ)) contDiffAt_snd)
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
      (Real.contDiff_exp.comp (Complex.reCLM.comp
        (ContinuousLinearMap.snd ℝ (ComplexModel N) ℂ)).contDiff).contDiffAt.of_le two_le_infty
    have hρz : ContDiffAt ℝ ∞ ρ z := hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hzW)
    have hρθz : ContDiffAt ℝ ∞ ρθ z := hρθ.2.2.1.contDiffAt (hρθ.1.mem_nhds hzW')
    have hg₃ : ContDiffAt ℝ 2 g₃ p₀ :=
      ((hρz.sub hρθz).comp p₀ contDiffAt_fst).of_le two_le_infty
    have h12 : ContDiffAt ℝ 2 (g₁ + g₂) p₀ := hg₁.add hg₂
    rw [hsplit, leviForm_add h12 hg₃, leviForm_add hg₁ hg₂]
    -- piece 1: the interface estimate
    have hL1 : leviForm g₁ p₀ (v, η) = leviForm (chartJoint H e ρθ) (z, Complex.exp (s : ℂ))
        (v, Complex.exp (s : ℂ) * η) :=
      leviForm_comp_expProd (hJs.of_le two_le_infty) v η
    have hwn : ‖Complex.exp (s : ℂ)‖ = r := Complex.norm_exp_ofReal s
    have hI := hlevi e z hz (Complex.exp (s : ℂ)) (by rw [hwn]; exact hrpos)
      (by rw [hwn]; exact lt_of_le_of_lt hrδ hδr) W' ρθ hzW' hρθ v (Complex.exp (s : ℂ) * η)
    rw [hwn] at hI
    rw [norm_mul, hwn] at hI
    -- piece 2
    have hL2 : leviForm g₂ p₀ (v, η) = r * ‖η‖ ^ 2 / 4 := leviForm_exp_re z s v η
    -- piece 3
    have hL3 : leviForm g₃ p₀ (v, η) =
        Real.pi * ((A * c + C * δ + 2 * C ^ 2 * δ) / Real.pi) * chartNormSq wY e z v := by
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
    have hpi : Real.pi * ((A * c + C * δ + 2 * C ^ 2 * δ) / Real.pi) =
        A * c + C * δ + 2 * C ^ 2 * δ := by field_simp
    rw [hL2, hL3, hpi]
    -- the algebra
    set N2 := chartNormSq wY e z v with hN2
    have hN2 : 0 ≤ N2 := kahler_coeff_nonneg wY hz v
    set nn := Real.sqrt N2 with hnn
    have hnn2 : nn * nn = N2 := Real.mul_self_sqrt hN2
    have hnn0 : 0 ≤ nn := Real.sqrt_nonneg _
    set x' := ‖η‖ with hx'
    have hx0 : 0 ≤ x' := norm_nonneg _
    set lam := logSlope H x r with hlamdef
    have hkey : C * nn * x' ≤ x' ^ 2 / 8 + 2 * C ^ 2 * N2 := by
      nlinarith [sq_nonneg (x' / 2 - 2 * C * nn), hnn2]
    have hyoung : C * nn * (r * x') ≤ r * x' ^ 2 / 8 + 2 * C ^ 2 * r * N2 := by
      calc C * nn * (r * x') = r * (C * nn * x') := by ring
        _ ≤ r * (x' ^ 2 / 8 + 2 * C ^ 2 * N2) := mul_le_mul_of_nonneg_left hkey hrpos.le
        _ = r * x' ^ 2 / 8 + 2 * C ^ 2 * r * N2 := by ring
    have hCr : C * r ≤ C * δ := mul_le_mul_of_nonneg_left hrδ hC
    have hvert : C * (r * x') ^ 2 ≤ r * x' ^ 2 / 8 := by
      have h1 : C * r ≤ 1 / 8 := by linarith
      have h2 : 0 ≤ r * x' ^ 2 := by positivity
      calc C * (r * x') ^ 2 = (C * r) * (r * x' ^ 2) := by ring
        _ ≤ (1 / 8) * (r * x' ^ 2) := mul_le_mul_of_nonneg_right h1 h2
        _ = r * x' ^ 2 / 8 := by ring
    have hAlam : A * lam ≤ A * c := mul_le_mul_of_nonneg_left hlam hA
    have hprod : (A * lam + C * r) * N2 ≤ (A * c + C * δ) * N2 :=
      mul_le_mul_of_nonneg_right (by linarith) hN2
    have hC2r : 2 * C ^ 2 * r * N2 ≤ 2 * C ^ 2 * δ * N2 := by
      have : 0 ≤ 2 * C ^ 2 * N2 := by positivity
      nlinarith
    rw [hL1]
    linarith [hI]

end SGPT.NPP.DN2
