import SGPT.NPP.DN2Regularity

/-!
# FPT `thm:big-metric-laplacian-rooftop` on the resolution, from the joint smoothing

Lane DN2, `thm:DNT23_C11bar`.  This is the analytic core of FPT `thm:big-metric-laplacian-rooftop`
after the reduction to one obstacle and the passage to a modification: on a compact Kähler manifold
`(Y, ω)` with a joint smoothing (`IsJointSmoothing`, FPT `lem:chern-joint-smoothing`), let

* `0 ≤ f ≤ B` be continuous with `-f` a `θ_f`-psh potential for some smooth closed `θ_f`
  (e.g. `f = g ∘ π` with `g` of bounded complex Hessian),
* `u = P_θ(f)` be the envelope (a `θ`-psh potential),
* `φ ≤ 0` be a `(θ - ω)`-psh potential (a Kähler current `θ + ddᶜφ ≥ ω`), finite, smooth and with
  `i∂∂̄φ ≤ C_φ ω` off an analytic set `Z` with empty interior (a divisorial Kähler current on a log
  resolution: `φ = Σ βⱼ log|gⱼ|² + smooth`).

Then `u` lies in `C^{1,1̄}_ω(Y \ Z)` (`HasBoundedMetricLaplacianOn`): continuous, with bounded
`ω`-Laplacian on every compact subset of `Y \ Z`.

Proof: `first_order_bound`, `second_order_bound`, uniformity of `R₂ = b₀(1 + B + |φ|)` on
compact subsets, `hasBoundedMetricLaplacianOn_of_quadratic`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **FPT `thm:big-metric-laplacian-rooftop` on the resolution** (from the joint smoothing). -/
theorem hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing {wY : KahlerBackground N Y}
    {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ)
    {θ : ClosedRealOneOneForm N Y} {f : Y → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    {B : ℝ} (hB0 : 0 ≤ B) (hfB : ∀ y, f y ≤ B) {θf : ClosedRealOneOneForm N Y}
    (hfneg : IsThetaPshPotential θf.val (fun y => ((-f y : ℝ) : EReal)))
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    (hudef : u = rooftopEnvelope θ.val (fun y => (f y : EReal))) (hule : ∀ y, u y ≤ (f y : EReal))
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
          Cφ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v])) :
    HasBoundedMetricLaplacianOn wY Zᶜ (fun y => (u y).toReal) := by
  have hZc : IsClosed Z := hZ.isClosed
  obtain ⟨Kf, hKf, hΨf⟩ := obstacle_smoothing_le hJ hfneg
  obtain ⟨K, A, C, C₁, hK, hA, hC, hC₁, hge, hconv, hlevi, himp⟩ := hJ.psh θ u hu
  obtain ⟨δ₀, a₀, hδ₀, hδ₀r, ha₀, hfirst⟩ := first_order_bound hJ hf hf0 hB0 hfB hKf hΨf hu hudef
    hule hK hA hC hge hconv hlevi hφ hφθ hφ0 hZ hZi hφZ hφc
  obtain ⟨δ₂, b₀, hδ₂, hb₀, hsecond⟩ := second_order_bound hJ hf hf0 hB0 hfB hKf hΨf hu hudef
    hule hK hA hC hC₁ hge hconv himp hφ hφθ hφ0 hZ hZi hφZ hφc hCφ hφs hφL hδ₀ hδ₀r ha₀ hfirst
  have hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh _
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  have hφu : ∀ y, φ y ≤ u y := by
    have := le_rooftopEnvelope hφθ (quasiEverywhere_of_forall (n := N)
      fun y => (hφ0 y).trans (EReal.coe_nonneg.mpr (hf0 y)))
    intro y; rw [hudef]; exact this y
  have hufin : ∀ y ∈ Zᶜ, u y = ((u y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hule y))
      (ne_bot_of_le_ne_bot (hφZ y hy) (hφu y))).symm
  refine hasBoundedMetricLaplacianOn_of_quadratic hJ hint hK hZc.isOpen_compl hge hufin ?_
  intro Kc hKcU hKcc
  -- `R₂ = b₀ (1 + B + |φ|)` is bounded on the compact set
  have hRc : ContinuousOn (fun y => b₀ * (1 + B + |(φ y).toReal|)) Kc :=
    (continuousOn_const.mul (continuousOn_const.add (hφc.mono hKcU).abs))
  obtain ⟨M₀, hM₀⟩ := hKcc.exists_bound_of_continuousOn hRc
  set M₂ := |M₀| with hM₂
  have hM₂0 : 0 ≤ M₂ := abs_nonneg _
  have hRle : ∀ y ∈ Kc, b₀ * (1 + B + |(φ y).toReal|) ≤ M₂ := fun y hy => by
    have := hM₀ y hy
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  have hRnn : ∀ y, 0 ≤ b₀ * (1 + B + |(φ y).toReal|) := fun y => by positivity
  refine ⟨M₂ * Real.exp (2 * M₂), δ₂ * Real.exp (-M₂), by positivity, fun y hy r hr hrr => ?_⟩
  have hyZ : y ∉ Z := hKcU hy
  set R := b₀ * (1 + B + |(φ y).toReal|) with hR
  have hRM : R ≤ M₂ := hRle y hy
  have hrle : r ≤ δ₂ * Real.exp (-R) := by
    have : Real.exp (-M₂) ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
    have := mul_le_mul_of_nonneg_left this hδ₂.le
    linarith
  have h := hsecond y hyZ r hr hrle
  have hexp : R * Real.exp (2 * R) ≤ M₂ * Real.exp (2 * M₂) :=
    mul_le_mul hRM (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hM₂0
  have := mul_le_mul_of_nonneg_right hexp (sq_nonneg r)
  linarith

end SGPT.NPP.DN2
