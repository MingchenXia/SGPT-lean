import SGPT.Foundations.Analysis.Pending.MultiplierIdealConvexShift
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.BallSubmean
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A uniform bound for the Lelong numbers of all `θ`-psh potentials on a compact manifold

Source: the standard compactness argument for quasi-psh functions (Demailly, *Complex analytic and
differential geometry*, III.5 for the local bound; the uniform version is the classical fact that a
Lelong number of `θ + ddᶜ w` is controlled by the mass of the current on a coordinate ball, which on
a compact manifold is cohomological).  Here the route avoids currents altogether.

## Main results

* `le_div_log_of_admissible` — **the quantitative three-circle bound**: if `u` is plurisubharmonic on
  `B(p, R)`, `u ≤ A` on `closedBall p R'` (`R' < R`), and `B ≤ u y₀` at one point with
  `0 < ‖y₀ - p‖ < R'`, then every admissible logarithmic exponent `γ` of `u` at `p` satisfies
  `γ ≤ (A - B) / (log R' - log ‖y₀ - p‖)`.  The proof is the one of
  `PshLogExponentBound.exists_bound_forall_log_exponent` with the constants kept explicit.
* `exists_ne_mem_ball_le` — **spreading a lower bound** (ball sub-mean in deficit form,
  `DiscPshOn.ball_deficit_le`): `v ≤ A` on `B(a, R₁)`, `v a ≥ -K`, `B(z, r) ⊆ B(a, R₁)` and
  `λ ≥ (R₁ / r)^d` give a point `y ≠ z` of `B(z, r)` with `v y ≥ -(λ (A + K) - A + 1)`.
* `exists_eventually_le_log_chart` — an admissible exponent in one atlas chart at `x` is admissible
  in every other atlas chart at `x` (the holomorphic transition is locally Lipschitz).
* `hasUniformLelongBound` — **the uniform Lelong bound**: on a compact complex manifold of positive
  dimension, for every closed real `(1,1)`-form `θ` there is one `N` with `ν(w, x) ≤ N` for every
  `θ`-psh potential `w` and every point `x`.  Proof: a finite cover by chart balls carrying fixed
  smooth local potentials of `θ`; normalise `w` by its maximum over the (clopen) union of the balls of
  one component of the overlap graph; spread the lower bound along a path of the overlap graph
  (length `<` the size of the cover); conclude with the three-circle bound.  No connectedness of `X`
  is assumed.
* `exists_multiplierIdeal_le_of_convexComb_le` — route F, F-b step 3 (P3) unconditionally, for compact
  `X` of positive dimension (TN23's statement of I-0794 C-0004 with `0 < n`).

`0 < n` is necessary: in dimension `0` every exponent is admissible and `lelongNumber = ⊤`
(`LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot`).

Sorry-free.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.UniformLelongBound

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

/-! ### The quantitative three-circle bound -/

section ThreeCircles

open Pending.PshThreeCircles

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The quantitative three-circle bound.**  If `u` is plurisubharmonic on `B(p, R)`, bounded by
`A` on `closedBall p R'` with `R' < R`, and `B ≤ u y₀` at a point with `0 < ‖y₀ - p‖ < R'`, then
every admissible logarithmic exponent of `u` at `p` is at most
`(A - B) / (log R' - log ‖y₀ - p‖)`. -/
theorem le_div_log_of_admissible {u : E → EReal} {p : E} {R R' : ℝ}
    (hu : PlurisubharmonicOn u (ball p R)) (hR'R : R' < R) {A B : ℝ}
    (hA : ∀ z ∈ closedBall p R', u z ≤ (A : EReal))
    {y₀ : E} (hd : 0 < ‖y₀ - p‖) (hdR' : ‖y₀ - p‖ < R') (hB : (B : EReal) ≤ u y₀)
    {γ C ρ : ℝ} (hρ : 0 < ρ)
    (hadm : ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      u z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal)) :
    γ ≤ (A - B) / (Real.log R' - Real.log ‖y₀ - p‖) := by
  have hball : closedBall p R' ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hR'R)
  set t₂ : ℝ := Real.log ‖y₀ - p‖ with ht₂
  set t₀ : ℝ := Real.log R' with ht₀
  have ht₂t₀ : t₂ < t₀ := Real.log_lt_log hd hdR'
  have hBA : B ≤ A := by
    have := hB.trans (hA y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hdR'.le)))
    exact_mod_cast this
  by_contra hgs
  rw [not_le] at hgs
  set P : ℝ := A - B - γ * (t₀ - t₂) with hP
  have hPneg : P < 0 := by
    have hpos : 0 < t₀ - t₂ := by linarith
    rw [hP]
    have := (div_lt_iff₀ hpos).mp hgs
    linarith
  set Q : ℝ := B * t₀ - C * (t₀ - t₂) - t₂ * A with hQ
  set t : ℝ := min (min (Real.log ρ) t₂) (-Q / P) - 1 with ht
  have htρ : t < Real.log ρ := by
    have : t ≤ Real.log ρ - 1 := by
      rw [ht]; have := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_left (Real.log ρ) t₂
      linarith [this.trans h2]
    linarith
  have htt₂ : t < t₂ := by
    have : t ≤ t₂ - 1 := by
      rw [ht]
      have h1 := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_right (Real.log ρ) t₂
      linarith [h1.trans h2]
    linarith
  have htQ : t < -Q / P := by
    have : t ≤ -Q / P - 1 := by
      rw [ht]; linarith [min_le_right (min (Real.log ρ) t₂) (-Q / P)]
    linarith
  set r : ℝ := Real.exp t with hr
  have hrpos : 0 < r := Real.exp_pos t
  have hrρ : r < ρ := by
    rw [hr, ← Real.exp_log hρ]; exact Real.exp_lt_exp.mpr htρ
  have hrd : r < ‖y₀ - p‖ := by
    rw [hr, ← Real.exp_log hd]; exact Real.exp_lt_exp.mpr htt₂
  have hrR' : r < R' := hrd.trans hdR'
  have hlogr : Real.log r = t := Real.log_exp t
  have h1 : ∀ z : E, ‖z - p‖ = r → u z ≤ ((γ * t + C : ℝ) : EReal) := by
    intro z hz
    have := hadm z (by rw [hz]; exact hrpos) (by rw [hz]; exact hrρ)
    rwa [hz, hlogr] at this
  have h3 : ∀ z : E, ‖z - p‖ = R' → u z ≤ (A : EReal) := fun z hz =>
    hA z (mem_closedBall.mpr (by rw [dist_eq_norm, hz]))
  have hchord := le_log_interpolation hu hrpos hrR' hball h1 h3
    (z := y₀) hrd.le hdR'.le
  rw [hlogr, ← ht₂, ← ht₀] at hchord
  have hreal : B ≤ γ * t + C + (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) :=
    EReal.coe_le_coe_iff.mp (hB.trans hchord)
  have ht₀t : 0 < t₀ - t := by linarith
  have h' : B - (γ * t + C) ≤ (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) := by linarith
  have hstep : (B - (γ * t + C)) * (t₀ - t) ≤ (t₂ - t) * (A - (γ * t + C)) :=
    (le_div_iff₀ ht₀t).mp h'
  have hclear : B * (t₀ - t) ≤ (γ * t + C) * (t₀ - t₂) + (t₂ - t) * A := by nlinarith [hstep]
  have hfinal : t * P ≤ -Q := by rw [hP, hQ]; nlinarith [hclear]
  have : -Q / P ≤ t := by
    rw [div_le_iff_of_neg hPneg]
    linarith [hfinal]
  linarith

end ThreeCircles

/-! ### Spreading a lower bound by the ball sub-mean inequality -/

section Spreading

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Spreading a lower bound.**  If `v` satisfies the disc criterion on `U ⊇ B(a, R₁)`, `v ≤ A`
there and `v a ≥ -K`, then every ball `B(z, r) ⊆ B(a, R₁)` contains a point `y ≠ z` with
`v y ≥ -(λ (A + K) - A + 1)`, for any `λ ≥ (R₁ / r)^d`, `d = dim_ℝ E`. -/
theorem exists_ne_mem_ball_le {v : E → EReal} {U : Set E} (hv : DiscPshOn v U) {a z : E}
    {R₁ r A K lam : ℝ} (hr : 0 < r) (hBU : ball a R₁ ⊆ U)
    (hA : ∀ y ∈ ball a R₁, v y ≤ (A : EReal)) (hK : ((-K : ℝ) : EReal) ≤ v a)
    (hzr : ball z r ⊆ ball a R₁) (hlam : (R₁ / r) ^ Module.finrank ℝ E ≤ lam) :
    ∃ y ∈ ball z r, y ≠ z ∧ ((-(lam * (A + K) - A + 1) : ℝ) : EReal) ≤ v y := by
  classical
  set μ : Measure E := Measure.addHaar with hμ
  set d : ℕ := Module.finrank ℝ E with hd
  set K' : ℝ := lam * (A + K) - A + 1 with hK'
  have hz : z ∈ ball a R₁ := hzr (mem_ball_self hr)
  have hR₁ : 0 < R₁ := lt_of_le_of_lt dist_nonneg hz
  have ha : a ∈ ball a R₁ := mem_ball_self hR₁
  have hAK : 0 ≤ A + K := by
    have h : ((-K : ℝ) : EReal) ≤ (A : EReal) := hK.trans (hA a ha)
    have : -K ≤ A := EReal.coe_le_coe_iff.mp h
    linarith
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  let dfn : E → ℝ≥0∞ := fun y => ((A : EReal) - v y).toENNReal
  have hupper : ∫⁻ y in ball a R₁, dfn y ∂μ ≤ μ (ball 0 R₁) * dfn a :=
    hv.ball_deficit_le μ a R₁ A hBU hA
  have hda : dfn a ≤ ENNReal.ofReal (A + K) := by
    have h : (A : EReal) - v a ≤ ((A + K : ℝ) : EReal) := by
      calc (A : EReal) - v a ≤ (A : EReal) - ((-K : ℝ) : EReal) := EReal.sub_le_sub le_rfl hK
        _ = ((A + K : ℝ) : EReal) := by rw [← EReal.coe_sub]; ring_nf
    calc dfn a ≤ (((A + K : ℝ)) : EReal).toENNReal := EReal.toENNReal_le_toENNReal h
      _ = ENNReal.ofReal (A + K) := EReal.real_coe_toENNReal _
  have hlow : ∀ y ∈ ball z r, y ≠ z → ENNReal.ofReal (A + K') ≤ dfn y := by
    intro y hy hyz
    have hv' := hcon y hy hyz
    have h : ((A + K' : ℝ) : EReal) ≤ (A : EReal) - v y := by
      calc ((A + K' : ℝ) : EReal) = (A : EReal) - ((-K' : ℝ) : EReal) := by
            rw [← EReal.coe_sub]; ring_nf
        _ ≤ (A : EReal) - v y := EReal.sub_le_sub le_rfl hv'.le
    calc ENNReal.ofReal (A + K') = ((A + K' : ℝ) : EReal).toENNReal :=
          (EReal.real_coe_toENNReal _).symm
      _ ≤ dfn y := EReal.toENNReal_le_toENNReal h
  have hne : ∀ᵐ y ∂μ, y ≠ z := compl_mem_ae_iff.mpr (measure_singleton z)
  have hae : ∀ᵐ y ∂μ.restrict (ball z r), ENNReal.ofReal (A + K') ≤ dfn y := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hne] with y hyz hy
    exact hlow y hy hyz
  have hlowint : ENNReal.ofReal (A + K') * μ (ball z r) ≤ ∫⁻ y in ball a R₁, dfn y ∂μ := by
    calc ENNReal.ofReal (A + K') * μ (ball z r)
          = ∫⁻ _y in ball z r, ENNReal.ofReal (A + K') ∂μ := by
            rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in ball z r, dfn y ∂μ := lintegral_mono_ae hae
      _ ≤ ∫⁻ y in ball a R₁, dfn y ∂μ := lintegral_mono_set hzr
  have hballz : μ (ball z r) = ENNReal.ofReal (r ^ d) * μ (ball 0 1) :=
    Measure.addHaar_ball μ z hr.le
  have hball0 : μ (ball 0 R₁) = ENNReal.ofReal (R₁ ^ d) * μ (ball 0 1) :=
    Measure.addHaar_ball μ 0 hR₁.le
  have hm0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hchain : ENNReal.ofReal ((A + K') * r ^ d) * μ (ball 0 1) ≤
      ENNReal.ofReal (R₁ ^ d * (A + K)) * μ (ball 0 1) := by
    have hK'pos : 0 ≤ A + K' := by
      have : 0 ≤ lam * (A + K) := mul_nonneg (le_trans (by positivity) hlam) hAK
      rw [hK']; linarith
    rw [ENNReal.ofReal_mul hK'pos, ENNReal.ofReal_mul (by positivity), mul_assoc, mul_assoc,
      ← hballz]
    calc ENNReal.ofReal (A + K') * μ (ball z r) ≤ ∫⁻ y in ball a R₁, dfn y ∂μ := hlowint
      _ ≤ μ (ball 0 R₁) * dfn a := hupper
      _ ≤ μ (ball 0 R₁) * ENNReal.ofReal (A + K) := by gcongr
      _ = ENNReal.ofReal (R₁ ^ d) * (ENNReal.ofReal (A + K) * μ (ball 0 1)) := by
            rw [hball0]; ring
  have hreal : (A + K') * r ^ d ≤ R₁ ^ d * (A + K) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      ((ENNReal.mul_le_mul_iff_left hm0 hmtop).mp hchain)
  have hrd : 0 < r ^ d := pow_pos hr d
  have hkey : (R₁ / r) ^ d * r ^ d = R₁ ^ d := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')]
  have hprod : 0 ≤ (lam - (R₁ / r) ^ d) * (A + K) * r ^ d :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam) hAK) hrd.le
  have : (A + K') * r ^ d = lam * (A + K) * r ^ d + r ^ d := by rw [hK']; ring
  nlinarith [hprod, hkey, hrd, this]

end Spreading

/-! ### Changing the chart in which an exponent is admissible -/

section Charts

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **An admissible exponent survives a change of chart.**  If `u ≤ γ log ‖e y - e x‖ + C` on a
punctured neighbourhood of `x`, then `u ≤ γ log ‖f y - f x‖ + C'` there, for every atlas chart `f`
at `x`: the transition `e ∘ f⁻¹` is holomorphic, hence locally Lipschitz at `f x`. -/
theorem exists_eventually_le_log_chart {u : M → EReal} {x : M} {e f : ComplexChart n M}
    (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) {γ C : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ᶠ y in 𝓝[≠] x, u y ≤ ((γ * Real.log ‖e.val y - e.val x‖ + C : ℝ) : EReal)) :
    ∃ C' : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ ((γ * Real.log ‖f.val y - f.val x‖ + C' : ℝ) : EReal) := by
  set T := chartTransition f e with hT
  have hTapp : ∀ y ∈ f.val.source, T (f.val y) = e.val y := by
    intro y hy
    show e.val (f.val.symm (f.val y)) = e.val y
    rw [f.val.left_inv hy]
  have hfx : f.val x ∈ T.source := by
    refine ⟨f.val.map_source hxf, ?_⟩
    show f.val.symm (f.val x) ∈ e.val.source
    rw [f.val.left_inv hxf]; exact hxe
  have hdiff : DifferentiableAt ℝ T (f.val x) :=
    (HolomorphicMaps.chartTransition_contDiffAt_real f e hfx).differentiableAt (by simp)
  obtain ⟨c, hc⟩ := hdiff.hasFDerivAt.isBigO_sub.bound
  have hev : ∀ᶠ y in 𝓝 x, ‖T (f.val y) - T (f.val x)‖ ≤ c * ‖f.val y - f.val x‖ :=
    (f.val.continuousAt hxf).eventually hc
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ e.val.source ∧ y ∈ f.val.source := by
    filter_upwards [e.val.open_source.mem_nhds hxe, f.val.open_source.mem_nhds hxf] with y h1 h2
    exact ⟨h1, h2⟩
  have hcpos : 0 < max c 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨γ * Real.log (max c 1) + C, ?_⟩
  filter_upwards [h, nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hsrc, self_mem_nhdsWithin]
    with y hy hyc hys hyx
  rw [hTapp y hys.2, hTapp x hxf] at hyc
  have hyx' : y ≠ x := hyx
  have hepos : 0 < ‖e.val y - e.val x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hyx' (e.val.injOn hys.1 hxe h))
  have hfpos : 0 < ‖f.val y - f.val x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hyx' (f.val.injOn hys.2 hxf h))
  have hle : ‖e.val y - e.val x‖ ≤ max c 1 * ‖f.val y - f.val x‖ :=
    hyc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hlog : Real.log ‖e.val y - e.val x‖ ≤
      Real.log (max c 1) + Real.log ‖f.val y - f.val x‖ := by
    rw [← Real.log_mul hcpos.ne' hfpos.ne']
    exact Real.log_le_log hepos hle
  refine hy.trans (EReal.coe_le_coe_iff.mpr ?_)
  nlinarith [mul_le_mul_of_nonneg_left hlog hγ]

/-- A property holding on a punctured neighbourhood of `x` holds at the points of a small punctured
ball of any atlas chart at `x` (`LelongNumberChartTransport.exists_chart_radius_of_eventually` for
the preferred chart). -/
theorem exists_radius_of_eventually {x : M} {f : ComplexChart n M} (hxf : x ∈ f.val.source)
    {Φ : M → Prop} (hΦ : ∀ᶠ y in 𝓝[≠] x, Φ y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ComplexModel n, 0 < ‖z - f.val x‖ → ‖z - f.val x‖ < ρ →
      z ∈ f.val.target ∧ Φ (f.val.symm z) := by
  set p : ComplexModel n := f.val x with hp
  have hptarget : p ∈ f.val.target := f.val.map_source hxf
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hΦ)
  have hTopen : IsOpen (f.val.target ∩ f.val.symm ⁻¹' V) :=
    f.val.isOpen_inter_preimage_symm hVopen
  have hpT : p ∈ f.val.target ∩ f.val.symm ⁻¹' V := by
    refine ⟨hptarget, ?_⟩
    show f.val.symm p ∈ V
    rw [hp, f.val.left_inv hxf]
    exact hxV
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hTopen p hpT
  refine ⟨ρ, hρpos, fun z hz0 hzρ => ?_⟩
  have hzball : z ∈ ball p ρ := mem_ball.mpr (by rwa [dist_eq_norm])
  obtain ⟨hztarget, hzV⟩ := hρsub hzball
  refine ⟨hztarget, hVsub hzV ?_⟩
  intro hzx
  have : z = p := by rw [hp, ← hzx, f.val.right_inv hztarget]
  rw [this] at hz0
  simp at hz0

/-- **The Lelong bound from one chart ball.**  Let `v = w ∘ f⁻¹ + ρ` be plurisubharmonic on
`B(c, 9R)`, with `|ρ| ≤ M` on `closedBall c (8R)` and `w ≤ s` on `f⁻¹(B(c, 8R))`.  If `f x ∈ B(c, R)`
and some `y₀ ≠ f x` of `B(f x, R)` has `w (f⁻¹ y₀) ≥ s - K`, then every admissible exponent of `w`
at `x` (in the preferred chart at `x`) is at most `(2M + K) / log 2`. -/
theorem le_of_admissible_of_chartBall {w : M → EReal} {x : M} {f : ComplexChart n M}
    {c : ComplexModel n} {R : ℝ} {ρ : ComplexModel n → ℝ} {s Mb Kb : ℝ} (hR : 0 < R)
    (hpsh : PlurisubharmonicOn (fun z => chartFunction w f z + (ρ z : EReal)) (ball c (9 * R)))
    (hρ : ∀ z ∈ closedBall c (8 * R), |ρ z| ≤ Mb)
    (hle : ∀ z ∈ ball c (8 * R), w (f.val.symm z) ≤ (s : EReal))
    (hxf : x ∈ f.val.source) (hx : f.val x ∈ ball c R)
    {y₀ : ComplexModel n} (hy₀ : y₀ ∈ ball (f.val x) R) (hy₀x : y₀ ≠ f.val x)
    (hy₀w : ((s - Kb : ℝ) : EReal) ≤ w (f.val.symm y₀)) (γ : ℝ≥0)
    (hγ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x, w y ≤ (((γ : ℝ) * Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
        EReal)) :
    (γ : ℝ) ≤ (2 * Mb + Kb) / Real.log 2 := by
  obtain ⟨C, hC⟩ := hγ
  set p : ComplexModel n := f.val x with hp
  obtain ⟨C', hC'⟩ := exists_eventually_le_log_chart (mem_complexChartAt_source x) hxf
    γ.coe_nonneg hC
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := exists_radius_of_eventually hxf hC'
  set v : ComplexModel n → EReal := fun z => chartFunction w f z + (ρ z : EReal) with hv
  have hpc : ‖p - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.mp hx
  -- geometry
  have hsub3 : ball p (3 * R) ⊆ ball c (9 * R) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - c‖ = ‖(z - p) + (p - c)‖ := by congr 1; abel
      _ ≤ ‖z - p‖ + ‖p - c‖ := norm_add_le _ _
      _ < 9 * R := by linarith
  have hsub2 : ∀ z ∈ closedBall p (2 * R), z ∈ ball c (8 * R) ∧ z ∈ closedBall c (8 * R) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have : ‖z - c‖ < 8 * R := by
      calc ‖z - c‖ = ‖(z - p) + (p - c)‖ := by congr 1; abel
        _ ≤ ‖z - p‖ + ‖p - c‖ := norm_add_le _ _
        _ < 8 * R := by linarith
    exact ⟨mem_ball.mpr (by rwa [dist_eq_norm]),
      mem_closedBall.mpr (by rw [dist_eq_norm]; exact this.le)⟩
  have hpshp : PlurisubharmonicOn v (ball p (3 * R)) := fun z hz => hpsh z (hsub3 hz)
  have hρup : ∀ z ∈ closedBall c (8 * R), ρ z ≤ Mb := fun z hz => (abs_le.mp (hρ z hz)).2
  have hρlo : ∀ z ∈ closedBall c (8 * R), -Mb ≤ ρ z := fun z hz => (abs_le.mp (hρ z hz)).1
  -- the upper bound on `closedBall p (2R)`
  have hA : ∀ z ∈ closedBall p (2 * R), v z ≤ ((s + Mb : ℝ) : EReal) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsub2 z hz
    rw [EReal.coe_add]
    exact add_le_add (hle z h1) (EReal.coe_le_coe_iff.mpr (hρup z h2))
  -- the lower bound at `y₀`
  have hy₀norm : ‖y₀ - p‖ < R := by rw [← dist_eq_norm]; exact mem_ball.mp hy₀
  have hy₀pos : 0 < ‖y₀ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy₀x)
  have hy₀cl : y₀ ∈ closedBall c (8 * R) :=
    (hsub2 y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; linarith))).2
  have hB : ((s - Kb - Mb : ℝ) : EReal) ≤ v y₀ := by
    have : ((s - Kb - Mb : ℝ) : EReal) = ((s - Kb : ℝ) : EReal) + ((-Mb : ℝ) : EReal) := by
      rw [← EReal.coe_add]; ring_nf
    rw [this]
    exact add_le_add hy₀w (EReal.coe_le_coe_iff.mpr (hρlo y₀ hy₀cl))
  -- admissibility for `v` at `p`
  have hadm : ∀ z : ComplexModel n, 0 < ‖z - p‖ → ‖z - p‖ < min ρ₀ R →
      v z ≤ (((γ : ℝ) * Real.log ‖z - p‖ + (C' + Mb) : ℝ) : EReal) := by
    intro z hz0 hzr
    obtain ⟨hzt, hzw⟩ := hρ₀sub z hz0 (lt_of_lt_of_le hzr (min_le_left _ _))
    rw [f.val.right_inv hzt] at hzw
    have hzcl : z ∈ closedBall c (8 * R) :=
      (hsub2 z (mem_closedBall.mpr (by
        rw [dist_eq_norm]; linarith [min_le_right ρ₀ R]))).2
    have : (((γ : ℝ) * Real.log ‖z - p‖ + (C' + Mb) : ℝ) : EReal) =
        (((γ : ℝ) * Real.log ‖z - p‖ + C' : ℝ) : EReal) + (Mb : EReal) := by
      rw [← EReal.coe_add]; ring_nf
    rw [this]
    exact add_le_add hzw (EReal.coe_le_coe_iff.mpr (hρup z hzcl))
  have hbound := le_div_log_of_admissible hpshp (by linarith : 2 * R < 3 * R) hA hy₀pos
    (by linarith) hB (lt_min hρ₀ hR) hadm
  -- simplify the bound
  have hnum : (s + Mb) - (s - Kb - Mb) = 2 * Mb + Kb := by ring
  rw [hnum] at hbound
  have hnum0 : 0 ≤ 2 * Mb + Kb := by
    have h1 := hB.trans (hA y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; linarith)))
    have : s - Kb - Mb ≤ s + Mb := EReal.coe_le_coe_iff.mp h1
    linarith
  have hden : Real.log 2 ≤ Real.log (2 * R) - Real.log ‖y₀ - p‖ := by
    have h1 : Real.log ‖y₀ - p‖ ≤ Real.log R := Real.log_le_log hy₀pos hy₀norm.le
    rw [Real.log_mul (by norm_num) hR.ne']
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact hbound.trans (div_le_div_of_nonneg_left hnum0 hlog2 hden)

end Charts

/-! ### Chart balls carrying a fixed local potential, and the spreading step on a manifold -/

section Global

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `(t : EReal) ≤ a + ρ` and `ρ ≤ M` give `t - M ≤ a`, for every extended real `a`. -/
theorem coe_sub_le_of_le_add {t ρ Mb : ℝ} {a : EReal} (h : (t : EReal) ≤ a + (ρ : EReal))
    (hρ : ρ ≤ Mb) : ((t - Mb : ℝ) : EReal) ≤ a := by
  induction a using EReal.rec with
  | bot => simp at h
  | top => exact le_top
  | coe a =>
      rw [← EReal.coe_add] at h
      have := EReal.coe_le_coe_iff.mp h
      exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- A ball `B(c, R)` of an atlas chart such that `B(c, 9R)` carries a fixed smooth local potential
of `θ`. -/
structure PotentialBall (θ : SmoothRealForm n X 2) where
  /-- the chart -/
  chart : ComplexChart n X
  /-- the centre, in chart coordinates -/
  center : ComplexModel n
  /-- the radius -/
  radius : ℝ
  /-- the local potential -/
  pot : ComplexModel n → ℝ
  radius_pos : 0 < radius
  isPotential : IsSmoothLocalPotential θ chart (ball center (9 * radius)) pot

namespace PotentialBall

variable {θ : SmoothRealForm n X 2} (D : PotentialBall θ)

/-- The points of `X` whose chart coordinates lie in `B(c, R)`. -/
def set : Set X := D.chart.val.source ∩ D.chart.val ⁻¹' ball D.center D.radius

theorem isOpen_set : IsOpen D.set := D.chart.val.isOpen_inter_preimage isOpen_ball

theorem ball_subset_target : ball D.center (9 * D.radius) ⊆ D.chart.val.target :=
  D.isPotential.2.1

/-- The local potential is bounded on `closedBall c (8R)`. -/
theorem exists_pot_bound : ∃ Mb : ℝ, ∀ z ∈ closedBall D.center (8 * D.radius), |D.pot z| ≤ Mb := by
  have hsub : closedBall D.center (8 * D.radius) ⊆ ball D.center (9 * D.radius) :=
    closedBall_subset_ball (by linarith [D.radius_pos])
  obtain ⟨C, hC⟩ := (isCompact_closedBall D.center (8 * D.radius)).exists_bound_of_continuousOn
    (D.isPotential.2.2.1.continuousOn.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

/-- `w ∘ f⁻¹ + ρ` is plurisubharmonic on `B(c, 9R)` for EVERY `θ`-psh `w`. -/
theorem plurisubharmonicOn {w : X → EReal} (hw : ThetaPlurisubharmonic θ w) :
    PlurisubharmonicOn (fun z => chartFunction w D.chart z + (D.pot z : EReal))
      (ball D.center (9 * D.radius)) :=
  BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hw D.chart D.isPotential

/-- `D` is `K`-good for `w` at level `s`: some point of `closedBall c (2R)` has `w ≥ s - K`. -/
def Good (w : X → EReal) (s K : ℝ) : Prop :=
  ∃ a ∈ closedBall D.center (2 * D.radius), ((s - K : ℝ) : EReal) ≤ w (D.chart.val.symm a)

theorem Good.mono {w : X → EReal} {s K K' : ℝ} (h : D.Good w s K) (hKK' : K ≤ K') :
    D.Good w s K' := by
  obtain ⟨a, ha, haw⟩ := h
  exact ⟨a, ha, le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) haw⟩

/-- **The spreading step in a chart ball.**  If `w ≤ s` on `f⁻¹(B(c, 8R))` and `D` is `K`-good,
then every ball `B(z, r)` with `z ∈ B(c, R)`, `r ≤ R` contains a point `y ≠ z` with
`w (f⁻¹ y) ≥ s - (λ (2M + K) + 1)`. -/
theorem exists_ne_mem_ball_le (hn : 0 < n) {w : X → EReal} (hw : ThetaPlurisubharmonic θ w)
    {s Mb K lam : ℝ} (hMb : ∀ z ∈ closedBall D.center (8 * D.radius), |D.pot z| ≤ Mb)
    (hle : ∀ z ∈ ball D.center (8 * D.radius), w (D.chart.val.symm z) ≤ (s : EReal))
    (hgood : D.Good w s K) {z : ComplexModel n} (hz : z ∈ ball D.center D.radius) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ D.radius)
    (hlam : (4 * D.radius / r) ^ Module.finrank ℝ (ComplexModel n) ≤ lam) :
    ∃ y ∈ ball z r, y ≠ z ∧
      ((s - (lam * (2 * Mb + K) + 1) : ℝ) : EReal) ≤ w (D.chart.val.symm y) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨a, ha, haw⟩ := hgood
  set c := D.center
  set R := D.radius
  have hR := D.radius_pos
  have hpsh := (D.plurisubharmonicOn hw).discPshOn
  have hac : ‖a - c‖ ≤ 2 * R := by rw [← dist_eq_norm]; exact mem_closedBall.mp ha
  have hzc : ‖z - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.mp hz
  have hBU : ball a (4 * R) ⊆ ball c (9 * R) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc ‖y - c‖ = ‖(y - a) + (a - c)‖ := by congr 1; abel
      _ ≤ ‖y - a‖ + ‖a - c‖ := norm_add_le _ _
      _ < 9 * R := by linarith
  have hin8 : ∀ y ∈ ball a (4 * R), y ∈ ball c (8 * R) ∧ y ∈ closedBall c (8 * R) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have : ‖y - c‖ < 8 * R := by
      calc ‖y - c‖ = ‖(y - a) + (a - c)‖ := by congr 1; abel
        _ ≤ ‖y - a‖ + ‖a - c‖ := norm_add_le _ _
        _ < 8 * R := by linarith
    exact ⟨mem_ball.mpr (by rwa [dist_eq_norm]),
      mem_closedBall.mpr (by rw [dist_eq_norm]; exact this.le)⟩
  have hA : ∀ y ∈ ball a (4 * R),
      chartFunction w D.chart y + (D.pot y : EReal) ≤ ((s + Mb : ℝ) : EReal) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hin8 y hy
    rw [EReal.coe_add]
    exact add_le_add (hle y h1) (EReal.coe_le_coe_iff.mpr (abs_le.mp (hMb y h2)).2)
  have hacl : a ∈ closedBall c (8 * R) :=
    mem_closedBall.mpr (by rw [dist_eq_norm]; linarith)
  have hK : ((-(K + Mb - s) : ℝ) : EReal) ≤ chartFunction w D.chart a + (D.pot a : EReal) := by
    have : ((-(K + Mb - s) : ℝ) : EReal) = ((s - K : ℝ) : EReal) + ((-Mb : ℝ) : EReal) := by
      rw [← EReal.coe_add]; ring_nf
    rw [this]
    exact add_le_add haw (EReal.coe_le_coe_iff.mpr (abs_le.mp (hMb a hacl)).1)
  have hzr : ball z r ⊆ ball a (4 * R) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc ‖y - a‖ = ‖(y - z) + (z - c) - (a - c)‖ := by congr 1; abel
      _ ≤ ‖y - z‖ + ‖z - c‖ + ‖a - c‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ < 4 * R := by linarith
  obtain ⟨y, hy, hyz, hyv⟩ := UniformLelongBound.exists_ne_mem_ball_le hpsh hr hBU hA hK hzr hlam
  refine ⟨y, hy, hyz, ?_⟩
  have hycl : y ∈ closedBall c (8 * R) := (hin8 y (hzr hy)).2
  have hρ : D.pot y ≤ Mb := (abs_le.mp (hMb y hycl)).2
  have hfinal := coe_sub_le_of_le_add hyv hρ
  have heq : -(lam * (s + Mb + (K + Mb - s)) - (s + Mb) + 1) - Mb =
      s - (lam * (2 * Mb + K) + 1) := by ring
  rw [heq] at hfinal
  exact hfinal

/-- **Propagation from one chart ball to an overlapping one.**  If `B(z, r)` is mapped by the
transition into `B(c', 2R')` of `E`, then `K`-goodness of `D` gives `(λ(2M+K)+1)`-goodness of `E`. -/
theorem good_of_good (hn : 0 < n) (E : PotentialBall θ) {w : X → EReal}
    (hw : ThetaPlurisubharmonic θ w) {s Mb K lam : ℝ}
    (hMb : ∀ z ∈ closedBall D.center (8 * D.radius), |D.pot z| ≤ Mb)
    (hle : ∀ z ∈ ball D.center (8 * D.radius), w (D.chart.val.symm z) ≤ (s : EReal))
    (hgood : D.Good w s K) {z : ComplexModel n} (hz : z ∈ ball D.center D.radius) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ D.radius)
    (hlam : (4 * D.radius / r) ^ Module.finrank ℝ (ComplexModel n) ≤ lam)
    (htr : ∀ y ∈ ball z r, y ∈ D.chart.val.target ∧ D.chart.val.symm y ∈ E.chart.val.source ∧
      E.chart.val (D.chart.val.symm y) ∈ ball E.center (2 * E.radius)) :
    E.Good w s (lam * (2 * Mb + K) + 1) := by
  obtain ⟨y, hy, -, hyw⟩ := D.exists_ne_mem_ball_le hn hw hMb hle hgood hz hr hrR hlam
  obtain ⟨-, hsrc, hball⟩ := htr y hy
  refine ⟨E.chart.val (D.chart.val.symm y), ball_subset_closedBall hball, ?_⟩
  rw [E.chart.val.left_inv hsrc]
  exact hyw

end PotentialBall

/-- Every point lies in a potential ball, once `θ` has smooth local potentials. -/
theorem exists_potentialBall {θ : SmoothRealForm n X 2} (hθ : HasSmoothLocalPotentials θ)
    (x : X) : ∃ D : PotentialBall θ, x ∈ D.set := by
  set e : ComplexChart n X := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hxW, hρ⟩ := hθ e (e.val x) (e.val.map_source hxs)
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 (e.val x) hxW
  refine ⟨⟨e, e.val x, ε / 9, ρ, by positivity, hρ.mono isOpen_ball ?_⟩, hxs, ?_⟩
  · have : 9 * (ε / 9) = ε := by ring
    rw [this]; exact hεW
  · show e.val x ∈ ball (e.val x) (ε / 9)
    exact mem_ball_self (by positivity)

/-- Propagation of goodness along a walk of a graph on the cover. -/
theorem good_of_walk {θ : SmoothRealForm n X 2} {ι : Type*} (D : ι → PotentialBall θ)
    (G : SimpleGraph ι) {j₀ : ι} {w : X → EReal} {s : ℝ} (Φ : ℝ → ℝ) (hΦ : ∀ K, 0 ≤ K → 0 ≤ Φ K)
    (step : ∀ i j K, 0 ≤ K → G.Adj i j → G.Reachable i j₀ → (D i).Good w s K →
      (D j).Good w s (Φ K)) :
    ∀ {i : ι} (p : G.Walk i j₀) {K : ℝ}, 0 ≤ K → (D i).Good w s K →
      (D j₀).Good w s (Φ^[p.length] K) := by
  intro i p
  induction p with
  | nil => intro K _ h; simpa using h
  | @cons u v t hadj p ih =>
      intro K hK h
      rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply]
      exact ih step (hΦ K hK) (step u v K hK hadj (SimpleGraph.Walk.cons hadj p).reachable h)

end Global

/-! ### The uniform Lelong bound -/

section Main

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

open MultiplierIdealConvexShift FirstPass.PositiveClasses

/-- **The uniform Lelong bound.**  On a compact complex manifold of positive dimension, for every
closed real `(1,1)`-form `θ` there is one `N` bounding the Lelong numbers of all `θ`-psh potentials
at all points.  (False for `n = 0`, where every Lelong number is `⊤`.) -/
theorem hasUniformLelongBound (hn : 0 < n) [CompactSpace X] (θ : ClosedRealOneOneForm n X) :
    HasUniformLelongBound θ := by
  classical
  by_cases hex : ∃ w₀ : X → EReal, IsThetaPshPotential θ.val w₀
  swap
  · exact ⟨0, fun w hw => absurd ⟨w, hw⟩ hex⟩
  obtain ⟨w₀, hw₀⟩ := hex
  have hloc : HasSmoothLocalPotentials θ.val := hw₀.1.hasSmoothLocalPotentials
  choose Dx hDx using exists_potentialBall hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (Dx x).set)
    (fun x => (Dx x).isOpen_set) (fun x _ => mem_iUnion.mpr ⟨x, hDx x⟩)
  let ι := { x : X // x ∈ t }
  let D : ι → PotentialBall θ.val := fun i => Dx i.1
  have hcover : ∀ x : X, ∃ i : ι, x ∈ (D i).set := by
    intro x
    have := ht (mem_univ x)
    rw [mem_iUnion₂] at this
    obtain ⟨y, hy, hxy⟩ := this
    exact ⟨⟨y, hy⟩, hxy⟩
  -- a common bound for the local potentials
  choose Mbi hMbi using fun i : ι => (D i).exists_pot_bound
  set Mb : ℝ := ∑ i, |Mbi i| with hMbdef
  have hMb : ∀ i, ∀ z ∈ closedBall (D i).center (8 * (D i).radius), |(D i).pot z| ≤ Mb := by
    intro i z hz
    calc |(D i).pot z| ≤ Mbi i := hMbi i z hz
      _ ≤ |Mbi i| := le_abs_self _
      _ ≤ Mb := Finset.single_le_sum (f := fun i => |Mbi i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
  -- transition data for overlapping pairs
  have hpair : ∀ i j : ι, ∃ z : ComplexModel n, ∃ r : ℝ, 0 < r ∧ r ≤ (D i).radius ∧
      (((D i).set ∩ (D j).set).Nonempty → z ∈ ball (D i).center (D i).radius ∧
        ∀ y ∈ ball z r, y ∈ (D i).chart.val.target ∧
          (D i).chart.val.symm y ∈ (D j).chart.val.source ∧
          (D j).chart.val ((D i).chart.val.symm y) ∈ ball (D j).center (2 * (D j).radius)) := by
    intro i j
    by_cases hij : ((D i).set ∩ (D j).set).Nonempty
    · obtain ⟨x, ⟨hxi, hxi'⟩, hxj, hxj'⟩ := hij
      set O : Set (ComplexModel n) := (D i).chart.val.target ∩ (D i).chart.val.symm ⁻¹'
        ((D j).chart.val.source ∩ (D j).chart.val ⁻¹' ball (D j).center (2 * (D j).radius))
        with hOdef
      have hO : IsOpen O := (D i).chart.val.isOpen_inter_preimage_symm
        ((D j).chart.val.isOpen_inter_preimage isOpen_ball)
      have hzO : (D i).chart.val x ∈ O := by
        refine ⟨(D i).chart.val.map_source hxi, ?_⟩
        show (D i).chart.val.symm ((D i).chart.val x) ∈
          (D j).chart.val.source ∩ (D j).chart.val ⁻¹' ball (D j).center (2 * (D j).radius)
        rw [(D i).chart.val.left_inv hxi]
        refine ⟨hxj, ?_⟩
        have hxj'' : (D j).chart.val x ∈ ball (D j).center (D j).radius := hxj'
        exact ball_subset_ball (by linarith [(D j).radius_pos]) hxj''
      obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO _ hzO
      refine ⟨(D i).chart.val x, min ε (D i).radius, lt_min hε (D i).radius_pos,
        min_le_right _ _, fun _ => ⟨hxi', fun y hy => ?_⟩⟩
      obtain ⟨h1, h2, h3⟩ := hεO (ball_subset_ball (min_le_left _ _) hy)
      exact ⟨h1, h2, h3⟩
    · exact ⟨(D i).center, (D i).radius, (D i).radius_pos, le_rfl, fun h => absurd h hij⟩
  choose zp rp hrp0 hrpR hrp using hpair
  set d : ℕ := Module.finrank ℝ (ComplexModel n) with hd
  set lam : ℝ := 4 ^ d + ∑ i, ∑ j, (4 * (D i).radius / rp i j) ^ d with hlamdef
  have hterm : ∀ i j, 0 ≤ (4 * (D i).radius / rp i j) ^ d := fun i j =>
    pow_nonneg (div_nonneg (by linarith [(D i).radius_pos]) (hrp0 i j).le) _
  have hsum0 : (0 : ℝ) ≤ ∑ i, ∑ j, (4 * (D i).radius / rp i j) ^ d :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  have hpow0 : (0 : ℝ) ≤ 4 ^ d := by positivity
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; linarith
  have hlam_pair : ∀ i j, (4 * (D i).radius / rp i j) ^ d ≤ lam := by
    intro i j
    have h1 : (4 * (D i).radius / rp i j) ^ d ≤ ∑ j', (4 * (D i).radius / rp i j') ^ d :=
      Finset.single_le_sum (f := fun j' => (4 * (D i).radius / rp i j') ^ d)
        (fun j' _ => hterm i j') (Finset.mem_univ j)
    have h2 : ∑ j', (4 * (D i).radius / rp i j') ^ d ≤
        ∑ i', ∑ j', (4 * (D i').radius / rp i' j') ^ d :=
      Finset.single_le_sum (f := fun i' => ∑ j', (4 * (D i').radius / rp i' j') ^ d)
        (fun i' _ => Finset.sum_nonneg fun j' _ => hterm i' j') (Finset.mem_univ i)
    rw [hlamdef]; linarith
  have hlam_four : ∀ i, (4 * (D i).radius / (D i).radius) ^ d ≤ lam := by
    intro i
    have : 4 * (D i).radius / (D i).radius = 4 := by
      field_simp [(D i).radius_pos.ne']
    rw [this, hlamdef]; linarith
  set Φ : ℝ → ℝ := fun K => lam * (2 * Mb + K) + 1 with hΦdef
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hΦ0 : ∀ K, 0 ≤ K → 0 ≤ Φ K := fun K hK =>
    add_nonneg (mul_nonneg hlam0 (by linarith)) zero_le_one
  have hΦmono : Monotone Φ := fun a b hab => by
    simp only [hΦdef]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 * Mb + a ≤ 2 * Mb + b) hlam0
    linarith
  set Kfin : ℝ := Φ^[Fintype.card ι] 0 with hKfin
  refine ⟨(2 * Mb + Φ Kfin) / Real.log 2, ?_⟩
  intro w hw x
  -- the overlap graph and the component of a ball containing `x`
  let G : SimpleGraph ι := SimpleGraph.fromRel fun i j => ((D i).set ∩ (D j).set).Nonempty
  obtain ⟨j₀, hxj₀⟩ := hcover x
  set U : Set X := ⋃ i ∈ {i : ι | G.Reachable i j₀}, (D i).set with hUdef
  have hUopen : IsOpen U := isOpen_biUnion fun i _ => (D i).isOpen_set
  have hkey : ∀ k : ι, ((D k).set ∩ U).Nonempty → G.Reachable k j₀ := by
    rintro k ⟨y, hyk, hyU⟩
    rw [hUdef, mem_iUnion₂] at hyU
    obtain ⟨i, hi, hyi⟩ := hyU
    by_cases hki : k = i
    · rw [hki]; exact hi
    · have hadj : G.Adj k i := by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hki, Or.inl ⟨y, hyk, hyi⟩⟩
      exact hadj.reachable.trans hi
  have hUclosed : IsClosed U := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨k, hyk⟩ := hcover y
    refine ⟨(D k).set, ?_, (D k).isOpen_set, hyk⟩
    intro y' hy' hy'U
    have hk := hkey k ⟨y', hy', hy'U⟩
    exact hy (mem_iUnion₂.mpr ⟨k, hk, hyk⟩)
  have hUclopen : IsClopen U := ⟨hUclosed, hUopen⟩
  have hxU : x ∈ U := mem_iUnion₂.mpr ⟨j₀, SimpleGraph.Reachable.refl j₀, hxj₀⟩
  -- the maximum of `w` on `U`
  have husc : UpperSemicontinuous w := hw.1.quasiPlurisubharmonic.upperSemicontinuous
  obtain ⟨xs, hxsU, hmax⟩ :=
    (husc.upperSemicontinuousOn U).exists_isMaxOn ⟨x, hxU⟩ hUclosed.isCompact
  obtain ⟨i₀, hi₀, hxsi₀⟩ := mem_iUnion₂.mp hxsU
  have hbot : w xs ≠ ⊥ := by
    obtain ⟨y, hy, hyb⟩ := hw.2 xs (D i₀).set (D i₀).isOpen_set hxsi₀
    have hyU : y ∈ U := mem_iUnion₂.mpr ⟨i₀, hi₀, hy⟩
    intro h
    have : w y ≤ ⊥ := h ▸ hmax hyU
    exact hyb (le_bot_iff.mp this)
  have htop : w xs ≠ ⊤ := hw.1.quasiPlurisubharmonic.ne_top xs
  set s : ℝ := (w xs).toReal with hsdef
  have hs : w xs = (s : EReal) := (EReal.coe_toReal htop hbot).symm
  -- `w ≤ s` on the chart region of every ball of the component
  have hle : ∀ i, G.Reachable i j₀ → ∀ z ∈ ball (D i).center (8 * (D i).radius),
      w ((D i).chart.val.symm z) ≤ (s : EReal) := by
    intro i hi z hz
    have hsub8 : ball (D i).center (8 * (D i).radius) ⊆ (D i).chart.val.target :=
      (ball_subset_ball (by linarith [(D i).radius_pos])).trans (D i).ball_subset_target
    have hconn : IsPreconnected ((D i).chart.val.symm '' ball (D i).center (8 * (D i).radius)) :=
      isPreconnected_ball.image _ ((D i).chart.val.continuousOn_symm.mono hsub8)
    have hc : (D i).center ∈ (D i).chart.val.target :=
      hsub8 (mem_ball_self (by linarith [(D i).radius_pos]))
    have hcen : (D i).chart.val.symm (D i).center ∈ (D i).set := by
      refine ⟨(D i).chart.val.map_target hc, ?_⟩
      show (D i).chart.val ((D i).chart.val.symm (D i).center) ∈ ball (D i).center (D i).radius
      rw [(D i).chart.val.right_inv hc]; exact mem_ball_self (D i).radius_pos
    have hne : (((D i).chart.val.symm '' ball (D i).center (8 * (D i).radius)) ∩ U).Nonempty :=
      ⟨_, ⟨(D i).center, mem_ball_self (by linarith [(D i).radius_pos]), rfl⟩,
        mem_iUnion₂.mpr ⟨i, hi, hcen⟩⟩
    have hmem : (D i).chart.val.symm z ∈ U :=
      hconn.subset_isClopen hUclopen hne ⟨z, hz, rfl⟩
    exact (hmax hmem).trans hs.le
  -- the ball containing the maximum is `0`-good
  have hgood₀ : (D i₀).Good w s 0 := by
    refine ⟨(D i₀).chart.val xs, ?_, ?_⟩
    · exact ball_subset_closedBall
        (ball_subset_ball (by linarith [(D i₀).radius_pos]) hxsi₀.2)
    · rw [(D i₀).chart.val.left_inv hxsi₀.1, hs]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  -- the propagation step
  have hstep : ∀ i j K, 0 ≤ K → G.Adj i j → G.Reachable i j₀ → (D i).Good w s K →
      (D j).Good w s (Φ K) := by
    intro i j K _ hadj hi hgood
    have hne : ((D i).set ∩ (D j).set).Nonempty := by
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | ⟨y, h1, h2⟩
      · exact h
      · exact ⟨y, h2, h1⟩
    obtain ⟨hz, htr⟩ := hrp i j hne
    exact (D i).good_of_good hn (D j) hw.1 (hMb i) (hle i hi) hgood hz (hrp0 i j) (hrpR i j)
      (hlam_pair i j) htr
  -- along a path from `i₀` to `j₀`
  obtain ⟨p⟩ : G.Reachable i₀ j₀ := hi₀
  have hlen : p.bypass.length ≤ Fintype.card ι := p.bypass_isPath.length_lt.le
  have hgood := good_of_walk D G Φ hΦ0 hstep p.bypass le_rfl hgood₀
  have hmono := hΦmono.monotone_iterate_of_le_map (hΦ0 0 le_rfl)
  have hgoodfin : (D j₀).Good w s Kfin := hgood.mono _ (hmono hlen)
  -- the final chart ball
  obtain ⟨y₀, hy₀, hy₀x, hy₀w⟩ := (D j₀).exists_ne_mem_ball_le hn hw.1 (hMb j₀)
    (hle j₀ (SimpleGraph.Reachable.refl j₀)) hgoodfin hxj₀.2 (D j₀).radius_pos le_rfl
    (hlam_four j₀)
  apply LelongNumberChartTransport.lelongNumber_le_ofReal
  intro γ hγ
  exact le_of_admissible_of_chartBall (D j₀).radius_pos ((D j₀).plurisubharmonicOn hw.1)
    (hMb j₀) (hle j₀ (SimpleGraph.Reachable.refl j₀)) hxj₀.1 hxj₀.2 hy₀ hy₀x hy₀w γ hγ

/-- **Route F, F-b step 3 (P3), unconditionally** on a compact manifold of positive dimension:
TN23's statement with `0 < n`.  The Kähler background of that statement is not used
(the proof needs neither a Kähler form nor connectedness); it is kept so that the consumer's call
shape is the agreed one. -/
theorem exists_multiplierIdeal_le_of_convexComb_le (hn : 0 < n) [CompactSpace X]
    (_omega : KahlerBackground n X) (θ₂ : ClosedRealOneOneForm n X) {q : ℝ} (hq : 0 < q) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ {v w φ : X → EReal},
      ManifoldQuasiPlurisubharmonic (n := n) v → IsThetaPshPotential θ₂.val w →
      ManifoldQuasiPlurisubharmonic (n := n) φ →
      (∀ x, ((1 - t : ℝ) : EReal) * v x + (t : EReal) * w x ≤ φ x) →
      (FirstPass.HolomorphicIdealSheaves.multiplierIdeal (n := n) (q + 1) v).Le
        (FirstPass.HolomorphicIdealSheaves.multiplierIdeal (n := n) q φ) :=
  exists_multiplierIdeal_le_of_convexComb_le_of_hasUniformLelongBound θ₂
    (hasUniformLelongBound hn θ₂) hq

end Main

end

end SGPT.Foundations.Analysis.Pending.UniformLelongBound
