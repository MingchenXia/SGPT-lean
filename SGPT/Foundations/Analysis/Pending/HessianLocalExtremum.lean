import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-!
# The second-order necessary condition at an interior extremum

For a real function `f` on a real normed space which is `C²` near `x`:

* `IsLocalMin.fderiv_fderiv_nonneg`: if `x` is a local minimum, then the second derivative is
  positive semidefinite, `0 ≤ D²f(x)(h, h)` for every `h`;
* `IsLocalMax.fderiv_fderiv_nonpos`: at a local maximum `D²f(x)(h, h) ≤ 0`.

This is the maximum principle at its most elementary (Gilbarg--Trudinger, Ch. 3; used in
Błocki's proof of the uniform estimate for Yau's theorem, where the lower contact set lies in
`{D²u ≥ 0}`, `blocki05-uniform-estimate:page-0002`, and in the `C²` estimate at a maximum point).
Part L5 of the the proof of Yau's theorem (TN.4 B5), taken by the
nonlinear track (the statement under discussion).

Proof: along the line `t ↦ x + t h` put `g(t) = f(x + t h)` and `ψ(t) = Df(x + t h) h = g'(t)`; then
`ψ(0) = 0` (first-order condition) and `ψ'(0) = D²f(x)(h, h)`.  If this were negative, `ψ < 0` on
some `(0, ε)`, and the mean value theorem would give `g(t) < g(0)` for small `t > 0`.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.HessianLocalExtremum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order necessary condition at a local minimum**: if `f` is `C²` at `x` and has a
local minimum there, then `D²f(x)(h, h) ≥ 0` for every `h`. -/
theorem _root_.IsLocalMin.fderiv_fderiv_nonneg {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hmin : IsLocalMin f x) (h : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x h h := by
  by_contra hneg
  rw [not_le] at hneg
  set c := fderiv ℝ (fderiv ℝ f) x h h with hcdef
  set ℓ : ℝ → E := fun t => x + t • h with hℓdef
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hℓ0 : ℓ 0 = x := by simp [hℓdef]
  have hℓd : ∀ t : ℝ, HasDerivAt ℓ h t := fun t => by
    simpa [hℓdef] using ((hasDerivAt_id t).smul_const h).const_add x
  -- `f` is `C²` near `x` and `x` is a local minimum
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y ∧ f x ≤ f y :=
    (hf.eventually (by simp)).and hmin
  have hevt : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (ℓ t) ∧ f x ≤ f (ℓ t) := by
    have := hℓc.continuousAt (x := 0)
    rw [ContinuousAt, hℓ0] at this
    exact this.eventually hev
  -- `ψ(t) = Df(x + t h) h` has derivative `c` at `0` and vanishes there
  set ψ : ℝ → ℝ := fun t => fderiv ℝ f (ℓ t) h with hψdef
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hψd : HasDerivAt ψ c 0 := by
    have h1 : HasDerivAt (fun t => fderiv ℝ f (ℓ t)) (fderiv ℝ (fderiv ℝ f) x h) 0 := by
      have hDf0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (ℓ 0) := by
        rw [hℓ0]; exact hDf.hasFDerivAt
      simpa [Function.comp_def] using hDf0.comp_hasDerivAt 0 (hℓd 0)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) h1
    simpa [Function.comp_def, hψdef, hcdef] using h2
  have hψ0 : ψ 0 = 0 := by
    simp [hψdef, hℓ0, hmin.fderiv_eq_zero]
  -- `ψ < 0` just to the right of `0`
  have hslope := hasDerivAt_iff_tendsto_slope.mp hψd
  have hneg' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope ψ 0 t < 0 := hslope.eventually (gt_mem_nhds hneg)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t < 0 := by
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope ψ 0 t < 0 :=
      nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht) hneg'
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
    rw [slope_def_field, hψ0, sub_zero, sub_zero] at ht
    exact (div_neg_iff.mp ht).resolve_left (fun h' => absurd h'.2 (not_lt.mpr (le_of_lt ht0)))
      |>.1
  obtain ⟨ε₁, hε₁, hP1⟩ := Metric.eventually_nhds_iff.mp hevt
  obtain ⟨ε₂, hε₂, hP2⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  set t₁ : ℝ := min ε₁ ε₂ / 2 with ht₁
  have ht₁pos : 0 < t₁ := by positivity
  have hsmall : ∀ s ∈ Icc (0 : ℝ) t₁, dist s 0 < ε₁ ∧ dist s 0 < ε₂ := by
    intro s hs
    have : |s| ≤ t₁ := by rw [abs_of_nonneg hs.1]; exact hs.2
    rw [Real.dist_eq, sub_zero]
    constructor <;> linarith [min_le_left ε₁ ε₂, min_le_right ε₁ ε₂]
  -- `g(t) = f(x + t h)` is differentiable on `[0, t₁]` with derivative `ψ`
  have hgd : ∀ s ∈ Icc (0 : ℝ) t₁, HasDerivAt (fun t => f (ℓ t)) (ψ s) s := by
    intro s hs
    have hC := (hP1 (hsmall s hs).1).1
    have hfd : DifferentiableAt ℝ f (ℓ s) := hC.differentiableAt (by norm_num)
    simpa [Function.comp_def, hψdef] using hfd.hasFDerivAt.comp_hasDerivAt s (hℓd s)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun t => f (ℓ t)) ψ ht₁pos
    (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hgd s (Ioo_subset_Icc_self hs))
  have hψξ : ψ ξ < 0 :=
    hP2 ⟨Metric.mem_ball.mpr (hsmall ξ (Ioo_subset_Icc_self hξ)).2, mem_Ioi.mpr hξ.1⟩
  have hmin₁ : f x ≤ f (ℓ t₁) := (hP1 (hsmall t₁ ⟨ht₁pos.le, le_rfl⟩).1).2
  rw [hξeq, sub_zero, hℓ0] at hψξ
  have : f (ℓ t₁) - f x < 0 := by
    have := (div_neg_iff.mp hψξ)
    rcases this with h' | h'
    · exact absurd h'.2 (not_lt.mpr (by linarith))
    · exact h'.1
  linarith

/-- **Second-order necessary condition at a local maximum**: `D²f(x)(h, h) ≤ 0`. -/
theorem _root_.IsLocalMax.fderiv_fderiv_nonpos {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (h : E) : fderiv ℝ (fderiv ℝ f) x h h ≤ 0 := by
  have h1 := IsLocalMin.fderiv_fderiv_nonneg hf.neg hmax.neg h
  have h2 : fderiv ℝ (fderiv ℝ (fun y => -f y)) x = -fderiv ℝ (fderiv ℝ f) x := by
    have : fderiv ℝ (fun y => -f y) = fun y => -fderiv ℝ f y := by
      funext y; exact fderiv_neg
    rw [this]
    exact fderiv_neg
  rw [h2] at h1
  simpa using h1

end SGPT.Foundations.Analysis.Pending.HessianLocalExtremum
