import SGPT.Foundations.Analysis.Pending.SmoothMax
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

set_option autoImplicit false

/-!
# Smooth truncation of a potential with smooth analytic singularities

Let `u` be a `θ`-psh potential with smooth analytic singularities, `θ ≥ 0`.  For a
level `t` put `u_t = -t + P(u + t)`, where `P` is the smooth convex function with
`P(s) = 0` for `s ≤ -1`, `P(s) = s` for `s ≥ 1` and `0 ≤ P' ≤ 1`
(`SmoothMax.posPart`).  Then:

* `u_t` is a smooth real function (`chartSmooth_smoothTruncation`): near a point
  where `u < -t - 1` (in particular near a pole, by upper semicontinuity) it is the
  constant `-t`, and near a point where `u > -t - 2` the potential is a smooth
  real function `g` and `u_t = -t + P(g + t)`;
* `θ + ddᶜu_t ≥ 0` (`isThetaPshPotential_smoothTruncation`): by the chain rule
  `ddᶜ P(g + t) = P'·ddᶜg + P''·(∂g ∧ ∂̄g)`, so
  `θ + ddᶜu_t ≥ (1 - P')θ + P'(θ + ddᶜg) ≥ 0`;
* `u_t = u` near every point where `u > -t + 1` (`eventuallyEq_smoothTruncation`).

This is the regularized form of the truncation `max(u, -t)` used to reduce mass
bounds for potentials with poles to smooth potentials.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PotentialSmoothTruncation

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.AdmissibleCurrentFormPositivity SmoothMax

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The smooth truncation `-t + P(u + t)` of an extended-real potential at level
`-t`; the inner `max` with `-t - 2` only makes the formula total at the poles and
does not change the value, since `P = 0` on `(-∞, -1]`. -/
def smoothTruncation (u : M → EReal) (t : ℝ) : M → ℝ :=
  fun x => -t + SmoothMax.posPart ((max (u x) ((-t - 2 : ℝ) : EReal)).toReal + t)

/-- On finite values the inner `max` does not change the truncation. -/
theorem posPart_max_coe (a t : ℝ) :
    SmoothMax.posPart ((max (a : EReal) ((-t - 2 : ℝ) : EReal)).toReal + t) =
      SmoothMax.posPart (a + t) := by
  rw [← Monotone.map_max EReal.coe_strictMono.monotone, EReal.toReal_coe]
  rcases le_total a (-t - 2) with h | h
  · rw [max_eq_right h, posPart_eq_zero (by linarith), posPart_eq_zero (by linarith)]
  · rw [max_eq_left h]

/-- Below the level `-t - 1` the truncation is the constant `-t`. -/
theorem posPart_max_of_lt {w : EReal} {t : ℝ} (hw : w < ((-t - 1 : ℝ) : EReal)) :
    SmoothMax.posPart ((max w ((-t - 2 : ℝ) : EReal)).toReal + t) = 0 := by
  induction w using EReal.rec with
  | bot => rw [max_eq_right bot_le, EReal.toReal_coe]; exact posPart_eq_zero (by linarith)
  | coe a =>
    rw [posPart_max_coe]
    exact posPart_eq_zero (by have := EReal.coe_lt_coe_iff.mp hw; linarith)
  | top => exact absurd hw (not_lt.mpr le_top)

/-- **The local dichotomy for the smooth truncation in a chart, in the `I-0489`
convention.**  Only the off-pole gateway
`exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt` is used: at a point
where `u` is finite the truncation is read off a smooth local expression, and near a pole
upper semicontinuity alone puts us in the constant branch. -/
theorem smoothTruncation_local_of_smoothOffPole {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ u)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) (t : ℝ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (fun y => smoothTruncation u t (e.val.symm y)) =ᶠ[𝓝 z] (fun _ => -t) ∨
      ∃ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) ∧
        chartFunction u e =ᶠ[𝓝 z] (fun y => (g y : EReal)) ∧
        (fun y => smoothTruncation u t (e.val.symm y)) =ᶠ[𝓝 z]
          fun y => -t + SmoothMax.posPart (g y + t) := by
  by_cases hlt : chartFunction u e z < ((-t - 1 : ℝ) : EReal)
  · left
    have husc : UpperSemicontinuousAt (chartFunction u e) z :=
      (hpsh.quasiPlurisubharmonic e z hz).upperSemicontinuousAt
    filter_upwards [husc _ hlt] with y hy
    simp only [smoothTruncation]
    change -t + SmoothMax.posPart ((max (chartFunction u e y) _).toReal + t) = -t
    rw [posPart_max_of_lt hy, add_zero]
  · right
    have hne : chartFunction u e z ≠ ⊥ := by
      intro h
      exact hlt (h ▸ EReal.bot_lt_coe _)
    obtain ⟨g, hg, hug⟩ :=
      exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt (hsing e z hz) hne
    refine ⟨g, hg, hug, ?_⟩
    filter_upwards [hug] with y hy
    simp only [smoothTruncation]
    change -t + SmoothMax.posPart ((max (chartFunction u e y) _).toReal + t) = _
    rw [hy, posPart_max_coe]

/-- The local dichotomy for the smooth truncation in a chart. -/
theorem smoothTruncation_local {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ u)
    (hsing : HasManifoldSmoothAnalyticSingularities (n := n) u) (t : ℝ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (fun y => smoothTruncation u t (e.val.symm y)) =ᶠ[𝓝 z] (fun _ => -t) ∨
      ∃ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) ∧
        chartFunction u e =ᶠ[𝓝 z] (fun y => (g y : EReal)) ∧
        (fun y => smoothTruncation u t (e.val.symm y)) =ᶠ[𝓝 z]
          fun y => -t + SmoothMax.posPart (g y + t) :=
  smoothTruncation_local_of_smoothOffPole hpsh hsing.smoothOffPole t e hz

/-- A chart-smooth real function has smooth analytic singularities (with the single
generator `1`). -/
theorem hasManifoldSmoothAnalyticSingularities_coe {v : M → ℝ}
    (hv : ChartSmooth (n := n) v) :
    HasManifoldSmoothAnalyticSingularities (n := n) (fun x => (v x : EReal)) := by
  intro e z hz
  refine ⟨1, 1, fun _ _ => 1, one_pos,
    ⟨univ, isOpen_univ, mem_univ _, fun _ => differentiableOn_const _⟩,
    fun y => v (e.val.symm y), ?_, ?_⟩
  · filter_upwards [e.val.open_target.mem_nhds hz] with y hy
    exact (hv e y hy).contDiffAt (e.val.open_target.mem_nhds hy)
  · refine Eventually.of_forall fun y => ?_
    have hlog : generatorLog (fun (_ : Fin 1) (_ : ComplexModel n) => (1 : ℂ)) y = 0 := by
      rw [generatorLog_of_nonzero ⟨0, one_ne_zero⟩]
      simp [generatorNormSq]
    simp [chartFunction, hlog]

/-- The smooth truncation is chart-smooth, in the bounded-remainder convention. -/
theorem chartSmooth_smoothTruncation_of_smoothOffPole {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hpsh : ThetaPlurisubharmonic θ u)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) (t : ℝ) :
    ChartSmooth (n := n) (smoothTruncation u t) := by
  intro e z hz
  refine ContDiffAt.contDiffWithinAt ?_
  rcases smoothTruncation_local_of_smoothOffPole hpsh hsing t e hz with h | ⟨g, hg, _, h⟩
  · exact contDiffAt_const.congr_of_eventuallyEq h
  · exact (contDiffAt_const.add (contDiff_posPart.contDiffAt.comp z
      (hg.self_of_nhds.add contDiffAt_const))).congr_of_eventuallyEq h

/-- The smooth truncation is chart-smooth. -/
theorem chartSmooth_smoothTruncation {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ u)
    (hsing : HasManifoldSmoothAnalyticSingularities (n := n) u) (t : ℝ) :
    ChartSmooth (n := n) (smoothTruncation u t) :=
  chartSmooth_smoothTruncation_of_smoothOffPole hpsh hsing.smoothOffPole t

omit [IsComplexManifold n M] in
/-- Near a point where `u > -t + 1` the smooth truncation agrees with `u`, in the `I-0489`
convention.  The point is off the pole set by hypothesis, so only the off-pole gateway is
needed. -/
theorem eventuallyEq_smoothTruncation_of_smoothOffPole {u : M → EReal}
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) (t : ℝ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hlt : ((-t + 1 : ℝ) : EReal) < u (e.val.symm z)) :
    (fun y => (u (e.val.symm y)).toReal) =ᶠ[𝓝 z]
      fun y => smoothTruncation u t (e.val.symm y) := by
  have hne : chartFunction u e z ≠ ⊥ := ne_bot_of_gt hlt
  obtain ⟨g, hg, hug⟩ :=
    exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt (hsing e z hz) hne
  have hgz : -t + 1 < g z := by
    have h := hug.self_of_nhds
    change u (e.val.symm z) = _ at h
    rw [h] at hlt
    exact EReal.coe_lt_coe_iff.mp hlt
  have hev : ∀ᶠ y in 𝓝 z, -t + 1 < g y :=
    hg.self_of_nhds.continuousAt.eventually (lt_mem_nhds hgz)
  filter_upwards [hug, hev] with y hy hgy
  change u (e.val.symm y) = _ at hy
  simp only [smoothTruncation]
  rw [hy, EReal.toReal_coe, posPart_max_coe, posPart_eq_self (by linarith)]
  ring

omit [IsComplexManifold n M] in
/-- Near a point where `u > -t + 1` the smooth truncation agrees with `u`. -/
theorem eventuallyEq_smoothTruncation {u : M → EReal}
    (hsing : HasManifoldSmoothAnalyticSingularities (n := n) u) (t : ℝ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hlt : ((-t + 1 : ℝ) : EReal) < u (e.val.symm z)) :
    (fun y => (u (e.val.symm y)).toReal) =ᶠ[𝓝 z]
      fun y => smoothTruncation u t (e.val.symm y) :=
  eventuallyEq_smoothTruncation_of_smoothOffPole hsing.smoothOffPole t e hz hlt

/-- For a semipositive closed `(1,1)`-form `θ`, the smooth truncation of a `θ`-psh
potential with analytic singularities in the bounded-remainder convention is again `θ`-psh. -/
theorem isThetaPshPotential_smoothTruncation_of_smoothOffPole {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hθ : θ.val.IsSemipositive) (hpsh : ThetaPlurisubharmonic θ.val u)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) (t : ℝ) :
    IsThetaPshPotential θ.val (fun x => (smoothTruncation u t x : EReal)) := by
  refine ⟨?_, fun x _ _ hx => ⟨x, hx, EReal.coe_ne_bot _⟩⟩
  rw [LocalPotentials.thetaPlurisubharmonic_smooth_iff θ _
    (chartSmooth_smoothTruncation_of_smoothOffPole hpsh hsing t)]
  intro e z hz v
  have hθz := hθ e z hz v
  rcases smoothTruncation_local_of_smoothOffPole hpsh hsing t e hz with h | ⟨g, hg, hug, h⟩
  · rw [smoothDDC_congr h, GlobalPotentialTransforms.smoothDDC_const]
    simpa using hθz
  · have hgz : ContDiffAt ℝ ∞ g z := hg.self_of_nhds
    have hg2 : ContDiffAt ℝ 2 g z := hgz.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    set φ : ℝ → ℝ := fun s => -t + SmoothMax.posPart (s + t) with hφdef
    have hφ : ContDiff ℝ ∞ φ :=
      contDiff_const.add (contDiff_posPart.comp (contDiff_id.add contDiff_const))
    have hdφ : deriv φ = fun s => trans (s + t) := by
      funext s
      exact (((hasDerivAt_posPart (s + t)).comp_add_const s t).const_add (-t)).deriv
    have hcomp : (fun y => -t + SmoothMax.posPart (g y + t)) = φ ∘ g := rfl
    have hφg2 : ContDiffAt ℝ 2 (φ ∘ g) z :=
      (hφ.contDiffAt.comp z hgz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hpos := semipositive_add_smoothDDC_of_thetaPlurisubharmonic hpsh e hz hg hug v
    rw [smoothDDC_congr h, hcomp, smoothDDC_complexDiagonal_eq_leviForm hφg2]
    rw [smoothDDC_complexDiagonal_eq_leviForm hg2] at hpos
    simp only [leviForm, realHessian_comp hφ hg2, hdφ] at hpos ⊢
    have h0 : 0 ≤ deriv (fun s => trans (s + t)) (g z) :=
      Monotone.deriv_nonneg fun a b hab => trans_monotone (by linarith)
    have h1 := trans_nonneg (g z + t)
    have h2 := trans_le_one (g z + t)
    have hpi := Real.pi_pos
    set T := (θ.val.coeff e z) ![v, Complex.I • v]
    set s := trans (g z + t)
    set d := deriv (fun s => trans (s + t)) (g z)
    set a := fderiv ℝ g z v
    set b := fderiv ℝ g z (Complex.I • v)
    set H₁ := realHessian g z v v
    set H₂ := realHessian g z (Complex.I • v) (Complex.I • v)
    have key : T + (d * (a * a) + s * H₁ + (d * (b * b) + s * H₂)) / 4 / Real.pi =
        (1 - s) * T + s * (T + (H₁ + H₂) / 4 / Real.pi) +
          d * (a * a + b * b) / 4 / Real.pi := by
      ring
    rw [key]
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hθz) (mul_nonneg h1 hpos))
      (div_nonneg (div_nonneg (mul_nonneg h0 (add_nonneg (mul_self_nonneg _)
        (mul_self_nonneg _))) (by norm_num)) hpi.le)

/-- For a semipositive closed `(1,1)`-form `θ`, the smooth truncation of a `θ`-psh
potential with smooth analytic singularities is again `θ`-psh. -/
theorem isThetaPshPotential_smoothTruncation {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hθ : θ.val.IsSemipositive) (hpsh : ThetaPlurisubharmonic θ.val u)
    (hsing : HasManifoldSmoothAnalyticSingularities (n := n) u) (t : ℝ) :
    IsThetaPshPotential θ.val (fun x => (smoothTruncation u t x : EReal)) :=
  isThetaPshPotential_smoothTruncation_of_smoothOffPole hθ hpsh hsing.smoothOffPole t

end

end SGPT.Foundations.Analysis.Pending.PotentialSmoothTruncation
