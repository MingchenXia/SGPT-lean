import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold

set_option autoImplicit false

/-!
# Regularization of a Kähler current from a quasi-equisingular approximation

Source: Demailly, *Regularization of closed positive currents and intersection
theory* (1992); SGPT, Theorem 1.6.2; Copy-4, `sec:prelim` (the paragraph defining
analytic singularities of type `(c, 𝔞)` with a BOUNDED remainder) and `sec:nK`;
blueprint `ana:regularization-kahler-current`.

Let `T = θ + ddᶜu ≥ ω₀` be a Kähler current on a compact complex manifold.  A
quasi-equisingular approximation `(u_k)` of `u`
(`Pending.QuasiEquisingularApproximation.exists_quasiEquisingularApproximation`)
decreases to `u`, has `u_k ∈ PSH(θ + ε_k ω₀)` with `ε_k ↓ 0`, and each `u_k` has
analytic singularity type in every chart.  For `ε_k < 1` the current
`θ + ddᶜu_k` dominates the Kähler form `(1 - ε_k) ω₀`, so it is again a Kähler
current in the same class; its poles have positive Lelong number, and `u_k ≥ u`
makes those Lelong numbers at most those of `u`.

This is exactly the conclusion of
`Pending.KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`
EXCEPT for the presentation conventions: here the singularities are the chartwise
bounded-remainder ones of `HasManifoldAnalyticSingularityType` (the convention in
which Copy-4 and SGPT state the theorem), not the global coherent type
`HasAnalyticSingularities` nor the chartwise SMOOTH remainder
`HasManifoldSmoothAnalyticSingularities` of CT22.  That theorem is proved
separately, in its own convention.

Everything here is sorry-free: the approximation step
`Pending.QuasiEquisingularApproximation.exists_quasiEquisingularApproximation` (Xia SGPT
Theorem 1.6.2) is proved from Demailly's approximation theorem in
`Pending.QuasiEquisingularApproximationDemailly`.  No module in the root import closure
imports this file.
-/

open Set Filter
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularKahlerCurrent

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section GeneratorBound

variable {N : ℕ} {f : Fin N → ComplexModel n → ℂ} {z : ComplexModel n}

/-- A finite family of holomorphic functions vanishing at `z` is dominated near
`z` by a multiple of `‖w - z‖²`. -/
theorem exists_generatorNormSq_le (hf : HolomorphicGeneratorsAt f z)
    (hz : ∀ j, f j z = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ w in 𝓝 z, generatorNormSq f w ≤ A * ‖w - z‖ ^ 2 := by
  classical
  obtain ⟨U, hU, hzU, hdiff⟩ := hf
  have hbound : ∀ j : Fin N, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ w in 𝓝 z, ‖f j w‖ ^ 2 ≤ c * ‖w - z‖ ^ 2 := by
    intro j
    have hdj : DifferentiableAt ℂ (f j) z :=
      (hdiff j).differentiableAt (hU.mem_nhds hzU)
    obtain ⟨c, hc, hcw⟩ :=
      (hdj.restrictScalars ℝ).hasFDerivAt.isBigO_sub.exists_pos
    refine ⟨c ^ 2, by positivity, ?_⟩
    filter_upwards [hcw.bound] with w hw
    have hw' : ‖f j w‖ ≤ c * ‖w - z‖ := by simpa [hz j] using hw
    have h0 : 0 ≤ ‖f j w‖ := norm_nonneg _
    have h1 : 0 ≤ ‖w - z‖ := norm_nonneg _
    nlinarith [hw', h0, h1]
  choose c hc hcbound using hbound
  have hcsum : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => (hc j).le
  refine ⟨(∑ j, c j) + 1, by linarith, ?_⟩
  have hall : ∀ᶠ w in 𝓝 z, ∀ j, ‖f j w‖ ^ 2 ≤ c j * ‖w - z‖ ^ 2 :=
    Filter.eventually_all.mpr hcbound
  filter_upwards [hall] with w hw
  have hsum : ∑ j, ‖f j w‖ ^ 2 ≤ ∑ j, c j * ‖w - z‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => hw j
  have hfinal : ∑ j, c j * ‖w - z‖ ^ 2 = (∑ j, c j) * ‖w - z‖ ^ 2 := by
    rw [← Finset.sum_mul]
  have hnn : (0 : ℝ) ≤ ‖w - z‖ ^ 2 := by positivity
  calc generatorNormSq f w = ∑ j, ‖f j w‖ ^ 2 := rfl
    _ ≤ (∑ j, c j) * ‖w - z‖ ^ 2 := by rw [← hfinal]; exact hsum
    _ ≤ ((∑ j, c j) + 1) * ‖w - z‖ ^ 2 := by nlinarith

/-- A finite family of holomorphic functions vanishing at `z` has
`log ∑ |f_j|² ≤ 2 log ‖w - z‖ + C` near `z`. -/
theorem exists_generatorLog_le (hf : HolomorphicGeneratorsAt f z)
    (hz : ∀ j, f j z = 0) :
    ∃ C : ℝ, ∀ᶠ w in 𝓝 z,
      generatorLog f w ≤ ((2 * Real.log ‖w - z‖ + C : ℝ) : EReal) := by
  obtain ⟨A, hA, hAle⟩ := exists_generatorNormSq_le hf hz
  refine ⟨Real.log A, ?_⟩
  filter_upwards [hAle] with w hw
  by_cases hbot : generatorLog f w = ⊥
  · rw [hbot]; exact bot_le
  have hne : ∃ j, f j w ≠ 0 := by
    by_contra hcon
    exact hbot ((generatorLog_eq_bot_iff f w).mpr
      fun j => not_not.mp fun h => hcon ⟨j, h⟩)
  have hpos : 0 < generatorNormSq f w := by
    obtain ⟨j, hj⟩ := hne
    have hjpos : 0 < ‖f j w‖ ^ 2 := by positivity
    exact lt_of_lt_of_le hjpos
      (Finset.single_le_sum (f := fun j => ‖f j w‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ j))
  have hwz : 0 < ‖w - z‖ := by
    rcases lt_or_eq_of_le (norm_nonneg (w - z)) with h | h
    · exact h
    · exact absurd (hpos.trans_le hw) (by rw [← h]; simp)
  rw [generatorLog_of_nonzero hne]
  refine EReal.coe_le_coe_iff.mpr ?_
  have hlog : Real.log (generatorNormSq f w) ≤ Real.log (A * ‖w - z‖ ^ 2) :=
    Real.log_le_log hpos hw
  have hsplit : Real.log (A * ‖w - z‖ ^ 2) = Real.log A + 2 * Real.log ‖w - z‖ := by
    rw [Real.log_mul hA.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  linarith [hlog, hsplit.le, hsplit.ge]

end GeneratorBound

/-- **A pole of a potential with analytic singularity type has positive Lelong
number.**  Only the chartwise bounded-remainder convention is used. -/
theorem lelongNumber_pos_of_hasAnalyticSingularityTypeAt {u : M → EReal} {x : M}
    (htype : HasAnalyticSingularityTypeAt
      (chartFunction u (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x))
    (hx : u x = ⊥) : 0 < lelongNumber (n := n) u x := by
  classical
  set e := complexChartAt (n := n) x with he
  set z := e.val x with hzdef
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hchart : chartFunction u e z = u x := by
    simp only [chartFunction, hzdef, e.val.left_inv hxsrc]
  obtain ⟨c, N, f, hlog⟩ := htype
  obtain ⟨hc, hgen, b, hb, heq⟩ := hlog
  have hfz : ∀ j, f j z = 0 :=
    (LogarithmicTypeAt.eq_bot_iff ⟨hc, hgen, b, hb, heq⟩).mp (by rw [hchart]; exact hx)
  obtain ⟨C, hC⟩ := exists_generatorLog_le hgen hfz
  obtain ⟨Cb, _, hCb⟩ := hb
  -- the coordinate bound
  have hcoord : ∀ᶠ w in 𝓝 z, chartFunction u e w ≤
      (((c : ℝ) * (2 * Real.log ‖w - z‖ + C) + Cb : ℝ) : EReal) := by
    filter_upwards [hC, hCb, heq] with w h1 h2 h3
    rw [h3]
    by_cases hbot : generatorLog f w = ⊥
    · rw [hbot, EReal.mul_bot_of_pos (by exact_mod_cast EReal.coe_pos.mpr hc)]
      simp
    have hne : generatorLog f w ≠ ⊤ := generatorLog_ne_top f w
    lift generatorLog f w to ℝ using ⟨hne, hbot⟩ with s hs
    rw [← EReal.coe_mul, ← EReal.coe_add]
    refine EReal.coe_le_coe_iff.mpr ?_
    have hs' : s ≤ 2 * Real.log ‖w - z‖ + C := EReal.coe_le_coe_iff.mp (hs ▸ h1)
    have hb' : b w ≤ Cb := (abs_le.mp h2).2
    nlinarith [hs', hb', hc]
  -- transport to the manifold
  refine LelongNumberComparison.lelongNumber_pos_of_le_log
    (γ := 2 * c) (C := (c : ℝ) * C + Cb) (by positivity) ?_
  have hcont : ContinuousAt e.val x := e.val.continuousAt hxsrc
  have hpull : ∀ᶠ y in 𝓝 x, chartFunction u e (e.val y) ≤
      (((c : ℝ) * (2 * Real.log ‖e.val y - z‖ + C) + Cb : ℝ) : EReal) :=
    hcont.eventually hcoord
  refine eventually_nhdsWithin_of_eventually_nhds ?_
  filter_upwards [hpull, e.val.open_source.mem_nhds hxsrc] with y h1 h2
  have hy : chartFunction u e (e.val y) = u y := by
    simp only [chartFunction, e.val.left_inv h2]
  rw [hy] at h1
  refine h1.trans (EReal.coe_le_coe_iff.mpr ?_)
  have : ‖e.val y - z‖ = ‖(complexChartAt (n := n) x).val y
      - (complexChartAt (n := n) x).val x‖ := by rw [he, hzdef]
  rw [this]
  ring_nf
  exact le_rfl

/-- **Demailly regularization in the bounded convention.**  Every Kähler current
on a compact complex manifold is dominated by a Kähler current in the same class
with chartwise analytic singularity type whose poles lie in the set where the
original current has positive Lelong number.

Proved from the quasi-equisingular approximation theorem
(`Pending.QuasiEquisingularApproximation.exists_quasiEquisingularApproximation`). -/
theorem exists_kahlerCurrent_analyticSingularityType_poleSet_subset [CompactSpace M]
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) :
    ∃ S : KahlerCurrent alpha,
      HasManifoldAnalyticSingularityType (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  classical
  obtain ⟨ε, uSeq, happ⟩ :=
    QuasiEquisingularApproximation.exists_quasiEquisingularApproximation
      T.lowerBound (T.representative - T.lowerBound.form) T.strictlyPsh
  obtain ⟨k, hk⟩ :=
    (happ.error_tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  have hpos : (0 : ℝ) < 1 - ε k := by linarith
  -- the approximant is a Kähler current in the same class
  have hform : (T.representative - T.lowerBound.form) + ε k • T.lowerBound.form =
      T.representative - (1 - ε k) • T.lowerBound.form := by
    rw [sub_smul, one_smul]
    abel
  refine ⟨{ representative := T.representative
            represents := T.represents
            potential := uSeq k
            lowerBound := PositiveClasses.KahlerBackground.smul hpos T.lowerBound
            strictlyPsh := by
              have h := happ.term k
              rw [hform] at h
              simpa only [PositiveClasses.KahlerBackground.smul_form] using h },
          happ.term_hasAnalyticSingularityType k, ?_⟩
  -- poles have positive Lelong number, bounded by those of the original potential
  intro x hx
  have hxbot : uSeq k x = ⊥ := hx
  have hpos' : 0 < lelongNumber (n := n) (uSeq k) x :=
    lelongNumber_pos_of_hasAnalyticSingularityTypeAt
      (happ.term_hasAnalyticSingularityType k (complexChartAt (n := n) x)
        ((complexChartAt (n := n) x).val x)
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)))
      hxbot
  have hle : ∀ y, T.potential y ≤ uSeq k y := by
    intro y
    refine le_of_tendsto (happ.term_tendsto y) ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact happ.term_antitone y hm
  exact lt_of_lt_of_le hpos'
    (KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (Filter.Eventually.of_forall fun y => hle y))

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularKahlerCurrent
