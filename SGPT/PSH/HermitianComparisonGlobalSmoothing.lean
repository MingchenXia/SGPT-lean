import Mathlib.Analysis.Calculus.MeanValue
import SGPT.PSH.HermitianProductPatches
import SGPT.PSH.HermitianComparisonMollifier
import SGPT.PSH.HermitianComparisonPositivePart
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization

/-!
# Actual bounded smooth scalar approximations for global transposition

The approximants are used as scalar weights only. A partition of ordinary
local PSH mollifiers produces globally chart-smooth functions with the
original pointwise limit. Smooth clipping supplies the required uniform
bound; no positivity or global regularization in the Hermitian class is
asserted for these auxiliary scalar functions.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalSmoothing

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar
  LocalBedfordTaylorContinuity GlobalQuasiPshSmoothLocalization ChartPartition
open Hermitian HermitianGlobalProducts HermitianComparisonMollifier
  HermitianComparisonPositivePart

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

/-- Every point has an actual open neighborhood on which global smooth
scalar functions converge pointwise to the original bounded potential. -/
theorem exists_local_smooth_scalar_approximation
    (omega : Background (m+1) M) {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (x : M) :
    ∃ (N : Opens M) (f : ℕ → M → ℝ), x ∈ N ∧
      (∀ j, ChartSmooth (n := m+1) (f j)) ∧
      ∀ y ∈ N, Tendsto (fun j => f j y) atTop (𝓝 ((u y).toReal)) := by
  obtain ⟨P, hxP⟩ := exists_backgroundPatch_containing omega x
  let e := P.geometry.chart
  let z := e.val x
  have hz : z ∈ P.geometry.domain := hxP.2
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp P.geometry.domain.isOpen z hz
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let A : Opens (ComplexModel (m+1)) := ⟨ball z r, isOpen_ball⟩
  have hcl : closure (A : Set (ComplexModel (m+1))) ⊆ closedBall z r :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  have hAD : closedBall z r ⊆ P.geometry.domain :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hball
  have hAV : A ≤ P.geometry.domain := ball_subset_closedBall.trans hAD
  have hA : RelativelyCompactIn A P.geometry.domain :=
    ⟨(isCompact_closedBall z r).of_isClosed_subset isClosed_closure hcl, hcl.trans hAD⟩
  obtain ⟨g, B, hgs, _, _, hglim, _⟩ :=
    exists_bounded_global_smooth_approximation hA (P.correctedReal_isLocallyBoundedPshOn hu hb)
  obtain ⟨β, hβs, hβ1, hβsupp⟩ := exists_cutoff isCompact_singleton A.isOpen
    (singleton_subset_iff.mpr (mem_ball_self hr))
  have hzβ : z ∈ interior {w | β w = 1} := by
    apply mem_interior_iff_mem_nhds.mpr
    exact hβ1 z (mem_singleton z)
  let V : Set (ComplexModel (m+1)) := A ∩ interior {w | β w = 1}
  have hV : IsOpen V := A.isOpen.inter isOpen_interior
  let N : Opens M := ⟨e.val.source ∩ e.val ⁻¹' V, e.val.isOpen_inter_preimage hV⟩
  let f : ℕ → M → ℝ := fun j => chartExtend e
    (fun w => β w * (g j w - P.correction w))
  have hfs : ∀ j, ChartSmooth (n := m+1) (f j) := by
    intro j
    apply chartSmooth_chartExtend e
    · exact contDiff_mul_of_tsupport_subset P.geometry.domain.isOpen hβs
        ((hgs j).contDiffOn.sub P.smooth) (hβsupp.trans hAV)
    · exact (isCompact_closedBall z r).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_mul_subset_left.trans (hβsupp.trans ball_subset_closedBall))
    · exact tsupport_mul_subset_left.trans
        (hβsupp.trans (fun w hw => P.geometry.domain_le_target (hAV hw)))
  refine ⟨N, f, ⟨hxP.1, mem_ball_self hr, hzβ⟩, hfs, ?_⟩
  intro y hy
  have hβy : β (e.val y) = 1 :=
    (interior_subset (s := {w | β w = 1}) hy.2.2)
  have heq : ∀ j, f j y = g j (e.val y) - P.correction (e.val y) := by
    intro j
    dsimp only [f]
    rw [chartExtend_of_mem hy.1, hβy, one_mul]
  have hlim := (hglim (e.val y) hy.2.1).sub_const (P.correction (e.val y))
  have hval : P.correctedReal u (e.val y) - P.correction (e.val y) = (u y).toReal := by
    change (chartFunction u e (e.val y)).toReal + P.correction (e.val y) -
      P.correction (e.val y) = _
    rw [add_sub_cancel_right, chartFunction, e.val.left_inv hy.1]
  simpa only [heq, hval] using hlim

/-- A finite smooth partition turns genuine local PSH mollifiers into
actual globally smooth scalar approximations, with the original pointwise
values. No Hermitian positivity is claimed for these auxiliary functions. -/
theorem exists_global_smooth_scalar_approximation [CompactSpace M]
    (omega : Background (m+1) M) {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    ∃ f : ℕ → M → ℝ, (∀ j, ChartSmooth (n := m+1) (f j)) ∧
      ∀ x, Tendsto (fun j => f j x) atTop (𝓝 ((u x).toReal)) := by
  classical
  choose N g hxN hgs hglim using fun x : M =>
    exists_local_smooth_scalar_approximation omega hu hb x
  obtain ⟨a, χ, idx, hχ, hχ0, hχsupp, _, hχsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m+1) N (fun x => ⟨x, hxN x⟩)
  let f : ℕ → M → ℝ := fun j x => ∑ i : Fin a, χ i x * g (idx i) j x
  refine ⟨f, fun j e => ContDiffOn.sum (fun i _ => (hχ i e).mul (hgs (idx i) j e)), ?_⟩
  intro x
  have hlim (i : Fin a) : Tendsto (fun j => χ i x * g (idx i) j x)
      atTop (𝓝 (χ i x * (u x).toReal)) := by
    by_cases hi : χ i x = 0
    · simp only [hi, zero_mul]; exact tendsto_const_nhds
    · exact (hglim (idx i) x (hχsupp i (subset_tsupport (χ i) hi))).const_mul _
  have hl := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have heq : (∑ i : Fin a, χ i x * (u x).toReal) = (u x).toReal := by
    rw [← Finset.sum_mul, hχsum x, one_mul]
  simpa only [heq] using hl

/-- A genuine smooth clipping to the interval `[0, δ]`. -/
def clipping (ε δ t : ℝ) : ℝ := cutoff ε t - cutoff ε (t - δ)

theorem clipping_mem_Icc {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (t : ℝ) :
    clipping ε δ t ∈ Icc 0 δ := by
  have hd : Differentiable ℝ (cutoff ε) := (contDiff_cutoff ε).differentiable (by simp)
  have hm : Monotone (cutoff ε) :=
    monotone_of_deriv_nonneg hd (fun x => (deriv_cutoff_mem_Icc hε x).1)
  have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ)) (f := cutoff ε) (C := 1)
    (fun x _ => hd x) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (deriv_cutoff_mem_Icc hε x).1]
      exact (deriv_cutoff_mem_Icc hε x).2)
    convex_univ (mem_univ (t-δ)) (mem_univ t)
  have he : t - (t-δ) = δ := by ring
  simp only [Real.norm_eq_abs, he, abs_of_nonneg hδ, one_mul] at hnorm
  exact ⟨sub_nonneg.mpr (hm (by linarith)), (le_abs_self _).trans hnorm⟩

/-- The actual smooth positive-part cutoffs converge for varying arguments,
by their uniform scalar error bound. -/
theorem cutoff_scale_tendsto_of_tendsto {a : ℕ → ℝ} {t : ℝ}
    (ha : Tendsto a atTop (𝓝 t)) :
    Tendsto (fun j => cutoff (scale j) (a j)) atTop (𝓝 (max t 0)) := by
  have hm : Tendsto (fun j => max (a j) 0) atTop (𝓝 (max t 0)) :=
    ha.max tendsto_const_nhds
  have hl := hm.sub scale_tendsto
  have hr := hm.add scale_tendsto
  simp only [sub_zero, add_zero] at hl hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr
    (fun j => (cutoff_bounds (scale_pos j) (a j)).1)
    (fun j => (cutoff_bounds (scale_pos j) (a j)).2)

/-- Actual globally smooth weights converge pointwise to the bounded
positive difference of two original Hermitian potentials. Their bounds are
exactly `[0, δ]`, so they can be inserted into global current transposition
and its actual density dominated-convergence extension. -/
theorem exists_bounded_smooth_positive_difference [CompactSpace M]
    (omega : Background (m+1) M) {u v : M → EReal}
    (hu : IsHermitianPSH omega u) (hv : IsHermitianPSH omega v)
    (hub : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (hvb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v x ∧ v x ≤ (b : EReal))
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : ∀ x, max ((v x).toReal - (u x).toReal) 0 ≤ δ) :
    ∃ f : ℕ → M → ℝ, (∀ j, ChartSmooth (n := m+1) (f j)) ∧
      (∀ j x, f j x ∈ Icc 0 δ) ∧
      ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (max ((v x).toReal - (u x).toReal) 0)) := by
  obtain ⟨a, has, halim⟩ := exists_global_smooth_scalar_approximation omega hu hub
  obtain ⟨b, hbs, hblim⟩ := exists_global_smooth_scalar_approximation omega hv hvb
  let f : ℕ → M → ℝ := fun j x => clipping (scale j) δ (b j x - a j x)
  refine ⟨f, ?_, fun j x => clipping_mem_Icc (scale_pos j) hδ _, ?_⟩
  · intro j e
    have hs := (hbs j e).sub (has j e)
    exact ((contDiff_cutoff (scale j)).comp_contDiffOn hs).sub
      ((contDiff_cutoff (scale j)).comp_contDiffOn (hs.sub contDiffOn_const))
  · intro x
    have hl := (hblim x).sub (halim x)
    have h1 := cutoff_scale_tendsto_of_tendsto hl
    have h2 := cutoff_scale_tendsto_of_tendsto (hl.sub_const δ)
    have hnonpos : (v x).toReal - (u x).toReal - δ ≤ 0 := by
      linarith [le_max_left ((v x).toReal - (u x).toReal) 0, hgap x]
    have h := h1.sub h2
    simpa only [f, clipping, max_eq_right hnonpos, sub_zero] using h

end SGPT.PSH.HermitianComparisonGlobalSmoothing
