import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A nonzero section from finite products of close projections

An actual smooth family of idempotent operators on a coordinate ball produces
a smooth nowhere-zero vector in its image on every smaller ball.  The proof
uses uniform continuity on the compact smaller closed ball and a finite radial
subdivision; it requires no ODE, connection, or parallel-transport assumption.

This is the projection-product producer in `siu-uniform-generation.tex`, node
`siu-uniform:projection-frame`.  The bundle application must still construct
the actual projector from its finite atlas frames and partition of unity.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nearby projection cannot kill a nonzero vector fixed by the old one.
Neither self-adjointness nor orthogonality is needed. -/
theorem apply_ne_zero_of_close_projection {A B : E →L[ℝ] E} {v : E}
    (hAv : A v = v) (hv : v ≠ 0) (hclose : ‖B - A‖ < 1) : B v ≠ 0 := by
  intro hBv
  have hbound := (B - A).le_opNorm v
  have heq : (B - A) v = -v := by simp only [sub_apply, hBv, hAv, zero_sub]
  rw [heq, norm_neg] at hbound
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

/-- A radial affine map in one fixed coordinate chart. -/
def radialPoint (c : ComplexModel n) (t : ℝ) (z : ComplexModel n) : ComplexModel n :=
  c + t • (z - c)

theorem contDiff_radialPoint (c : ComplexModel n) (t : ℝ) :
    ContDiff ℝ ∞ (radialPoint c t) := by
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul t)

theorem radialPoint_mem_closedBall (c : ComplexModel n) {r t : ℝ}
    (hr : 0 ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) {z : ComplexModel n}
    (hz : z ∈ closedBall c r) : radialPoint c t z ∈ closedBall c r :=
  (convex_closedBall c r).add_smul_sub_mem (mem_closedBall_self hr) hz ht

/-- A literal finite sequence of radial projection products. -/
def radialProjectionProduct (P : ComplexModel n → E →L[ℝ] E)
    (c : ComplexModel n) (N : ℕ) (v₀ : E) : ℕ → ComplexModel n → E
  | 0 => fun _ => v₀
  | j + 1 => fun z => P (radialPoint c (((j + 1 : ℕ) : ℝ) / N) z)
      (radialProjectionProduct P c N v₀ j z)

/-- The finite products are smooth wherever all their radial arguments remain
in the given larger ball. -/
theorem contDiffOn_radialProjectionProduct
    (P : ComplexModel n → E →L[ℝ] E) (c : ComplexModel n)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hP : ContDiffOn ℝ ∞ P (ball c R)) {N : ℕ} (hN : 0 < N) (v₀ : E) :
    ∀ j : ℕ, j ≤ N → ContDiffOn ℝ ∞ (radialProjectionProduct P c N v₀ j) (ball c r) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  intro j
  induction j with
  | zero => intro _; exact contDiffOn_const
  | succ j ih =>
      intro hj
      have ht : (((j + 1 : ℕ) : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
        refine ⟨by positivity, (div_le_one hNreal).mpr ?_⟩
        exact_mod_cast hj
      have hmaps : MapsTo (radialPoint c (((j + 1 : ℕ) : ℝ) / N)) (ball c r) (ball c R) :=
        fun z hz => (closedBall_subset_ball hrR)
          (radialPoint_mem_closedBall c hr ht (ball_subset_closedBall hz))
      exact (hP.comp (contDiff_radialPoint c _).contDiffOn hmaps).clm_apply (ih (by omega))

/-- Uniform continuity of the actual projector gives one finite radial
subdivision valid for every endpoint in the smaller closed ball. -/
theorem exists_radial_projection_subdivision
    (P : ComplexModel n → E →L[ℝ] E) (c : ComplexModel n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hP : ContinuousOn P (ball c R)) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ closedBall c r, ∀ j : ℕ, j < N →
      ‖P (radialPoint c (((j + 1 : ℕ) : ℝ) / N) z) -
        P (radialPoint c ((j : ℝ) / N) z)‖ < 1 := by
  have huc := (isCompact_closedBall c r).uniformContinuousOn_of_continuous
    (hP.mono (closedBall_subset_ball hrR))
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.mp huc (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (r / δ) 0)
  have hN0real : (0 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hN0 : 0 < N := by exact_mod_cast hN0real
  have hrNδ : r / N < δ := by
    have h1 : r / δ < N := (le_max_left _ _).trans_lt hN
    have h2 : r < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp h1
    exact (div_lt_iff₀ hN0real).mpr (by nlinarith)
  refine ⟨N, hN0, fun z hz j hj => ?_⟩
  have ht₀ : ((j : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hN0real).mpr ?_⟩
    exact_mod_cast hj.le
  have ht₁ : (((j + 1 : ℕ) : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hN0real).mpr ?_⟩
    exact_mod_cast Nat.succ_le_iff.mpr hj
  have hdist : dist (radialPoint c (((j + 1 : ℕ) : ℝ) / N) z)
      (radialPoint c ((j : ℝ) / N) z) < δ := by
    have hcoef : (((j + 1 : ℕ) : ℝ) / N) - (j : ℝ) / N = 1 / (N : ℝ) := by
      push_cast
      ring
    have hdiff : radialPoint c (((j + 1 : ℕ) : ℝ) / N) z -
        radialPoint c ((j : ℝ) / N) z =
        ((((j + 1 : ℕ) : ℝ) / N) - (j : ℝ) / N) • (z - c) := by
      dsimp [radialPoint]
      module
    rw [dist_eq_norm, hdiff, hcoef, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (1 / (N : ℝ)) * ‖z - c‖ ≤ (1 / (N : ℝ)) * r :=
          mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hz)
            (by positivity)
      _ < δ := by simpa only [one_div, ← div_eq_mul_inv, mul_comm] using hrNδ
  have hnear := hδP _ (radialPoint_mem_closedBall c hr.le ht₁ hz)
    _ (radialPoint_mem_closedBall c hr.le ht₀ hz) hdist
  rw [dist_eq_norm] at hnear
  exact hnear.trans (by norm_num)

/-- Actual smooth idempotents produce an actual smooth nowhere-zero vector in
their images on the smaller ball, with no assumed output section or transport.
The number of projection factors may depend on this family. -/
theorem exists_smooth_nonzero_fixedVector_on_ball
    (P : ComplexModel n → E →L[ℝ] E) (c : ComplexModel n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hP : ContDiffOn ℝ ∞ P (ball c R))
    (hPid : ∀ z ∈ ball c R, ∀ v : E, P z (P z v) = P z v)
    (v₀ : E) (hv₀ : v₀ ≠ 0) (hfix₀ : P c v₀ = v₀) :
    ∃ v : ComplexModel n → E, ContDiffOn ℝ ∞ v (ball c r) ∧
      ∀ z ∈ ball c r, v z ≠ 0 ∧ P z (v z) = v z := by
  obtain ⟨N, hN, hnear⟩ := exists_radial_projection_subdivision P c hr hrR hP.continuousOn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfixed : ∀ j : ℕ, j ≤ N → ∀ z ∈ closedBall c r,
      P (radialPoint c ((j : ℝ) / N) z) (radialProjectionProduct P c N v₀ j z) =
        radialProjectionProduct P c N v₀ j z ∧ radialProjectionProduct P c N v₀ j z ≠ 0 := by
    intro j
    induction j with
    | zero => intro _ z _; simpa only [Nat.cast_zero, zero_div, radialPoint, zero_smul,
        add_zero, radialProjectionProduct] using And.intro hfix₀ hv₀
    | succ j ih =>
        intro hj z hz
        obtain ⟨hfix, hne⟩ := ih (by omega) z hz
        have ht : (((j + 1 : ℕ) : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
          refine ⟨by positivity, (div_le_one hNr).mpr ?_⟩
          exact_mod_cast hj
        have hmem : radialPoint c (((j + 1 : ℕ) : ℝ) / N) z ∈ ball c R :=
          closedBall_subset_ball hrR (radialPoint_mem_closedBall c hr.le ht hz)
        exact ⟨hPid _ hmem _, apply_ne_zero_of_close_projection hfix hne
          (hnear z hz j (by omega))⟩
  refine ⟨radialProjectionProduct P c N v₀ N,
    contDiffOn_radialProjectionProduct P c hr.le hrR hP hN v₀ N le_rfl, fun z hz => ?_⟩
  have h := hfixed N le_rfl z (ball_subset_closedBall hz)
  have hpoint : radialPoint c ((N : ℝ) / N) z = z := by
    simp [radialPoint, div_self hNr.ne']
  rw [hpoint] at h
  exact h.symm

end SGPT.Bergman.SiuUniformGeneration
