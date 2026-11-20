import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

/-!
# The method of continuity

Let `X` be a real Banach space, `Y` a real normed space and `T₀, T₁ : X →ₗ[ℝ] Y` linear maps whose
difference is bounded, `‖T₁ u - T₀ u‖ ≤ K ‖u‖`.  Put `T_t = T₀ + t (T₁ - T₀)`.  If there is a
uniform estimate `‖u‖ ≤ C ‖T_t u‖` for all `t ∈ [0, 1]` and `T₀` is onto, then `T₁` is onto
(`surjective_of_continuity`; Gilbarg--Trudinger, Theorem 5.2).

Proof: if `T_s` is onto and `|t - s| ≤ δ = 1 / (2 (C + 1) (K + 1))`, then for every `f` the map
`u ↦ T_s⁻¹ (f - (t - s)(T₁ - T₀) u)` (any right inverse; the estimate makes it unique) is a
contraction of `X` with constant `1/2`, whose fixed point solves `T_t u = f`; finitely many steps
of length `δ` lead from `0` to `1`.

Used for the solvability of `L u - μ u = f` on the whole space (TN.4 B5 linear track L2.10,
the linear elliptic estimates; blueprint
`bou:kahler-laplacian-solvability`).
-/

noncomputable section

open Set

namespace SGPT.Foundations.Analysis.Pending.MethodOfContinuity

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- One step of the method of continuity. -/
theorem surjective_step (T₀ T₁ : X →ₗ[ℝ] Y) {C K s t : ℝ} (hC0 : 0 ≤ C)
    (hK : ∀ u, ‖T₁ u - T₀ u‖ ≤ K * ‖u‖)
    (hCs : ∀ u, ‖u‖ ≤ C * ‖T₀ u + s • (T₁ u - T₀ u)‖)
    (hs : Function.Surjective fun u => T₀ u + s • (T₁ u - T₀ u))
    (hst : |t - s| * (C * K) ≤ 1 / 2) :
    Function.Surjective fun u => T₀ u + t • (T₁ u - T₀ u) := by
  intro f
  set Ts : X → Y := fun u => T₀ u + s • (T₁ u - T₀ u) with hTs
  have hTs_sub : ∀ u v, Ts u - Ts v = Ts (u - v) := fun u v => by
    simp only [hTs, map_sub, smul_sub]; abel
  choose R hR using hs
  set Φ : X → X := fun u => R (f - (t - s) • (T₁ u - T₀ u)) with hΦ
  have hlip : ∀ u v, ‖Φ u - Φ v‖ ≤ (1 / 2) * ‖u - v‖ := fun u v => by
    have h1 := hCs (Φ u - Φ v)
    have h2 : Ts (Φ u - Φ v) = (t - s) • ((T₁ v - T₀ v) - (T₁ u - T₀ u)) := by
      rw [← hTs_sub]
      simp only [hΦ]
      rw [hR, hR, sub_sub_sub_cancel_left, ← smul_sub]
    change ‖Φ u - Φ v‖ ≤ C * ‖Ts (Φ u - Φ v)‖ at h1
    rw [h2, norm_smul, Real.norm_eq_abs] at h1
    have h3 : (T₁ v - T₀ v) - (T₁ u - T₀ u) = -(T₁ (u - v) - T₀ (u - v)) := by
      simp only [map_sub]; abel
    rw [h3, norm_neg] at h1
    have h4 := hK (u - v)
    calc ‖Φ u - Φ v‖ ≤ C * (|t - s| * ‖T₁ (u - v) - T₀ (u - v)‖) := h1
      _ ≤ C * (|t - s| * (K * ‖u - v‖)) := by gcongr
      _ = (|t - s| * (C * K)) * ‖u - v‖ := by ring
      _ ≤ (1 / 2) * ‖u - v‖ := by gcongr
  have hcon : ContractingWith (1 / 2 : NNReal) Φ := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    simpa using hlip u v
  set u := ContractingWith.fixedPoint Φ hcon with hu
  have hfix : Φ u = u := ContractingWith.fixedPoint_isFixedPt hcon
  refine ⟨u, ?_⟩
  have h := hR (f - (t - s) • (T₁ u - T₀ u))
  change Ts (Φ u) = _ at h
  rw [hfix] at h
  simp only [hTs] at h
  change T₀ u + t • (T₁ u - T₀ u) = f
  rw [show t = s + (t - s) by ring, add_smul, ← add_assoc, h]
  abel

/-- **The method of continuity** (Gilbarg--Trudinger, Theorem 5.2). -/
theorem surjective_of_continuity (T₀ T₁ : X →ₗ[ℝ] Y) {C K : ℝ} (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hK : ∀ u, ‖T₁ u - T₀ u‖ ≤ K * ‖u‖)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ C * ‖T₀ u + t • (T₁ u - T₀ u)‖)
    (h0 : Function.Surjective T₀) : Function.Surjective T₁ := by
  set δ : ℝ := 1 / (2 * (C * K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδCK : δ * (C * K) ≤ 1 / 2 := by
    rw [hδ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hC0 hK0]
  have hstep : ∀ n : ℕ, Function.Surjective fun u => T₀ u + min (n * δ) 1 • (T₁ u - T₀ u) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      rw [min_eq_left zero_le_one]
      simpa using h0
    | succ n ih =>
      refine surjective_step T₀ T₁ hC0 hK (s := min (n * δ) 1)
        (hC _ ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩) ih ?_
      have hle : |min (((n + 1 : ℕ) : ℝ) * δ) 1 - min (n * δ) 1| ≤ δ := by
        rw [abs_le]
        constructor
        · have : min (n * δ) 1 ≤ min (((n + 1 : ℕ) : ℝ) * δ) 1 :=
            min_le_min_right _ (by push_cast; nlinarith)
          linarith
        · have h1 : min (((n + 1 : ℕ) : ℝ) * δ) 1 ≤ min (n * δ) 1 + δ := by
            rcases le_total ((n : ℝ) * δ) 1 with h | h
            · rw [min_eq_left h]; push_cast
              exact (min_le_left _ _).trans (by linarith)
            · rw [min_eq_right h]
              exact (min_le_right _ _).trans (by linarith)
          linarith
      calc |min (((n + 1 : ℕ) : ℝ) * δ) 1 - min (n * δ) 1| * (C * K) ≤ δ * (C * K) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg hC0 hK0)
        _ ≤ 1 / 2 := hδCK
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / δ)
  have hNδ : 1 ≤ (N : ℝ) * δ := by
    rwa [div_le_iff₀ hδ0] at hN
  have h1 := hstep N
  rw [min_eq_right hNδ] at h1
  intro f
  obtain ⟨u, hu⟩ := h1 f
  exact ⟨u, by simpa using hu⟩

end SGPT.Foundations.Analysis.Pending.MethodOfContinuity
