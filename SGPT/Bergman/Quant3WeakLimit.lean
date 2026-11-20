import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Weak limits from one-sided comparisons

Measure-theoretic bookkeeping for the proofs of `prop:mainKahcurr` and `thm:pBMconvergence`
(`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`, lines 1211--1288).

The book argues with weak cluster points `τ` of the partial Bergman measures: it proves
`τ ≤ θⁿ_P` (resp. `θⁿ_P ≤ τ`) as measures and concludes by comparing total masses. We use the
equivalent test-function form, which avoids compactness of sets of measures and the passage from
continuous test functions to Borel sets:

* `tendsto_integral_of_eventually_le_of_mass`: if `∫ w dβ_k ≤ ∫ w dν + ε` eventually for every
  continuous `w ≥ 0` and every `ε > 0`, and the masses `β_k(X) → ν(X)`, then `β_k ⇀ ν`;
* `tendsto_integral_of_eventually_ge_of_mass`: the same with `∫ w dν - ε ≤ ∫ w dβ_k`;
* `eventually_integral_le_of_le_of_tendsto` / `eventually_integral_ge_of_ge_of_tendsto`: the
  one-sided bounds, when `β_k ≤ γ_{j,k}` (resp. `γ_{j,k} ≤ β_k`), `γ_{j,k} ⇀ ν_j` as `k → ∞` and
  `ν_j ⇀ ν` as `j → ∞` (the book's "`τ ≤ θⁿ_{P_j}` for every `j`, and `θⁿ_{P_j} ⇀ θⁿ_P`").
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.Quant3

open MeasureTheory Filter Set
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- A continuous function on a compact space is integrable for every finite measure. -/
theorem integrable_continuousMap (ν : Measure X) [IsFiniteMeasure ν] (w : C(X, ℝ)) :
    Integrable w ν :=
  (BoundedContinuousFunction.mkOfCompact w).integrable ν

/-- `∫ (w + c) dν = ∫ w dν + c ν(X)`. -/
theorem integral_add_const_continuousMap (ν : Measure X) [IsFiniteMeasure ν] (w : C(X, ℝ))
    (c : ℝ) : ∫ x, (w x + c) ∂ν = ∫ x, w x ∂ν + (ν univ).toReal * c := by
  rw [integral_add (integrable_continuousMap ν w) (integrable_const c), integral_const,
    smul_eq_mul]
  rfl

/-- `∫ (c - w) dν = c ν(X) - ∫ w dν`. -/
theorem integral_const_sub_continuousMap (ν : Measure X) [IsFiniteMeasure ν] (w : C(X, ℝ))
    (c : ℝ) : ∫ x, (c - w x) ∂ν = (ν univ).toReal * c - ∫ x, w x ∂ν := by
  rw [integral_sub (integrable_const c) (integrable_continuousMap ν w), integral_const,
    smul_eq_mul]
  rfl

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- The functions `w + ‖w‖` and `‖w‖ - w` are nonnegative. -/
theorem norm_add_nonneg_continuousMap (w : C(X, ℝ)) :
    0 ≤ w + ContinuousMap.const X ‖w‖ ∧ 0 ≤ ContinuousMap.const X ‖w‖ - w := by
  have h x := abs_le.mp ((Real.norm_eq_abs (w x)).symm ▸ w.norm_coe_le_norm x)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change (0 : ℝ) ≤ w x + ‖w‖
    linarith [(h x).1]
  · change (0 : ℝ) ≤ ‖w‖ - w x
    linarith [(h x).2]

/-- **Weak convergence from upper bounds and convergence of masses.** If `∫ w dβ_k ≤ ∫ w dν + ε`
eventually for every continuous `w ≥ 0` and `ε > 0`, and `β_k(X) → ν(X)`, then
`∫ w dβ_k → ∫ w dν` for every continuous `w`. -/
theorem tendsto_integral_of_eventually_le_of_mass (β : ℕ → Measure X) (ν : Measure X)
    [IsFiniteMeasure ν] (hfin : ∀ᶠ k in atTop, IsFiniteMeasure (β k))
    (hmass : Tendsto (fun k => (β k univ).toReal) atTop (𝓝 (ν univ).toReal))
    (hup : ∀ w : C(X, ℝ), 0 ≤ w → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∫ x, w x ∂β k ≤ ∫ x, w x ∂ν + ε)
    (w : C(X, ℝ)) : Tendsto (fun k => ∫ x, w x ∂β k) atTop (𝓝 (∫ x, w x ∂ν)) := by
  have hc0 : 0 ≤ ‖w‖ := norm_nonneg w
  obtain ⟨h₁, h₂⟩ := norm_add_nonneg_continuousMap w
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hmc : ∀ᶠ k in atTop, |(β k univ).toReal - (ν univ).toReal| * ‖w‖ < ε / 3 := by
    have hm := (hmass.sub_const (ν univ).toReal).abs.mul_const ‖w‖
    simp only [sub_self, abs_zero, zero_mul] at hm
    exact hm.eventually (gt_mem_nhds hε3)
  have hA := hup _ h₁ (ε / 3) hε3
  have hB := hup _ h₂ (ε / 3) hε3
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hfin.and (hmc.and (hA.and hB)))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hN k hk
  have := hk1
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply] at hk3 hk4
  rw [integral_add_const_continuousMap, integral_add_const_continuousMap] at hk3
  rw [integral_const_sub_continuousMap, integral_const_sub_continuousMap] at hk4
  rw [Real.dist_eq, abs_lt]
  have hk2' : |((β k univ).toReal - (ν univ).toReal) * ‖w‖| < ε / 3 := by
    rwa [abs_mul, abs_of_nonneg hc0]
  have hk2'' := abs_lt.mp hk2'
  have hexp : ((β k univ).toReal - (ν univ).toReal) * ‖w‖ =
      (β k univ).toReal * ‖w‖ - (ν univ).toReal * ‖w‖ := by ring
  rw [hexp] at hk2''
  constructor <;> linarith [hk2''.1, hk2''.2]

/-- **Weak convergence from lower bounds and convergence of masses.** If `∫ w dν - ε ≤ ∫ w dβ_k`
eventually for every continuous `w ≥ 0` and `ε > 0`, and `β_k(X) → ν(X)`, then
`∫ w dβ_k → ∫ w dν` for every continuous `w`. -/
theorem tendsto_integral_of_eventually_ge_of_mass (β : ℕ → Measure X) (ν : Measure X)
    [IsFiniteMeasure ν] (hfin : ∀ᶠ k in atTop, IsFiniteMeasure (β k))
    (hmass : Tendsto (fun k => (β k univ).toReal) atTop (𝓝 (ν univ).toReal))
    (hlow : ∀ w : C(X, ℝ), 0 ≤ w → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∫ x, w x ∂ν - ε ≤ ∫ x, w x ∂β k)
    (w : C(X, ℝ)) : Tendsto (fun k => ∫ x, w x ∂β k) atTop (𝓝 (∫ x, w x ∂ν)) := by
  have hc0 : 0 ≤ ‖w‖ := norm_nonneg w
  obtain ⟨h₁, h₂⟩ := norm_add_nonneg_continuousMap w
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hmc : ∀ᶠ k in atTop, |(β k univ).toReal - (ν univ).toReal| * ‖w‖ < ε / 3 := by
    have hm := (hmass.sub_const (ν univ).toReal).abs.mul_const ‖w‖
    simp only [sub_self, abs_zero, zero_mul] at hm
    exact hm.eventually (gt_mem_nhds hε3)
  have hA := hlow _ h₁ (ε / 3) hε3
  have hB := hlow _ h₂ (ε / 3) hε3
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hfin.and (hmc.and (hA.and hB)))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hN k hk
  have := hk1
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply] at hk3 hk4
  rw [integral_add_const_continuousMap, integral_add_const_continuousMap] at hk3
  rw [integral_const_sub_continuousMap, integral_const_sub_continuousMap] at hk4
  rw [Real.dist_eq, abs_lt]
  have hk2' : |((β k univ).toReal - (ν univ).toReal) * ‖w‖| < ε / 3 := by
    rwa [abs_mul, abs_of_nonneg hc0]
  have hk2'' := abs_lt.mp hk2'
  have hexp : ((β k univ).toReal - (ν univ).toReal) * ‖w‖ =
      (β k univ).toReal * ‖w‖ - (ν univ).toReal * ‖w‖ := by ring
  rw [hexp] at hk2''
  constructor <;> linarith [hk2''.1, hk2''.2]

/-- **Upper bound by comparison** (the book's `τ ≤ θⁿ_{P_j}` for every `j` and
`θⁿ_{P_j} ⇀ θⁿ_P`): if `β_k ≤ γ_{j,k}` for `k` large, `∫ w dγ_{j,k} → ∫ w dν_j` as `k → ∞` and
`∫ w dν_j → ∫ w dν` as `j → ∞`, then `∫ w dβ_k ≤ ∫ w dν + ε` eventually, for `w ≥ 0`. -/
theorem eventually_integral_le_of_le_of_tendsto (β : ℕ → Measure X) (γ : ℕ → ℕ → Measure X)
    (ν' : ℕ → Measure X) (ν : Measure X)
    (hle : ∀ j, ∀ᶠ k in atTop, β k ≤ γ j k)
    (hfin : ∀ j, ∀ᶠ k in atTop, IsFiniteMeasure (γ j k))
    (hγ : ∀ j (w : C(X, ℝ)), Tendsto (fun k => ∫ x, w x ∂γ j k) atTop (𝓝 (∫ x, w x ∂ν' j)))
    (hν : ∀ w : C(X, ℝ), Tendsto (fun j => ∫ x, w x ∂ν' j) atTop (𝓝 (∫ x, w x ∂ν)))
    (w : C(X, ℝ)) (hw : 0 ≤ w) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∫ x, w x ∂β k ≤ ∫ x, w x ∂ν + ε := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨j, hj⟩ := ((hν w).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε2))).exists
  filter_upwards [hle j, hfin j, (hγ j w).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε2))]
    with k hk hkfin hkγ
  have hmono : ∫ x, w x ∂β k ≤ ∫ x, w x ∂γ j k :=
    integral_mono_measure hk (Eventually.of_forall fun x => hw x)
      (integrable_continuousMap (γ j k) w)
  linarith

/-- **Lower bound by comparison** (the book's `θⁿ_{P_j} ≤ τ` for every `j` and
`θⁿ_{P_j} ⇀ θⁿ_P`): if `γ_{j,k} ≤ β_k` for `k` large (with `β_k` eventually finite),
`∫ w dγ_{j,k} → ∫ w dν_j` as `k → ∞` and `∫ w dν_j → ∫ w dν` as `j → ∞`, then
`∫ w dν - ε ≤ ∫ w dβ_k` eventually, for `w ≥ 0`. -/
theorem eventually_integral_ge_of_ge_of_tendsto (β : ℕ → Measure X) (γ : ℕ → ℕ → Measure X)
    (ν' : ℕ → Measure X) (ν : Measure X)
    (hle : ∀ j, ∀ᶠ k in atTop, γ j k ≤ β k)
    (hfin : ∀ᶠ k in atTop, IsFiniteMeasure (β k))
    (hγ : ∀ j (w : C(X, ℝ)), Tendsto (fun k => ∫ x, w x ∂γ j k) atTop (𝓝 (∫ x, w x ∂ν' j)))
    (hν : ∀ w : C(X, ℝ), Tendsto (fun j => ∫ x, w x ∂ν' j) atTop (𝓝 (∫ x, w x ∂ν)))
    (w : C(X, ℝ)) (hw : 0 ≤ w) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∫ x, w x ∂ν - ε ≤ ∫ x, w x ∂β k := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨j, hj⟩ := ((hν w).eventually (lt_mem_nhds (sub_lt_self _ hε2))).exists
  filter_upwards [hle j, hfin, (hγ j w).eventually (lt_mem_nhds (sub_lt_self _ hε2))]
    with k hk hkfin hkγ
  have hmono : ∫ x, w x ∂γ j k ≤ ∫ x, w x ∂β k :=
    integral_mono_measure hk (Eventually.of_forall fun x => hw x)
      (integrable_continuousMap (β k) w)
  linarith

end SGPT.Bergman.Quant3
