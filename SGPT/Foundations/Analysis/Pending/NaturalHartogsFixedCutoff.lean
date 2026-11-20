import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# One fixed native smooth cutoff captures almost all nearby ball mass

The actual bump is constructed before any weak convergence threshold. Its
entire closed support lies in every sufficiently nearby moving ball, and its
mass approximates the fixed ball's actual Haar mass. No sphere-boundary or
positive-dimension hypothesis is used.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace Function
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHartogsFixedCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- A genuine interior radius captures almost all of the original ball's actual mass. -/
theorem exists_inner_radius_mass_ge (μ : Measure E) [μ.IsAddHaarMeasure]
    (x : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ (1 - η) * (μ (ball x R)).toReal ≤
      (μ (closedBall x r)).toReal := by
  let r : ℕ → ℝ := fun j => R * (1 - (1 / 2 : ℝ) ^ (j + 1))
  have hrpos : ∀ j, 0 < r j := by
    intro j
    apply mul_pos hR
    exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero j))
  have hrlt : ∀ j, r j < R := by
    intro j
    have hp : 0 < (1 / 2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
    dsimp [r]
    nlinarith
  have hrmono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro j
    have hp : 0 ≤ (1 / 2 : ℝ) ^ j := pow_nonneg (by norm_num) _
    dsimp [r]
    simp only [pow_succ]
    nlinarith [mul_nonneg hR.le hp]
  have hr : Tendsto r atTop (𝓝 R) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
    have hr' := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul R
    simpa only [r, zero_mul, mul_zero, sub_zero, mul_one, ← pow_succ] using hr'
  have hunion : (⋃ j, ball x (r j)) = ball x R := by
    apply subset_antisymm
    · exact iUnion_subset (fun j => ball_subset_ball (hrlt j).le)
    · intro y hy
      have hdist : dist y x < R := hy
      obtain ⟨j, hj⟩ := (hr.eventually (Ioi_mem_nhds hdist)).exists
      exact mem_iUnion.mpr ⟨j, hj⟩
  have hm := tendsto_measure_iUnion_atTop (μ := μ) (s := fun j => ball x (r j))
    (fun i j hij => ball_subset_ball (hrmono hij))
  rw [hunion] at hm
  have hreal := (ENNReal.tendsto_toReal (measure_ball_ne_top (μ := μ) (x := x) (r := R))).comp hm
  have hmass : 0 < (μ (ball x R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos μ x hR).ne' measure_ball_ne_top
  have htarget : (1 - η) * (μ (ball x R)).toReal < (μ (ball x R)).toReal := by
    nlinarith
  obtain ⟨j, hj⟩ := (hreal.eventually (Ioi_mem_nhds htarget)).exists
  refine ⟨r j, hrpos j, hrlt j, hj.le.trans ?_⟩
  exact ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono ball_subset_closedBall)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual whole closed support of one bump lies inside every nearby moving ball. -/
theorem tsupport_subset_moving_ball (x : E) (χ : ContDiffBump x) {R : ℝ}
    (hχR : χ.rOut < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ ball x ε, tsupport χ ⊆ ball y R := by
  refine ⟨(R - χ.rOut) / 2, half_pos (sub_pos.mpr hχR), ?_⟩
  intro y hy z hz
  rw [χ.tsupport_eq] at hz
  have hz' : dist z x ≤ χ.rOut := hz
  have hy' : dist x y < (R - χ.rOut) / 2 := by
    simpa only [dist_comm] using (mem_ball.mp hy)
  show dist z y < R
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < R := by linarith

/-- A constructed native test captures near-full mass and has one uniform moving-support gap. -/
theorem exists_testFunction_mass_ge_and_moving_support
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
    (x : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hΩ : closedBall x R ⊆ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
      (1 - η) * (μ (ball x R)).toReal ≤ ∫ z, φ z ∂μ ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ ball x ε, tsupport φ ⊆ ball y R := by
  obtain ⟨r, hr, hrR, hmass⟩ := exists_inner_radius_mass_ge μ x hR hη
  let χ : ContDiffBump x := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hχR : χ.rOut < R := by dsimp [χ]; linarith
  have hsupp : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_closedBall hχR.le).trans hΩ
  let φ : 𝓓(Ω, ℝ) := ⟨χ, χ.contDiff, χ.hasCompactSupport, hsupp⟩
  refine ⟨φ, (fun z => ⟨χ.nonneg, χ.le_one⟩), ?_, ?_⟩
  · exact hmass.trans (χ.measure_closedBall_le_integral μ)
  · exact tsupport_subset_moving_ball x χ hχR

end SGPT.Foundations.Analysis.Pending.NaturalHartogsFixedCutoff
