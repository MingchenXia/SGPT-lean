import SGPT.Foundations.Analysis.Pending.BergmanVanishingUniformGenerators
import SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition

set_option autoImplicit false

/-! # Actual local finite equations for a common-domain arbitrary zero family

A true constrained Bergman space produces one common comparison neighbourhood;
there is no interchange of infinite intersections with equality of germs.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.CommonDomainHolomorphicZeroSet

open FirstPass BergmanGenerators AnalyticGermDecomposition

noncomputable section

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

private theorem exists_nonzero_scale {f : ComplexModel n → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 (4 * R))) :
    ∃ η : ℂ, η ≠ 0 ∧ (fun x => η * f x) ∈ bergmanUnitBall 0 R (fun _ => 1) := by
  have hsub : closedBall (0 : ComplexModel n) (2 * R) ⊆ ball 0 (4 * R) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ComplexModel n) (2 * R)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  let M : ℝ := max B 0 + 1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_right B 0]
  have hbound : ∀ x ∈ ball (0 : ComplexModel n) (2 * R), ‖f x‖ ≤ M := by
    intro x hx
    exact (hB x (ball_subset_closedBall hx)).trans
      (by dsimp only [M]; linarith [le_max_left B 0])
  let V : ℝ≥0∞ := volume (ball (0 : ComplexModel n) (2 * R))
  let A : ℝ≥0∞ := ENNReal.ofReal (M ^ 2) * (V + 1)
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hA0 : A ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hM)).ne'
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_left le_rfl)))
  have hAtop : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by exact ENNReal.add_ne_top.mpr ⟨hVtop, ENNReal.one_ne_top⟩)
  have hint : ∫⁻ x in ball (0 : ComplexModel n) (2 * R), ENNReal.ofReal (‖f x‖ ^ 2) ≤ A := by
    calc
      _ ≤ ∫⁻ _x in ball (0 : ComplexModel n) (2 * R), ENNReal.ofReal (M ^ 2) :=
        setLIntegral_mono' measurableSet_ball fun x hx => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (hbound x hx) 2)
      _ = ENNReal.ofReal (M ^ 2) * V := by simp only [lintegral_const, Measure.restrict_apply_univ, V]
      _ ≤ A := by dsimp only [A]; gcongr; exact le_add_right le_rfl
  let a : ℝ := A.toReal
  have ha : 0 < a := ENNReal.toReal_pos hA0 hAtop
  have haA : ENNReal.ofReal a = A := ENNReal.ofReal_toReal hAtop
  let η : ℂ := ((Real.sqrt a)⁻¹ : ℝ)
  have hη : η ≠ 0 := by
    dsimp only [η]
    exact_mod_cast (inv_ne_zero (Real.sqrt_pos.mpr ha).ne')
  have hnorm : ∀ x, ‖η * f x‖ ^ 2 = a⁻¹ * ‖f x‖ ^ 2 := by
    intro x
    simp only [η, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt ha.le]
  refine ⟨η, hη, hf.const_mul _ |>.mono (ball_subset_closedBall.trans hsub), ?_⟩
  simp only [hnorm, mul_one]
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ a⁻¹)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal a⁻¹ * A := by gcongr
    _ = 1 := by rw [← haA, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]

/-- Any family of original functions holomorphic on one common larger ball has
one actual finite zero presentation on an internally supplied smaller ball. -/
theorem exists_finite_zero_family {ι : Type*} (f : ι → ComplexModel n → ℂ)
    {R : ℝ} (hR : 0 < R) (hf : ∀ i, DifferentiableOn ℂ (f i) (ball 0 (4 * R))) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (r : ℝ), 0 < r ∧ r ≤ 2 * R ∧
      (∀ j, DifferentiableOn ℂ (g j) (ball 0 (2 * R))) ∧
      ∀ y ∈ ball 0 r, (∀ i, f i y = 0) ↔ (∀ j, g j y = 0) := by
  classical
  let A : Set (ComplexModel n) := {x | ∀ i, f i x = 0}
  obtain ⟨N, g, r, K, hr, hg, hdom⟩ :=
    BergmanVanishingUniformGenerators.exists_uniform_generators (z := (0 : ComplexModel n))
      (w := fun _ => 1) A hR aemeasurable_const zero_lt_one
      (fun _ _ => by rw [ENNReal.ofReal_one])
  refine ⟨N, g, min r (2 * R), lt_min hr (by positivity), min_le_right _ _,
    fun j => (hg j).1.1, ?_⟩
  intro y hy
  have hyD : y ∈ ball (0 : ComplexModel n) (2 * R) :=
    ball_subset_ball (min_le_right _ _) hy
  have hyr : y ∈ ball (0 : ComplexModel n) r := ball_subset_ball (min_le_left _ _) hy
  constructor
  · intro h j
    exact (hg j).2 y ⟨h, hyD⟩
  · intro h i
    obtain ⟨η, hη, hηf⟩ := exists_nonzero_scale hR (hf i)
    have hzero : ∀ x ∈ A ∩ ball (0 : ComplexModel n) (2 * R), η * f i x = 0 := by
      intro x hx
      rw [hx.1 i, mul_zero]
    have hle := hdom _ hηf hzero y hyr
    simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero] at hle
    have hz : η * f i y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (η * f i y)])
    exact (mul_eq_zero.mp hz).resolve_left hη

/-- The infinite common zero set is an actual finite-equation analytic germ. -/
theorem isAnalyticGerm_zero_set {ι : Type*} (f : ι → ComplexModel n → ℂ)
    {R : ℝ} (hR : 0 < R) (hf : ∀ i, DifferentiableOn ℂ (f i) (ball 0 (4 * R))) :
    IsAnalyticGerm {x : ComplexModel n | ∀ i, f i x = 0} := by
  obtain ⟨N, g, r, hr, _, hg, hzero⟩ := exists_finite_zero_family f hR hf
  refine ⟨N, g, fun j => ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : ComplexModel n) (by positivity : 0 < 2 * R)] with x hx
    exact (hg j).differentiableAt (isOpen_ball.mem_nhds hx)
  · filter_upwards [ball_mem_nhds (0 : ComplexModel n) hr] with x hx
    exact hzero x hx

end
end SGPT.Foundations.Analysis.Pending.CommonDomainHolomorphicZeroSet
