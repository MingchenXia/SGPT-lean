import SGPT.Bergman.SourceHolomorphicGaugeTaylor
import SGPT.Bergman.SourcePolynomialBallScaling

/-!
# PolynomialLocalBound

Uniform degree-`k` Taylor control of the log frame norm on shrinking balls (local step for `h⁰ = O(kⁿ)`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology ContDiff ENNReal

variable {n : ℕ}

/-- The actual tensor-degree log squared frame norm. -/
def degreePotential (p q : ComplexModel n → ℝ) (k : ℕ) (z : ComplexModel n) : ℝ :=
  (k : ℝ) * p z + q z

/-- Built from the actual real frame-potential derivatives. -/
def degreeDifferential (p q : ComplexModel n → ℝ) (k : ℕ) (a : ComplexModel n) :
    ComplexModel n →L[ℝ] ℝ :=
  (k : ℝ) • fderiv ℝ p a + fderiv ℝ q a

theorem degreeDifferential_eq_fderiv {p q : ComplexModel n → ℝ}
    {a : ComplexModel n} (hp : DifferentiableAt ℝ p a) (hq : DifferentiableAt ℝ q a) (k : ℕ) :
    degreeDifferential p q k a = fderiv ℝ (degreePotential p q k) a := by
  change (k : ℝ) • fderiv ℝ p a + fderiv ℝ q a =
    fderiv ℝ (fun z => (k : ℝ) * p z + q z) a
  rw [fderiv_fun_add (hp.const_mul _) hq, fderiv_const_mul hp]

/-- One constant for the true degree-dependent Taylor remainder, selected
before ALL positive degrees and ALL pairs of points in the compact ball. -/
theorem exists_uniform_degree_remainder {U K : Set (ComplexModel n)} (hU : IsOpen U)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hKU : K ⊆ U)
    {p q : ComplexModel n → ℝ} (hp : ContDiffOn ℝ 2 p U) (hq : ContDiffOn ℝ 2 q U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, 0 < k → ∀ a ∈ K, ∀ z ∈ K,
      |degreePotential p q k z - degreePotential p q k a - degreeDifferential p q k a (z - a)| ≤
        A * (k : ℝ) * ‖z - a‖ ^ 2 := by
  obtain ⟨P, hP, hPr⟩ := exists_uniform_quadratic_remainder hU hK hconv hKU hp
  obtain ⟨Q, hQ, hQr⟩ := exists_uniform_quadratic_remainder hU hK hconv hKU hq
  refine ⟨P + Q, add_nonneg hP hQ, fun k hk a ha z hz => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : degreePotential p q k z - degreePotential p q k a - degreeDifferential p q k a (z - a) =
      (k : ℝ) * (p z - p a - fderiv ℝ p a (z - a)) +
        (q z - q a - fderiv ℝ q a (z - a)) := by
    simp only [degreePotential, degreeDifferential, add_apply,
      smul_apply, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ |(k : ℝ) * (p z - p a - fderiv ℝ p a (z - a))| +
        |q z - q a - fderiv ℝ q a (z - a)| := abs_add_le _ _
    _ = (k : ℝ) * |p z - p a - fderiv ℝ p a (z - a)| +
        |q z - q a - fderiv ℝ q a (z - a)| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (k : ℝ) * (P * ‖z - a‖ ^ 2) + Q * ‖z - a‖ ^ 2 := by
      gcongr
      · exact hPr a ha z hz
      · exact hQr a ha z hz
    _ ≤ (P + Q) * (k : ℝ) * ‖z - a‖ ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hQ (sub_nonneg.mpr hk1)) (sq_nonneg ‖z - a‖)]

/-- Natural C² and positive continuous density manufacture nested balls and
uniform gauge control, before all degrees, all centers and all coefficients. -/
theorem exists_local_polynomial_data {U : Set (ComplexModel n)} (hU : IsOpen U)
    {y : ComplexModel n} (hy : y ∈ U) {p q g : ComplexModel n → ℝ}
    (hp : ContDiffOn ℝ 2 p U) (hq : ContDiffOn ℝ 2 q U)
    (hg : ContinuousAt g y) (hgpos : 0 < g y) :
    ∃ r c B : ℝ, 0 < r ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ k : ℕ, 0 < k → ∀ a ∈ ball y r,
        closedBall a (polynomialRadius r k) ⊆ U ∧
        ∀ z ∈ closedBall a (polynomialRadius r k), c ≤ g z ∧
          degreePotential p q k a + degreeDifferential p q k a (z - a) ≤
            degreePotential p q k z + B := by
  let c : ℝ := g y / 2
  have hc : 0 < c := half_pos hgpos
  have hnear : (U ∩ {z | c < g z}) ∈ 𝓝 y :=
    inter_mem (hU.mem_nhds hy) (hg.eventually (Ioi_mem_nhds (half_lt_self hgpos)))
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let R := s / 2
  let r := R / 2
  have hR : 0 < R := half_pos hs
  have hr : 0 < r := half_pos hR
  have hK : closedBall y R ⊆ U ∩ {z | c < g z} :=
    (closedBall_subset_ball (half_lt_self hs)).trans hsub
  obtain ⟨A, hA, hAr⟩ := exists_uniform_degree_remainder hU
    (isCompact_closedBall y R) (convex_closedBall y R) (fun z hz => (hK hz).1) hp hq
  refine ⟨r, c, A * r ^ 2, hr, hc, mul_nonneg hA (sq_nonneg r), fun k hk a ha => ?_⟩
  have hak : a ∈ closedBall y R :=
    ball_subset_closedBall ((ball_subset_ball (half_le_self hR.le)) ha)
  have hinner : closedBall a (polynomialRadius r k) ⊆ closedBall y R := by
    intro z hz
    have hzdist := mem_closedBall.mp hz
    have hadist := mem_ball.mp ha
    have hδ := polynomialRadius_le hr.le hk
    apply mem_closedBall.mpr
    calc dist z y ≤ dist z a + dist a y := dist_triangle _ _ _
      _ ≤ polynomialRadius r k + r := add_le_add hzdist hadist.le
      _ ≤ r + r := add_le_add hδ le_rfl
      _ = R := by dsimp only [r]; ring
  refine ⟨fun z hz => (hK (hinner hz)).1, fun z hz => ⟨(hK (hinner hz)).2.le, ?_⟩⟩
  have hrem := (abs_le.mp (hAr k hk a hak z (hinner hz))).1
  have hnorm : ‖z - a‖ ≤ polynomialRadius r k := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hδp := (polynomialRadius_pos hr hk).le
  have hsquare : (k : ℝ) * ‖z - a‖ ^ 2 ≤ r ^ 2 := by
    calc _ ≤ (k : ℝ) * polynomialRadius r k ^ 2 := by gcongr
         _ = _ := polynomialRadius_sq hk
  nlinarith

end SGPT.Bergman.PolynomialH0Growth
