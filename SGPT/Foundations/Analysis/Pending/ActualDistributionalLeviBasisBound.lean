import SGPT.Foundations.Analysis.Pending.PositivityLeviLink
import SGPT.Foundations.Analysis.Pending.ActualHolomorphicRegularSpanningDirections

set_option autoImplicit false

/-! # Actual complex-basis control of positive distributional Levi pairings

The literal directional derivative algebra internally supplies a comparison
constant for any actual complex basis, with no incoming domination certificate.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Module
open scoped Topology Distributions ContDiff InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualDistributionalLeviBasisBound
open FirstPass PositivityLeviLink

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem levi_zero (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) :
    distributionalLeviCLM (0 : ComplexModel n) T φ = 0 := by
  have hz : (0 : ComplexModel n) = (0 : ℝ) • (0 : ComplexModel n) := by simp
  conv_lhs => rw [hz]
  rw [distributionalLeviCLM_smul_apply]
  simp

private theorem levi_I (T : 𝓓'(U, ℝ)) (v : ComplexModel n) (φ : 𝓓(U, ℝ)) :
    distributionalLeviCLM (Complex.I • v) T φ = distributionalLeviCLM v T φ := by
  have hII : Complex.I • (Complex.I • v) = (-1 : ℝ) • v := by
    rw [smul_smul, Complex.I_mul_I]
    simp
  rw [distributionalLeviCLM_apply, distributionalLeviCLM_apply, hII,
    TestFunction.lineDerivCLM_smul]
  simp only [_root_.smul_apply, map_smul, smul_eq_mul]
  ring

private theorem levi_parallelogram (T : 𝓓'(U, ℝ)) (v w : ComplexModel n)
    (φ : 𝓓(U, ℝ)) :
    distributionalLeviCLM (v + w) T φ + distributionalLeviCLM (v - w) T φ =
      2 * distributionalLeviCLM v T φ + 2 * distributionalLeviCLM w T φ := by
  have hsub : v - w = v + (-1 : ℝ) • w := by simp [sub_eq_add_neg]
  rw [hsub]
  simp only [distributionalLeviCLM_apply, smul_add, smul_comm Complex.I (-1 : ℝ),
    TestFunction.lineDerivCLM_add, TestFunction.lineDerivCLM_smul,
    _root_.add_apply, _root_.smul_apply, map_add, map_smul, smul_eq_mul]
  ring

private theorem levi_add_le (T : 𝓓'(U, ℝ)) (hT : HasNonnegativeDistributionalLevi T)
    (v w : ComplexModel n) (φ : 𝓓(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    distributionalLeviCLM (v + w) T φ ≤
      2 * (distributionalLeviCLM v T φ + distributionalLeviCLM w T φ) := by
  have hp := levi_parallelogram T v w φ
  have hz := hT (v - w) φ hφ
  linarith

private theorem levi_complex_smul_le (T : 𝓓'(U, ℝ))
    (hT : HasNonnegativeDistributionalLevi T) (c : ℂ) (v : ComplexModel n)
    (φ : 𝓓(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    distributionalLeviCLM (c • v) T φ ≤
      2 * (c.re ^ 2 + c.im ^ 2) * distributionalLeviCLM v T φ := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    ext i
    change c * v i = (c.re : ℂ) * v i + (c.im : ℂ) * (Complex.I * v i)
    calc
      c * v i = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * v i :=
        congrArg (fun z : ℂ => z * v i) (Complex.re_add_im c).symm
      _ = _ := by ring
  rw [he]
  have ha := levi_add_le T hT (c.re • v) (c.im • (Complex.I • v)) φ hφ
  rw [distributionalLeviCLM_smul_apply, distributionalLeviCLM_smul_apply, levi_I] at ha
  nlinarith

private theorem levi_sum_le {ι : Type*} (T : 𝓓'(U, ℝ))
    (hT : HasNonnegativeDistributionalLevi T) (s : Finset ι) (u : ι → ComplexModel n)
    (φ : 𝓓(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    distributionalLeviCLM (∑ i ∈ s, u i) T φ ≤
      (2 : ℝ) ^ s.card * ∑ i ∈ s, distributionalLeviCLM (u i) T φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      pow_succ]
    have ha := levi_add_le T hT (u i) (∑ j ∈ s, u j) φ hφ
    have hn := hT (u i) φ hφ
    have hp : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    calc
      distributionalLeviCLM (u i + ∑ j ∈ s, u j) T φ ≤
          2 * (distributionalLeviCLM (u i) T φ +
            distributionalLeviCLM (∑ j ∈ s, u j) T φ) := ha
      _ ≤ 2 * (distributionalLeviCLM (u i) T φ +
            2 ^ s.card * ∑ j ∈ s, distributionalLeviCLM (u j) T φ) := by
        gcongr
      _ ≤ 2 ^ s.card * 2 *
          (distributionalLeviCLM (u i) T φ + ∑ j ∈ s, distributionalLeviCLM (u j) T φ) := by
        nlinarith

/-- Natural genuine Levi positivity and an actual complex basis internally
produce one positive constant controlling every nonnegative compact scalar test. -/
theorem exists_pos_bound_from_complex_basis (T : 𝓓'(U, ℝ))
    (hT : HasNonnegativeDistributionalLevi T)
    (b : Basis (Fin n) ℂ (ComplexModel n)) (v : ComplexModel n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : 𝓓(U, ℝ)), (∀ x, 0 ≤ φ x) →
      distributionalLeviCLM v T φ ≤
        C * ∑ i, distributionalLeviCLM (b i) T φ := by
  classical
  let s : Fin n → ℝ := fun i => (b.repr v i).re ^ 2 + (b.repr v i).im ^ 2
  have hs (i : Fin n) : 0 ≤ s i := add_nonneg (sq_nonneg _) (sq_nonneg _)
  let H : ℝ := 1 + ∑ i, s i
  have hsum : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
  have hH : 0 < H := by dsimp [H]; linarith
  have hsH (i : Fin n) : s i ≤ H := by
    have ht := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hs j)
      (Finset.mem_univ i)
    dsimp [H]
    linarith
  refine ⟨2 ^ (n + 1) * H, mul_pos (pow_pos (by norm_num) _) hH, ?_⟩
  intro φ hφ
  have hbase : distributionalLeviCLM v T φ ≤
      (2 : ℝ) ^ n * ∑ i, distributionalLeviCLM ((b.repr v i) • b i) T φ := by
    simpa only [Finset.card_univ, Fintype.card_fin, b.sum_repr] using
      levi_sum_le T hT Finset.univ (fun i => (b.repr v i) • b i) φ hφ
  calc
    distributionalLeviCLM v T φ ≤
        (2 : ℝ) ^ n * ∑ i, distributionalLeviCLM ((b.repr v i) • b i) T φ := hbase
    _ ≤ (2 : ℝ) ^ n * ∑ i, 2 * s i * distributionalLeviCLM (b i) T φ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      exact Finset.sum_le_sum fun i _ => levi_complex_smul_le T hT (b.repr v i) (b i) φ hφ
    _ = (2 : ℝ) ^ (n + 1) * ∑ i, s i * distributionalLeviCLM (b i) T φ := by
      rw [pow_succ]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (n + 1) * (H * ∑ i, distributionalLeviCLM (b i) T φ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hsH i) (hT (b i) φ hφ)
    _ = _ := by ring

end SGPT.Foundations.Analysis.Pending.ActualDistributionalLeviBasisBound
