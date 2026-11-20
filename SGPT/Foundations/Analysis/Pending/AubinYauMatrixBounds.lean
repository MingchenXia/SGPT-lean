import SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
import SGPT.Foundations.Analysis.Pending.HessianLocalExtremum
import SGPT.Foundations.Analysis.Pending.ConcentrationEigenvalueBound
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Two matrix steps of the Aubin--Yau `C²` estimate

* **Maximum principle, trace form** (`re_trace_mul_complexHessian_nonpos`): at a local maximum `z`
  of a `C²` function `H` on `ℂⁿ`, `Re tr(P · (H_{jk̄}(z))) ≤ 0` for every positive semidefinite `P`.
  With `P = (g'_{jk̄})⁻¹` this is `Δ'H(z) ≤ 0`, the step "`0 ≥ Δ'(log tr_g g' − Aφ)(p)`" of Székelyhidi's
  proof of Lemma 3.8 (`szekelyhidi-extremal:page-0060`).
* **The endgame** (`quad_le_of_trace_inv_le`, `quad_le_of_trace_le`): for positive definite `G` (the
  background metric) and `G'` (the new metric) in a common frame where `G = I`, `G' = diag λ`
  (`ConcentrationEigenvalueBound.exists_simultaneous_diagonalization`):
  `tr(G'⁻¹G) ≤ K` and `det G' ≤ D det G` give `G' ≤ D K^{n-1} G` (each `λ_k ≥ 1/K`, `∏ λ ≤ D`;
  (3.9)–(3.10) of `page-0060`), and `tr(G⁻¹G') ≤ T`, `det G' ≥ d det G` give `G' ≤ T G` and
  `G ≤ (T^{n-1}/d) G'` (the last paragraph of the proof of Lemma 3.8).

TN.4 B5, nonlinear track N3 (a), (b) (the statement under discussion; design note
the second-order Monge–Ampère estimate).
-/

open Matrix
open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.AubinYauMatrixBounds

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian

variable {n : ℕ}

/-! ### The maximum principle in trace form -/

/-- At a local maximum the complex Hessian is negative semidefinite. -/
theorem re_dotProduct_mulVec_complexHessian_nonpos {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hmax : IsLocalMax u z) (y : Fin n → ℂ) :
    (star y ⬝ᵥ ((complexHessian u z).mulVec y)).re ≤ 0 := by
  rw [dotProduct_mulVec_complexHessian_eq_leviForm hu y, Complex.ofReal_re, leviForm,
    realHessian_eq_fderiv, realHessian_eq_fderiv]
  have h1 := hmax.fderiv_fderiv_nonpos hu (coordCombination y)
  have h2 := hmax.fderiv_fderiv_nonpos hu (Complex.I • coordCombination y)
  linarith

/-- **Maximum principle, trace form**: `Re tr(P · Hess_ℂ u(z)) ≤ 0` at a local maximum, for
positive semidefinite `P`. -/
theorem re_trace_mul_complexHessian_nonpos {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hmax : IsLocalMax u z) {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosSemidef) : (P * complexHessian u z).trace.re ≤ 0 := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  rw [Finset.sum_mul, trace_sum, Complex.re_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]
  exact re_dotProduct_mulVec_complexHessian_nonpos hu hmax (v i)

/-! ### Eigenvalue inequalities -/

/-- From `∑ 1/λ ≤ K` and `∏ λ ≤ D`: `λ_k ≤ D K^{n-1}`. -/
theorem le_of_sum_inv_le_of_prod_le {lam : Fin n → ℝ} (hlam : ∀ k, 0 < lam k) {K D : ℝ}
    (hK : ∑ k, (lam k)⁻¹ ≤ K) (hD : ∏ k, lam k ≤ D) (k : Fin n) :
    lam k ≤ D * K ^ (n - 1) := by
  classical
  have hKk : ∀ j, (lam j)⁻¹ ≤ K := fun j =>
    (Finset.single_le_sum (f := fun j => (lam j)⁻¹) (fun j _ => (inv_pos.mpr (hlam j)).le)
      (Finset.mem_univ j)).trans hK
  have hK0 : 0 < K := (inv_pos.mpr (hlam k)).trans_le (hKk k)
  have hge : ∀ j, K⁻¹ ≤ lam j := fun j => by
    rw [inv_le_comm₀ hK0 (hlam j)]; exact hKk j
  have hcard : (Finset.univ.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hP : K⁻¹ ^ (n - 1) ≤ ∏ j ∈ Finset.univ.erase k, lam j := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun j _ => (inv_pos.mpr hK0).le) fun j _ => hge j
  have hsplit := Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ k)
  have h1 : lam k * K⁻¹ ^ (n - 1) ≤ D := by
    calc lam k * K⁻¹ ^ (n - 1) ≤ lam k * ∏ j ∈ Finset.univ.erase k, lam j :=
          mul_le_mul_of_nonneg_left hP (hlam k).le
      _ = ∏ j, lam j := hsplit
      _ ≤ D := hD
  have hKp : 0 < K ^ (n - 1) := pow_pos hK0 _
  rw [inv_pow] at h1
  calc lam k = lam k * (K ^ (n - 1))⁻¹ * K ^ (n - 1) := by field_simp
    _ ≤ D * K ^ (n - 1) := mul_le_mul_of_nonneg_right h1 hKp.le

/-- From `∑ λ ≤ T` and `d ≤ ∏ λ`: `d / T^{n-1} ≤ λ_k ≤ T`. -/
theorem le_of_sum_le_of_le_prod {lam : Fin n → ℝ} (hlam : ∀ k, 0 < lam k) {T d : ℝ}
    (hT : ∑ k, lam k ≤ T) (hd : d ≤ ∏ k, lam k) (k : Fin n) :
    lam k ≤ T ∧ d / T ^ (n - 1) ≤ lam k := by
  classical
  have hTk : ∀ j, lam j ≤ T := fun j =>
    (Finset.single_le_sum (f := lam) (fun j _ => (hlam j).le) (Finset.mem_univ j)).trans hT
  refine ⟨hTk k, ?_⟩
  have hT0 : 0 < T := (hlam k).trans_le (hTk k)
  have hcard : (Finset.univ.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hP : ∏ j ∈ Finset.univ.erase k, lam j ≤ T ^ (n - 1) := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun j _ => (hlam j).le) fun j _ => hTk j
  have hsplit := Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ k)
  have h1 : d ≤ lam k * T ^ (n - 1) :=
    hd.trans (hsplit ▸ mul_le_mul_of_nonneg_left hP (hlam k).le)
  rw [div_le_iff₀ (pow_pos hT0 _)]
  exact h1

/-! ### The common frame of two positive definite matrices -/

theorem star_mulVec_dotProduct_mulVec (R M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    star (R *ᵥ y) ⬝ᵥ (M *ᵥ (R *ᵥ y)) = star y ⬝ᵥ ((star R * M * R) *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose]

theorem re_dotProduct_diagonal_mulVec (lam : Fin n → ℝ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (diagonal (fun k => (lam k : ℂ)) *ᵥ y)).re = ∑ k, lam k * Complex.normSq (y k) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  ring

/-- **The common frame**: for positive definite `G, G'` there are `λ_k > 0` (the eigenvalues of
`G⁻¹G'`) with `tr(G'⁻¹G) = ∑ 1/λ`, `tr(G⁻¹G') = ∑ λ`, `det G' = ∏ λ · det G`, and the quadratic forms
compare through `λ`. -/
theorem exists_frame {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) (hG' : G'.PosDef) :
    ∃ lam : Fin n → ℝ, (∀ k, 0 < lam k) ∧
      (G'⁻¹ * G).trace = ∑ k, ((lam k : ℂ))⁻¹ ∧ (G⁻¹ * G').trace = ∑ k, (lam k : ℂ) ∧
      G'.det = (∏ k, (lam k : ℂ)) * G.det ∧
      (∀ c : ℝ, (∀ k, lam k ≤ c) → ∀ x : Fin n → ℂ,
        (star x ⬝ᵥ (G' *ᵥ x)).re ≤ c * (star x ⬝ᵥ (G *ᵥ x)).re) ∧
      (∀ c : ℝ, (∀ k, 1 ≤ c * lam k) → ∀ x : Fin n → ℂ,
        (star x ⬝ᵥ (G *ᵥ x)).re ≤ c * (star x ⬝ᵥ (G' *ᵥ x)).re) := by
  classical
  obtain ⟨R, hdet, hGR, lam, hlam, hG'R⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hG' hG
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun k => (lam k : ℂ) with hD
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hRu
  have hDdet : D.det ≠ 0 := by
    rw [hD, det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (hlam k).ne'
  have hDD : D⁻¹ * D = 1 := nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hDdet)
  have hDinv : D⁻¹ = diagonal fun k => ((lam k : ℂ))⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    have : (lam k : ℂ) ≠ 0 := by exact_mod_cast (hlam k).ne'
    field_simp
  -- `(star R) G = R⁻¹` and `(star R) G' = D R⁻¹`
  have hSG : (star R) * G = R⁻¹ := by
    calc (star R) * G = (star R) * G * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * G * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ := by rw [hGR, Matrix.one_mul]
  have hSG' : (star R) * G' = D * R⁻¹ := by
    calc (star R) * G' = (star R) * G' * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * G' * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D * R⁻¹ := by rw [hG'R]
  have hGinv : G⁻¹ = R * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSG, hRR]
  have hG'inv : G'⁻¹ = R * D⁻¹ * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSG', Matrix.mul_assoc R, ← Matrix.mul_assoc D⁻¹ D, hDD,
      Matrix.one_mul, hRR]
  refine ⟨lam, hlam, ?_, ?_, ?_, ?_, ?_⟩
  · calc (G'⁻¹ * G).trace = (R * D⁻¹ * R⁻¹).trace := by
          rw [hG'inv, Matrix.mul_assoc (R * D⁻¹), hSG]
      _ = (R⁻¹ * R * D⁻¹).trace := trace_mul_cycle _ _ _
      _ = ∑ k, ((lam k : ℂ))⁻¹ := by
          rw [nonsing_inv_mul R hRu, Matrix.one_mul, hDinv, trace_diagonal]
  · calc (G⁻¹ * G').trace = (R * D * R⁻¹).trace := by
          rw [hGinv, Matrix.mul_assoc, hSG', Matrix.mul_assoc]
      _ = (R⁻¹ * R * D).trace := trace_mul_cycle _ _ _
      _ = ∑ k, (lam k : ℂ) := by
          rw [nonsing_inv_mul R hRu, Matrix.one_mul, hD, trace_diagonal]
  · have h1 := congrArg det hGR
    have h2 := congrArg det hG'R
    rw [det_mul, det_mul, det_one] at h1
    rw [det_mul, det_mul, hD, det_diagonal] at h2
    calc G'.det = G'.det * ((star R).det * G.det * R.det) := by rw [h1, mul_one]
      _ = ((star R).det * G'.det * R.det) * G.det := by ring
      _ = (∏ k, (lam k : ℂ)) * G.det := by rw [h2]
  · intro c hc x
    obtain ⟨y, rfl⟩ : ∃ y, x = R *ᵥ y := ⟨R⁻¹ *ᵥ x, by rw [mulVec_mulVec, hRR, one_mulVec]⟩
    rw [star_mulVec_dotProduct_mulVec, star_mulVec_dotProduct_mulVec, hG'R, hGR,
      ← diagonal_one, hD, show (diagonal fun _ : Fin n => (1 : ℂ)) =
        diagonal fun k => (((fun _ : Fin n => (1 : ℝ)) k : ℝ) : ℂ) by simp,
      re_dotProduct_diagonal_mulVec, re_dotProduct_diagonal_mulVec, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right (hc k) (Complex.normSq_nonneg _)
  · intro c hc x
    obtain ⟨y, rfl⟩ : ∃ y, x = R *ᵥ y := ⟨R⁻¹ *ᵥ x, by rw [mulVec_mulVec, hRR, one_mulVec]⟩
    rw [star_mulVec_dotProduct_mulVec, star_mulVec_dotProduct_mulVec, hG'R, hGR,
      ← diagonal_one, hD, show (diagonal fun _ : Fin n => (1 : ℂ)) =
        diagonal fun k => (((fun _ : Fin n => (1 : ℝ)) k : ℝ) : ℂ) by simp,
      re_dotProduct_diagonal_mulVec, re_dotProduct_diagonal_mulVec, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [one_mul, ← mul_assoc]
      exact le_mul_of_one_le_left (Complex.normSq_nonneg _) (hc k)

/-! ### The endgame of the Aubin--Yau estimate -/

/-- `tr(G'⁻¹G) ≤ K` and `det G' ≤ D det G` give `G' ≤ D K^{n-1} G` (Székelyhidi (3.9)--(3.10),
`szekelyhidi-extremal:page-0060`). -/
theorem quad_le_of_trace_inv_le {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hG' : G'.PosDef) {K D : ℝ} (hK : (G'⁻¹ * G).trace.re ≤ K) (hD : G'.det.re ≤ D * G.det.re)
    (x : Fin n → ℂ) :
    (star x ⬝ᵥ (G' *ᵥ x)).re ≤ D * K ^ (n - 1) * (star x ⬝ᵥ (G *ᵥ x)).re := by
  classical
  obtain ⟨lam, hlam, htr, -, hdet, hq, -⟩ := exists_frame hG hG'
  have hdetG : 0 < G.det.re := (Complex.pos_iff.mp hG.det_pos).1
  have hK' : ∑ k, (lam k)⁻¹ ≤ K := by
    rw [htr, Complex.re_sum] at hK
    simpa [← Complex.ofReal_inv] using hK
  have hD' : ∏ k, lam k ≤ D := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_ofReal_mul] at hD
    exact le_of_mul_le_mul_right hD hdetG
  exact hq _ (fun k => le_of_sum_inv_le_of_prod_le hlam hK' hD' k) x

/-- `tr(G⁻¹G') ≤ T` and `det G' ≥ d det G` (`d > 0`) give `G' ≤ T G` and `G ≤ (T^{n-1}/d) G'`
(the last paragraph of the proof of Székelyhidi's Lemma 3.8, `szekelyhidi-extremal:page-0060`). -/
theorem quad_le_of_trace_le {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) (hG' : G'.PosDef)
    {T d : ℝ} (hT : (G⁻¹ * G').trace.re ≤ T) (hd : d * G.det.re ≤ G'.det.re) (hd0 : 0 < d)
    (x : Fin n → ℂ) :
    (star x ⬝ᵥ (G' *ᵥ x)).re ≤ T * (star x ⬝ᵥ (G *ᵥ x)).re ∧
      (star x ⬝ᵥ (G *ᵥ x)).re ≤ T ^ (n - 1) / d * (star x ⬝ᵥ (G' *ᵥ x)).re := by
  classical
  obtain ⟨lam, hlam, -, htr, hdet, hq, hq'⟩ := exists_frame hG hG'
  have hdetG : 0 < G.det.re := (Complex.pos_iff.mp hG.det_pos).1
  have hT' : ∑ k, lam k ≤ T := by
    rw [htr, Complex.re_sum] at hT
    simpa using hT
  have hd' : d ≤ ∏ k, lam k := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_ofReal_mul] at hd
    exact le_of_mul_le_mul_right hd hdetG
  have hb := fun k => le_of_sum_le_of_le_prod hlam hT' hd' k
  refine ⟨hq _ (fun k => (hb k).1) x, hq' _ (fun k => ?_) x⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact k.elim0
  have hT0 : 0 < T := (hlam k).trans_le (hb k).1
  have hpow : 0 < T ^ (n - 1) := pow_pos hT0 _
  have := (hb k).2
  rw [div_le_iff₀ hpow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
  linarith

end SGPT.Foundations.Analysis.Pending.AubinYauMatrixBounds
