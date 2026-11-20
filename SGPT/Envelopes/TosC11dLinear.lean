import SGPT.Envelopes.TosC11cHessianComponents
import SGPT.Envelopes.TosC11Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Linear algebra at the maximum point of the real-Hessian estimate

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:linear`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 2–4 (the eigenvectors `V_α` of
`∇²a(x₀)`, the perturbation `B₀` by the projection onto `V₁^⊥`, the complex components
`∂ᵢ = ½(∂_{xᵢ} - i ∂_{yᵢ})`), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

On `E = ℂⁿ` viewed as a real inner product space (`⟪x, y⟫ = Re ⟪x, y⟫_ℂ`):

* `bilinOp B` — the symmetric operator of a bilinear form, `⟪bilinOp B x, y⟫ = B x y`, linear and
  continuous in `B` (`bilinOpL`);
* `exists_top_eigen` — an orthonormal eigenbasis of a symmetric form with a top eigenvalue, and the
  Rayleigh bound `B(y, y) ≤ λ_max ‖y‖²`;
* `projForm b` — the form `⟪Y, Z⟫ - ⟪Y, b⟫⟪Z, b⟫` of the orthogonal projection onto `b^⊥`
  (FPT's `B₀`), positive semidefinite;
* `cpx L i = ½(L eᵢ - i L (i eᵢ))` — the complex component `∂ᵢ` of a real covector, with
  `‖cpx L i‖² = ¼((L eᵢ)² + (L (i eᵢ))²)`;
* `abs_apply_le_of_frame` — a bilinear form bounded by `C` on the real frame `eⱼ, i eⱼ` is bounded by
  `4 n² C ‖v‖ ‖w‖`.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-! ### The operator of a bilinear form -/

/-- The inverse Riesz map `E^* → E` as a continuous linear map. -/
def rieszInv : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n :=
  (InnerProductSpace.toDual ℝ (ComplexModel n)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem inner_rieszInv (L : ComplexModel n →L[ℝ] ℝ) (y : ComplexModel n) :
    ⟪rieszInv L, y⟫ = L y :=
  InnerProductSpace.toDual_symm_apply

theorem norm_rieszInv (L : ComplexModel n →L[ℝ] ℝ) : ‖rieszInv L‖ = ‖L‖ :=
  (InnerProductSpace.toDual ℝ (ComplexModel n)).symm.norm_map L

/-- The operator `T` of a bilinear form `B`: `⟪T x, y⟫ = B x y`. -/
def bilinOpL : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →L[ℝ]
    (ComplexModel n →L[ℝ] ComplexModel n) :=
  ContinuousLinearMap.compL ℝ (ComplexModel n) (ComplexModel n →L[ℝ] ℝ) (ComplexModel n) rieszInv

theorem inner_bilinOpL (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (x y : ComplexModel n) :
    ⟪bilinOpL B x, y⟫ = B x y := by
  simp only [bilinOpL, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  exact inner_rieszInv _ _

theorem finrank_real : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel n)]
  simp [Complex.finrank_real_complex]

/-- The operator of a symmetric form is symmetric. -/
theorem isSymmetric_bilinOpL {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = B y x) : (bilinOpL B : ComplexModel n →ₗ[ℝ] ComplexModel n).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_bilinOpL, real_inner_comm, inner_bilinOpL, hB]

/-- **Eigenbasis with a top eigenvalue** of a symmetric form on `ℂⁿ`, `n > 0`. -/
theorem exists_top_eigen (hn : 0 < n) {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = B y x) :
    ∃ (b : OrthonormalBasis (Fin (2 * n)) ℝ (ComplexModel n)) (μ : Fin (2 * n) → ℝ)
      (i₁ : Fin (2 * n)), (∀ i, bilinOpL B (b i) = μ i • b i) ∧ (∀ i, μ i ≤ μ i₁) ∧
      ∀ y, B y y ≤ μ i₁ * ‖y‖ ^ 2 := by
  have hT := isSymmetric_bilinOpL hB
  set b := hT.eigenvectorBasis finrank_real
  set μ := hT.eigenvalues finrank_real
  have hb : ∀ i, bilinOpL B (b i) = μ i • b i := fun i => by
    have := hT.apply_eigenvectorBasis finrank_real i
    exact this
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ μ Finset.univ_nonempty
  have htop : ∀ i, μ i ≤ μ i₁ := fun i => hi₁ i (Finset.mem_univ i)
  refine ⟨b, μ, i₁, hb, htop, fun y => ?_⟩
  have h := TosC11.inner_le_of_isTopEigen (bilinOpL B) b μ hb i₁ htop y
  rwa [inner_bilinOpL] at h

/-! ### The projection form -/

/-- The form of the orthogonal projection onto `b^⊥`: `⟪Y, Z⟫ - ⟪Y, b⟫⟪Z, b⟫` (FPT's `B₀`). -/
def projForm (b : ComplexModel n) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun Y Z => ⟪Y, Z⟫ - ⟪Y, b⟫ * ⟪Z, b⟫)
      (fun Y Y' Z => by simp only [inner_add_left]; ring)
      (fun c Y Z => by simp only [real_inner_smul_left, smul_eq_mul]; ring)
      (fun Y Z Z' => by simp only [inner_add_right, inner_add_left]; ring)
      (fun c Y Z => by simp only [real_inner_smul_right, real_inner_smul_left, smul_eq_mul]; ring))
    (1 + ‖b‖ ^ 2) fun Y Z => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      have h1 := abs_real_inner_le_norm Y Z
      have h2 := abs_real_inner_le_norm Y b
      have h3 := abs_real_inner_le_norm Z b
      calc |⟪Y, Z⟫ - ⟪Y, b⟫ * ⟪Z, b⟫| ≤ |⟪Y, Z⟫| + |⟪Y, b⟫| * |⟪Z, b⟫| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ ‖Y‖ * ‖Z‖ + (‖Y‖ * ‖b‖) * (‖Z‖ * ‖b‖) :=
            add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
        _ = (1 + ‖b‖ ^ 2) * ‖Y‖ * ‖Z‖ := by ring

theorem projForm_apply (b Y Z : ComplexModel n) :
    projForm b Y Z = ⟪Y, Z⟫ - ⟪Y, b⟫ * ⟪Z, b⟫ := rfl

theorem projForm_symm (b Y Z : ComplexModel n) : projForm b Y Z = projForm b Z Y := by
  rw [projForm_apply, projForm_apply, real_inner_comm]; ring

/-- The projection form is positive semidefinite for a unit vector `b`. -/
theorem projForm_nonneg {b : ComplexModel n} (hb : ‖b‖ = 1) (Y : ComplexModel n) :
    0 ≤ projForm b Y Y := by
  rw [projForm_apply, real_inner_self_eq_norm_sq]
  have h := abs_real_inner_le_norm Y b
  rw [hb, mul_one] at h
  have h2 : ⟪Y, b⟫ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

/-! ### Complex components of real covectors -/

/-- The complex component `∂ᵢ L = ½(L eᵢ - i L(i eᵢ))` of a real covector `L`. -/
def cpx (L : ComplexModel n →L[ℝ] ℝ) (i : Fin n) : ℂ :=
  ((L (TosC11c.stdVec i) : ℂ) - Complex.I * (L (Complex.I • TosC11c.stdVec i) : ℂ)) / 2

theorem norm_cpx_sq (L : ComplexModel n →L[ℝ] ℝ) (i : Fin n) :
    ‖cpx L i‖ ^ 2 = ((L (TosC11c.stdVec i)) ^ 2 + (L (Complex.I • TosC11c.stdVec i)) ^ 2) / 4 := by
  rw [cpx, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

theorem cpx_add (L L' : ComplexModel n →L[ℝ] ℝ) (i : Fin n) : cpx (L + L') i = cpx L i + cpx L' i := by
  simp only [cpx, add_apply]; push_cast; ring

theorem cpx_smul (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ) (i : Fin n) :
    cpx (c • L) i = c * cpx L i := by
  simp only [cpx, smul_apply, smul_eq_mul]; push_cast; ring

/-! ### Bounds from the real frame -/

theorem abs_re_le (v : ComplexModel n) (j : Fin n) : |(v j).re| ≤ ‖v‖ :=
  (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le v j)

theorem abs_im_le (v : ComplexModel n) (j : Fin n) : |(v j).im| ≤ ‖v‖ :=
  (Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le v j)

/-- A real covector bounded by `C` on the real frame `eⱼ, i eⱼ` is bounded by `2 n C ‖v‖`. -/
theorem abs_apply_le_of_frame (L : ComplexModel n →L[ℝ] ℝ) {C : ℝ}
    (hL : ∀ j, |L (TosC11c.stdVec j)| ≤ C ∧ |L (Complex.I • TosC11c.stdVec j)| ≤ C)
    (v : ComplexModel n) : |L v| ≤ 2 * n * C * ‖v‖ := by
  have hexp : L v = ∑ j, ((v j).re * L (TosC11c.stdVec j) +
      (v j).im * L (Complex.I • TosC11c.stdVec j)) := by
    conv_lhs => rw [TosC11c.eq_sum_re_im v]
    simp [map_sum, map_add, map_smul, smul_eq_mul]
  rw [hexp]
  have hterm : ∀ j, |(v j).re * L (TosC11c.stdVec j) +
      (v j).im * L (Complex.I • TosC11c.stdVec j)| ≤ 2 * C * ‖v‖ := by
    intro j
    obtain ⟨h1, h2⟩ := hL j
    have a1 := abs_re_le v j
    have a2 := abs_im_le v j
    calc _ ≤ |(v j).re * L (TosC11c.stdVec j)| + |(v j).im * L (Complex.I • TosC11c.stdVec j)| :=
          abs_add_le _ _
      _ ≤ ‖v‖ * C + ‖v‖ * C := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul a1 h1 (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul a2 h2 (abs_nonneg _) (norm_nonneg _))
      _ = 2 * C * ‖v‖ := by ring
  calc _ ≤ ∑ j, |(v j).re * L (TosC11c.stdVec j) + (v j).im * L (Complex.I • TosC11c.stdVec j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, 2 * C * ‖v‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * n * C * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The norm of a real covector bounded by `C` on the real frame. -/
theorem norm_le_of_frame (L : ComplexModel n →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ j, |L (TosC11c.stdVec j)| ≤ C ∧ |L (Complex.I • TosC11c.stdVec j)| ≤ C) :
    ‖L‖ ≤ 2 * n * C :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
    rw [Real.norm_eq_abs]; exact abs_apply_le_of_frame L hL v

/-- The norm of a bilinear form bounded by `C` on pairs of frame vectors: `‖B‖ ≤ 4 n² C`. -/
theorem norm_le_of_frame₂ (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ j k, |B (TosC11c.stdVec j) (TosC11c.stdVec k)| ≤ C ∧
      |B (TosC11c.stdVec j) (Complex.I • TosC11c.stdVec k)| ≤ C ∧
      |B (Complex.I • TosC11c.stdVec j) (TosC11c.stdVec k)| ≤ C ∧
      |B (Complex.I • TosC11c.stdVec j) (Complex.I • TosC11c.stdVec k)| ≤ C) :
    ‖B‖ ≤ 2 * n * (2 * n * C) := by
  have h1 : ∀ j, ‖B (TosC11c.stdVec j)‖ ≤ 2 * n * C ∧
      ‖B (Complex.I • TosC11c.stdVec j)‖ ≤ 2 * n * C := fun j =>
    ⟨norm_le_of_frame _ hC fun k => ⟨(hB j k).1, (hB j k).2.1⟩,
      norm_le_of_frame _ hC fun k => ⟨(hB j k).2.2.1, (hB j k).2.2.2⟩⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set L : ComplexModel n →L[ℝ] (ComplexModel n →L[ℝ] ℝ) := B
  have hexp : B v = ∑ j, ((v j).re • B (TosC11c.stdVec j) +
      (v j).im • B (Complex.I • TosC11c.stdVec j)) := by
    conv_lhs => rw [TosC11c.eq_sum_re_im v]
    simp [map_sum, map_add, map_smul]
  rw [hexp]
  have hterm : ∀ j, ‖(v j).re • B (TosC11c.stdVec j) +
      (v j).im • B (Complex.I • TosC11c.stdVec j)‖ ≤ 2 * (2 * n * C) * ‖v‖ := by
    intro j
    calc _ ≤ ‖(v j).re • B (TosC11c.stdVec j)‖ + ‖(v j).im • B (Complex.I • TosC11c.stdVec j)‖ :=
          norm_add_le _ _
      _ ≤ ‖v‖ * (2 * n * C) + ‖v‖ * (2 * n * C) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul (abs_re_le v j) (h1 j).1 (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul (abs_im_le v j) (h1 j).2 (norm_nonneg _) (norm_nonneg _))
      _ = 2 * (2 * n * C) * ‖v‖ := by ring
  calc _ ≤ ∑ j, ‖(v j).re • B (TosC11c.stdVec j) + (v j).im • B (Complex.I • TosC11c.stdVec j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, 2 * (2 * n * C) * ‖v‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * n * (2 * n * C) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end SGPT.Envelopes.TosC11d
