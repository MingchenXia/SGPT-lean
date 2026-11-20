import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Second variation of a simple top eigenvalue: the Rayleigh barrier

Lane TOS-C11 (`claude-tos-c11`, node `tos-c11:rayleigh-barrier`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 3 (the first and second variation
formulas of a simple eigenvalue), used for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

Let `t ↦ M(t)` be a twice differentiable curve of symmetric operators on a real inner product space,
and let `λ₁` be a **simple largest** eigenvalue of `M(0)`, with orthonormal eigenbasis `(bᵢ)`,
eigenvalues `λᵢ < λ₁` for `i ≠ i₁` and `b_{i₁}` the eigenvector of `λ₁`.  FPT uses that the largest
eigenvalue `λ₁(M(t))` is smooth near `0` with

* `λ₁'(0) = ⟪M'(0) b, b⟫`,
* `λ₁''(0) = ⟪M''(0) b, b⟫ + 2 Σ_{i ≠ i₁} ⟪M'(0) b, bᵢ⟫² / (λ₁ - λᵢ)`.

For the maximum principle only a **lower barrier** touching at `0` is needed: we construct an explicit
unit vector field `y(t) = (b + t w)/‖b + t w‖`, `w = Σ_{i ≠ i₁} ⟪M'(0) b, bᵢ⟫/(λ₁ - λᵢ) bᵢ`, such that
the Rayleigh quotient `r(t) = ⟪M(t) y(t), y(t)⟫`

* satisfies `r(t) ≤ sup_{‖z‖ = 1} ⟪M(t) z, z⟫ = λ₁(M(t))` for every `t` (it is a Rayleigh quotient of a
  unit vector),
* equals `λ₁ = λ₁(M(0))` at `t = 0` (`inner_le_of_isTopEigen`), and
* has exactly the first and second derivatives above at `0` (`exists_rayleigh_barrier`).

At a maximum point `x₀` of `log λ₁(Φ) + …` (FPT Step 2) one applies this along every real line
`t ↦ x₀ + t v`: the function `log r + …` lies below and touches at `t = 0`, so it has a local maximum
there, which gives the first-order condition and the second-order inequality used in FPT Step 3
without differentiating `λ₁(Φ)` itself.  (This replaces the implicit-function-theorem smoothness of
the simple eigenvalue in FPT; the resulting inequalities are identical.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- At `t = 0` the barrier value is the **largest** eigenvalue: for a symmetric `M₀` with
orthonormal eigenbasis `(bᵢ)` and `λᵢ ≤ λ₁` for all `i`, `⟪M₀ z, z⟫ ≤ λ₁ ‖z‖²`. -/
theorem inner_le_of_isTopEigen (M₀ : V →L[ℝ] V) (b : OrthonormalBasis ι ℝ V) (lam : ι → ℝ)
    (hb : ∀ i, M₀ (b i) = lam i • b i) (i₁ : ι) (htop : ∀ i, lam i ≤ lam i₁) (z : V) :
    ⟪M₀ z, z⟫ ≤ lam i₁ * ‖z‖ ^ 2 := by
  have hz : z = ∑ i, ⟪b i, z⟫ • b i := (b.sum_repr' z).symm
  have hMz : M₀ z = ∑ i, (⟪b i, z⟫ * lam i) • b i := by
    conv_lhs => rw [hz]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, smul_smul]
  have h1 : ⟪M₀ z, z⟫ = ∑ i, (⟪b i, z⟫ * lam i) * ⟪b i, z⟫ := by
    rw [hMz, sum_inner]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
  have h2 : ‖z‖ ^ 2 = ∑ i, ⟪b i, z⟫ * ⟪b i, z⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner z z]
    simp only [real_inner_comm z]
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := mul_self_nonneg ⟪b i, z⟫
  nlinarith [htop i]

/-- **The Rayleigh barrier for a simple top eigenvalue.**  Let `M : ℝ → (V →L[ℝ] V)` have derivative
`M' t` near `0`, with `M'` differentiable at `0` with derivative `M₂`, and let `M 0`, `M' 0` be
symmetric.  Let `(bᵢ)` be an orthonormal eigenbasis of `M 0` with eigenvalues `λᵢ`, and `λᵢ < λ_{i₁}`
for `i ≠ i₁`.  Then there is a unit vector field `y` with `y 0 = b_{i₁}` such that
`r(t) = ⟪M t (y t), y t⟫` is differentiable near `0` with derivative `r'` satisfying
`r' 0 = ⟪M' 0 b, b⟫` and `r''(0) = ⟪M₂ b, b⟫ + 2 Σ_{i ≠ i₁} ⟪M' 0 b, bᵢ⟫² / (λ_{i₁} - λᵢ)`. -/
theorem exists_rayleigh_barrier {M M' : ℝ → V →L[ℝ] V} {M₂ : V →L[ℝ] V}
    (hM : ∀ᶠ t in 𝓝 0, HasDerivAt M (M' t) t) (hM' : HasDerivAt M' M₂ 0)
    (hsym₀ : ∀ x z, ⟪M 0 x, z⟫ = ⟪x, M 0 z⟫) (hsym₁ : ∀ x z, ⟪M' 0 x, z⟫ = ⟪x, M' 0 z⟫)
    (b : OrthonormalBasis ι ℝ V) (lam : ι → ℝ) (hb : ∀ i, M 0 (b i) = lam i • b i) (i₁ : ι)
    (hgap : ∀ i, i ≠ i₁ → lam i < lam i₁) :
    ∃ y : ℝ → V, (∀ t, ‖y t‖ = 1) ∧ y 0 = b i₁ ∧
      ∃ r' : ℝ → ℝ, (∀ᶠ t in 𝓝 0, HasDerivAt (fun t => ⟪M t (y t), y t⟫) (r' t) t) ∧
        r' 0 = ⟪M' 0 (b i₁), b i₁⟫ ∧
        HasDerivAt r' (⟪M₂ (b i₁), b i₁⟫ + 2 * ∑ i ∈ Finset.univ.erase i₁,
          ⟪M' 0 (b i₁), b i⟫ ^ 2 / (lam i₁ - lam i)) 0 := by
  set b₁ := b i₁ with hb₁
  set m : ι → ℝ := fun i => ⟪M' 0 b₁, b i⟫
  set c : ι → ℝ := fun i => if i = i₁ then 0 else m i / (lam i₁ - lam i)
  set w : V := ∑ i, c i • b i
  set S : ℝ := ∑ i ∈ Finset.univ.erase i₁, m i ^ 2 / (lam i₁ - lam i)
  -- algebraic facts at `t = 0`
  have hb1n : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i₁, one_pow]
  have hwb : ⟪b₁, w⟫ = 0 := by
    rw [hb₁, b.orthonormal.inner_right_fintype]; simp [c]
  have hbw : ⟪w, b₁⟫ = 0 := by rw [real_inner_comm, hwb]
  have hcm : ∀ i, c i * (lam i₁ - lam i) = if i = i₁ then 0 else m i := by
    intro i
    by_cases hi : i = i₁
    · simp [c, hi]
    · have : lam i₁ - lam i ≠ 0 := sub_ne_zero.mpr (hgap i hi).ne'
      simp only [c, hi, if_false]
      field_simp
  have hS : ⟪M' 0 b₁, w⟫ = S := by
    rw [inner_sum]
    simp only [inner_smul_right]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₁)]
    simp only [c, if_true, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    simp only [m]
    ring
  have hMw : M 0 w = ∑ i, (c i * lam i) • b i := by
    simp only [w, map_sum, map_smul, hb, smul_smul]
  have hMww : ⟪M 0 w, w⟫ - lam i₁ * ⟪w, w⟫ = -S := by
    rw [hMw, b.orthonormal.inner_sum, b.orthonormal.inner_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← hS, inner_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_smul_right, starRingEnd_apply, star_trivial]
    have h := hcm i
    by_cases hi : i = i₁
    · simp [c, hi]
    · rw [if_neg hi] at h
      simp only [m] at h
      rw [← h]
      ring
  have hMb : M 0 b₁ = lam i₁ • b₁ := hb i₁
  have hN0 : ⟪M 0 b₁, b₁⟫ = lam i₁ := by rw [hMb, inner_smul_left, hb1n]; simp
  -- the curve `b + t w`
  set yv : ℝ → V := fun t => b₁ + t • w
  have hyv : ∀ t, HasDerivAt yv w t := fun t => by
    have h := HasDerivAt.const_add b₁ (HasDerivAt.smul_const (hasDerivAt_id t) w)
    simpa [yv] using h
  have hyv0 : yv 0 = b₁ := by simp [yv]
  have hD : ∀ t, ⟪yv t, yv t⟫ = 1 + t ^ 2 * ⟪w, w⟫ := by
    intro t
    simp only [yv, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb1n, hwb,
      hbw, starRingEnd_apply, star_trivial]
    ring
  have hDpos : ∀ t, 0 < ⟪yv t, yv t⟫ := fun t => by
    rw [hD]; nlinarith [real_inner_self_nonneg (x := w), sq_nonneg t]
  have hyvn : ∀ t, ‖yv t‖ ≠ 0 := fun t => by
    intro h
    have := hDpos t
    rw [real_inner_self_eq_norm_sq, h] at this
    simp at this
  -- the unit field and the quotient form of the barrier
  set y : ℝ → V := fun t => ‖yv t‖⁻¹ • yv t
  have hy1 : ∀ t, ‖y t‖ = 1 := fun t => by
    simp only [y, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hyvn t)
  have hb1norm : ‖b₁‖ = 1 := b.orthonormal.1 i₁
  have hy0 : y 0 = b₁ := by
    simp only [y, hyv0, hb1norm, inv_one, one_smul]
  set N : ℝ → ℝ := fun t => ⟪M t (yv t), yv t⟫
  set D : ℝ → ℝ := fun t => ⟪yv t, yv t⟫
  have hrq : (fun t => ⟪M t (y t), y t⟫) = fun t => N t / D t := by
    funext t
    simp only [y, N, D, map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial,
      real_inner_self_eq_norm_sq]
    field_simp [hyvn t]
  -- first derivatives
  set N' : ℝ → ℝ := fun t => ⟪M t (yv t), w⟫ + ⟪M' t (yv t) + M t w, yv t⟫
  set D' : ℝ → ℝ := fun t => ⟪yv t, w⟫ + ⟪w, yv t⟫
  have hNd : ∀ᶠ t in 𝓝 0, HasDerivAt N (N' t) t := hM.mono fun t ht =>
    HasDerivAt.inner ℝ (HasDerivAt.clm_apply ht (hyv t)) (hyv t)
  have hDd : ∀ t, HasDerivAt D (D' t) t := fun t => HasDerivAt.inner ℝ (hyv t) (hyv t)
  have vD0 : D 0 = 1 := by simp only [D, hyv0, hb1n]
  have vD'0 : D' 0 = 0 := by simp only [D', hyv0, hwb, hbw, add_zero]
  have vN0 : N 0 = lam i₁ := by simp only [N, hyv0, hN0]
  have vN'0 : N' 0 = ⟪M' 0 b₁, b₁⟫ := by
    simp only [N', hyv0]
    rw [hMb, inner_smul_left, hwb, inner_add_left, hsym₀ w b₁, hMb, inner_smul_right, hbw]
    simp
  refine ⟨y, hy1, hy0, fun t => (N' t * D t - N t * D' t) / D t ^ 2, ?_, ?_, ?_⟩
  · rw [hrq]
    exact hNd.mono fun t ht => HasDerivAt.fun_div ht (hDd t) (hDpos t).ne'
  · simp only [vN'0, vD0, vN0, vD'0]
    ring
  · -- second derivative at `0`
    have hM0 : HasDerivAt M (M' 0) 0 := hM.self_of_nhds
    have hw0 : HasDerivAt (fun _ : ℝ => w) 0 0 := hasDerivAt_const 0 w
    have hN'd : HasDerivAt N'
        ((⟪M 0 (yv 0), 0⟫ + ⟪M' 0 (yv 0) + M 0 w, w⟫) +
          (⟪M' 0 (yv 0) + M 0 w, w⟫ + ⟪(M₂ (yv 0) + M' 0 w) + (M' 0 w + M 0 0), yv 0⟫)) 0 :=
      HasDerivAt.add (HasDerivAt.inner ℝ (HasDerivAt.clm_apply hM0 (hyv 0)) hw0)
        (HasDerivAt.inner ℝ (HasDerivAt.add (HasDerivAt.clm_apply hM' (hyv 0))
          (HasDerivAt.clm_apply hM0 hw0)) (hyv 0))
    have hD'd : HasDerivAt D' ((⟪yv 0, 0⟫ + ⟪w, w⟫) + (⟪w, w⟫ + ⟪0, yv 0⟫)) 0 :=
      HasDerivAt.add (HasDerivAt.inner ℝ (hyv 0) hw0) (HasDerivAt.inner ℝ hw0 (hyv 0))
    have hq := HasDerivAt.fun_div (HasDerivAt.fun_sub (HasDerivAt.fun_mul hN'd (hDd 0))
      (HasDerivAt.fun_mul hNd.self_of_nhds hD'd)) (HasDerivAt.fun_pow (hDd 0) 2)
      (pow_ne_zero 2 (hDpos 0).ne')
    refine HasDerivAt.congr_deriv hq ?_
    rw [vD0, vD'0, vN0, vN'0, hyv0]
    have hsw : ⟪M' 0 w, b₁⟫ = S := by rw [hsym₁, real_inner_comm, hS]
    simp only [inner_add_left, inner_zero_left, inner_zero_right, map_zero, hsw, hS]
    have := hMww
    field_simp
    linarith

end SGPT.Envelopes.TosC11
