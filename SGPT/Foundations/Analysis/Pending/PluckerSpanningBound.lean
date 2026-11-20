import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import SGPT.Foundations.Analysis.Pending.CauchyBinet

set_option autoImplicit false

/-!
# A spanning family of decomposable forms controls the Gram determinant

Demailly, CADG III.2.6, first step: write the monomials `dz_K ∧ d\bar z_L` in
terms of an arbitrary basis of `Λ^{k,k}T^⋆Ω` made of DECOMPOSABLE forms
`β_s = i β_{s,1}∧\bar β_{s,1}∧…∧i β_{s,k}∧\bar β_{s,k}`; then it suffices to
bound each `T ∧ β_s`.  That is what this module makes algebraic.

A decomposable `β_s` is the same datum as a surjective `ℂ`-linear map
`B_s : ℂⁿ → ℂ^k` (its rows are the `β_{s,j}`), and pairing `β_s` against the
`k`-plane spanned by the columns of an `n × k` matrix `A` gives `det (B_s A)`.
By Cauchy--Binet that pairing is linear in the Plücker vector
`ξ_I = det A_{I,·}` with coefficients the Plücker vector
`plucker (B_s) I = det (B_s)_{·,I}`.  So the only thing needed of the family is
that the Plücker functionals SEPARATE POINTS of `Λ^k ℂⁿ` — Demailly's
"`(β_s)` remains a basis", which is an OPEN condition and therefore survives the
slight perturbation of the `β_{s,j}` that the rest of the proof performs.

`exists_gram_le` is the conclusion: for such a family there is one constant `C`
with
  `Re det (AᴴA) ≤ C · Σ_s ‖det (B_s A)‖²`  for EVERY `n × k` matrix `A`.
The left-hand side is the flat `2k`-density of the `k`-plane of `A`
(`Pending.FlatDensityGramDeterminant`), and each summand on the right is the real
Jacobian of the projection `B_s` restricted to that plane
(`Pending.LinearProjectionJacobian.det_comp_linear`).  Nothing here is
`k`-subset specific: taking for `B_s` the `binom n k` coordinate projections
recovers Cauchy--Binet with `C = 1`.
-/

noncomputable section

open scoped Matrix

namespace SGPT.Foundations.Analysis.Pending.PluckerSpanningBound

open SGPT.Foundations.Analysis.Pending.CauchyBinet

variable {k n : ℕ}

/-- **The Plücker vector of a `k × n` matrix**: the `k × k` minor on the columns
`I`.  For `B` the matrix of `β_{s,1}, …, β_{s,k}` this is the coefficient of
`dz_I` in `β_{s,1}∧…∧β_{s,k}`. -/
def plucker (B : Matrix (Fin k) (Fin n) ℂ) (I : CardSubset k n) : ℂ :=
  (B.submatrix id I.emb).det

/-- **Cauchy--Binet as a Plücker pairing.**  `det (B·A)` is the pairing of the
Plücker vector of `B` with that of `A`. -/
theorem det_mul_eq_plucker_pairing (B : Matrix (Fin k) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin k) ℂ) :
    (B * A).det = ∑ I : CardSubset k n, plucker B I * (A.submatrix I.emb id).det :=
  det_mul_rect B A

/-- **The spanning condition.**  The Plücker functionals of the family separate
points of `Λ^k ℂⁿ ≅ ℂ^{CardSubset k n}`.  This is Demailly's "`(β_s)` remains a
basis of `Λ^{k,k}`", weakened to exactly what the estimate uses. -/
def SpansPlucker {σ : Type*} (B : σ → Matrix (Fin k) (Fin n) ℂ) : Prop :=
  ∀ ξ : CardSubset k n → ℂ, (∀ s, ∑ I : CardSubset k n, plucker (B s) I * ξ I = 0) → ξ = 0

/-- The Plücker pairing of a family, as a `ℂ`-linear map between Euclidean
spaces.  Euclidean (not supremum) norms are used so that the squared norm is
literally the sum of the squared moduli of the entries. -/
def pluckerMap {σ : Type*} [Fintype σ] (B : σ → Matrix (Fin k) (Fin n) ℂ) :
    EuclideanSpace ℂ (CardSubset k n) →ₗ[ℂ] EuclideanSpace ℂ σ where
  toFun ξ := WithLp.toLp 2 fun s => ∑ I : CardSubset k n, plucker (B s) I * ξ I
  map_add' := by
    intro x y
    ext s
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext s
    simp [Finset.mul_sum, mul_left_comm]

@[simp]
theorem pluckerMap_apply {σ : Type*} [Fintype σ] (B : σ → Matrix (Fin k) (Fin n) ℂ)
    (ξ : EuclideanSpace ℂ (CardSubset k n)) (s : σ) :
    pluckerMap B ξ s = ∑ I : CardSubset k n, plucker (B s) I * ξ I := rfl

/-- The squared Euclidean norm is the sum of the squared moduli of the entries. -/
theorem sq_norm_euclidean {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

/-- **The estimate.**  A family of `k × n` matrices whose Plücker functionals
separate points bounds the Gram determinant of every `n × k` matrix by the sum
of the squared moduli of the corresponding `k × k` determinants.

This is the algebraic content of the first step of Demailly's proof of CADG
III.2.6: since `(β_s)` is a basis of `Λ^{k,k}`, the coefficients of the current
are linear combinations of the `T ∧ β_s`, so a bound on each of the latter is a
bound on the mass. -/
theorem exists_gram_le {σ : Type*} [Fintype σ] (B : σ → Matrix (Fin k) (Fin n) ℂ)
    (hB : SpansPlucker B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix (Fin n) (Fin k) ℂ,
      ((Aᴴ * A).det).re ≤ C * ∑ s : σ, ‖(B s * A).det‖ ^ 2 := by
  have hker : LinearMap.ker (pluckerMap B) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    have h : ∀ s, ∑ I : CardSubset k n, plucker (B s) I * ξ I = 0 := by
      intro s
      have := congrArg (fun y : EuclideanSpace ℂ σ => y s) hξ
      simpa using this
    have := hB (fun I => ξ I) h
    ext I
    exact congrFun this I
  obtain ⟨K, -, hK⟩ := (pluckerMap B).exists_antilipschitzWith hker
  refine ⟨(K : ℝ) ^ 2, by positivity, fun A => ?_⟩
  set ξ : EuclideanSpace ℂ (CardSubset k n) :=
    WithLp.toLp 2 (fun I => (A.submatrix I.emb id).det) with hξdef
  have hξ : ∀ I : CardSubset k n, ξ I = (A.submatrix I.emb id).det := fun _ => rfl
  have hmap : ∀ s : σ, pluckerMap B ξ s = (B s * A).det := by
    intro s
    rw [pluckerMap_apply, det_mul_eq_plucker_pairing]
  have hnorm : ‖ξ‖ ≤ (K : ℝ) * ‖pluckerMap B ξ‖ := by
    have h := hK.le_mul_dist ξ 0
    simpa [dist_zero_right] using h
  have hlhs : ((Aᴴ * A).det).re = ‖ξ‖ ^ 2 := by
    rw [sq_norm_euclidean, re_det_conjTranspose_mul_self]
  have hrhs : ‖pluckerMap B ξ‖ ^ 2 = ∑ s : σ, ‖(B s * A).det‖ ^ 2 := by
    rw [sq_norm_euclidean]
    exact Finset.sum_congr rfl fun s _ => by rw [hmap s]
  calc ((Aᴴ * A).det).re = ‖ξ‖ ^ 2 := hlhs
    _ ≤ ((K : ℝ) * ‖pluckerMap B ξ‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) hnorm
    _ = (K : ℝ) ^ 2 * ‖pluckerMap B ξ‖ ^ 2 := by ring
    _ = (K : ℝ) ^ 2 * ∑ s : σ, ‖(B s * A).det‖ ^ 2 := by rw [hrhs]

end SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
