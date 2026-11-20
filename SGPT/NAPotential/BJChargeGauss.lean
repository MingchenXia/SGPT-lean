import SGPT.NAPotential.BJModelGauss
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Residues of the Gauss extension

Source: Boucksom–Jonsson ([BJ22], `references/bj22-trivval`), §1.3 and the proof of
Lemma `lem:tcdiv` (via [BHJ17, Theorem 4.6]): the residue field of the Gauss extension
`σ(v)` (`eq:Gext` of `chapter_NApotential.tex`) of a valuation `v` of `K` contains the residue field
of `v` and one more transcendental element. Towards `thm:BJappseq` (step R8 of
`claude-bj-model3:plan`: divisorial points are Rees valuations of flag ideals). Blueprint:
`claude-bj-charge.tex`.

We avoid residue fields: a family `u` of elements of a valued field `(L, w)` is *residually
independent* (`ResiduallyIndependent`) if `w(P(u)) = 0` for every nonzero polynomial `P` with
complex coefficients. This says that the `u_i` are `w`-units whose residues are algebraically
independent over `ℂ`; in particular the transcendence degree over `ℂ` of the residue field of any
local ring dominated by `w` and containing the `u_i` is at least the cardinality of the family.

## Main results

* `ResiduallyIndependent.val_eq_zero`, `ResiduallyIndependent.nonneg_aeval`;
* `residuallyIndependent_gaussExtension`: if `u` is residually independent for `v` and
  `v(f) = λ ∈ ℕ_{>0}`, then `u` together with `t^λ / f` is residually independent for the Gauss
  extension `σ(v)` of `K(t)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJCharge

open Polynomial SGPT.NAPotential.BJModel

section residual

variable {L : Type*} [Field L] [Algebra ℂ L]

/-- **Residual independence** of a family `u` in a valued field `(L, w)`: `w(P(u)) = 0` for every
nonzero polynomial `P` over `ℂ`, i.e. the `u_i` are `w`-units with residues algebraically
independent over `ℂ`. -/
def ResiduallyIndependent {ι : Type*} (w : SourceRealValuation L) (u : ι → L) : Prop :=
  ∀ P : MvPolynomial ι ℂ, P ≠ 0 → w (MvPolynomial.aeval u P) = 0

variable {ι : Type*} {w : SourceRealValuation L} {u : ι → L}

/-- The members of a residually independent family are units: `w(u_i) = 0`. -/
theorem ResiduallyIndependent.val_eq_zero (h : ResiduallyIndependent w u) (i : ι) :
    w (u i) = 0 := by
  have := h (MvPolynomial.X i) (MvPolynomial.X_ne_zero i)
  rwa [MvPolynomial.aeval_X] at this

/-- Polynomial expressions of a residually independent family are `w`-integral. -/
theorem ResiduallyIndependent.nonneg_aeval (h : ResiduallyIndependent w u)
    (P : MvPolynomial ι ℂ) : 0 ≤ w (MvPolynomial.aeval u P) := by
  by_cases hP : P = 0
  · rw [hP, map_zero, SourceRealValuation.map_zero]
    exact le_top
  · rw [h P hP]

end residual

section gauss

variable {K : Type*} [Field K] [Algebra ℂ K] (v : SourceRealValuation K)

/-- The embedding `K[t] → K(t)`. -/
abbrev polyEmb : K[X] →+* FractionRing K[X] := algebraMap K[X] (FractionRing K[X])

/-- The element `t^λ / f` of `K(t)`. -/
def gaussRatio (f : K) (l : ℕ) : FractionRing K[X] :=
  polyEmb (X ^ l) / polyEmb (C f)

/-- The family `u` (in `K ⊆ K(t)`) together with `t^λ / f` (index `none`). -/
def gaussFamily {ι : Type*} (u : ι → K) (f : K) (l : ℕ) : Option ι → FractionRing K[X] :=
  fun o => o.elim (gaussRatio f l) fun i => polyEmb (C (u i))

/-- The polynomial `∑_{k ≤ D} (a_k / f^k) t^{kλ}`. -/
def gaussPoly (a : ℕ → K) (f : K) (l D : ℕ) : K[X] :=
  ∑ k ∈ Finset.range D, C (a k / f ^ k) * X ^ (k * l)

omit [Algebra ℂ K] in
theorem coeff_gaussPoly (a : ℕ → K) (f : K) {l : ℕ} (hl : 0 < l) (D i : ℕ) :
    (gaussPoly a f l D).coeff i =
      if l ∣ i ∧ i / l < D then a (i / l) / f ^ (i / l) else 0 := by
  rw [gaussPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · obtain ⟨⟨m, rfl⟩, hm⟩ := h
    rw [Nat.mul_div_cancel_left m hl] at hm ⊢
    rw [Finset.sum_eq_single m]
    · simp [mul_comm]
    · intro k _ hk
      rw [if_neg, mul_zero]
      intro he
      apply hk
      have : k * l = m * l := by rw [← he]; ring
      exact Nat.eq_of_mul_eq_mul_right hl this
    · intro hm'
      exact absurd (Finset.mem_range.mpr hm) hm'
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    apply h
    refine ⟨⟨k, mul_comm k l⟩, ?_⟩
    rw [Nat.mul_div_cancel k hl]
    exact Finset.mem_range.mp hk

/-- `σ(v)(∑_{k<D} (a_k / f^k) t^{kλ}) = min_k v(a_k)` when `v(f) = λ`: lower bound. -/
theorem le_gaussVal_gaussPoly (a : ℕ → K) {f : K} (hf0 : f ≠ 0) {l : ℕ} (hl : 0 < l)
    (hf : v f = ((l : ℝ) : WithTop ℝ)) (D : ℕ) (r : WithTop ℝ) (ha : ∀ k, r ≤ v (a k)) :
    r ≤ gaussVal v (gaussPoly a f l D) := by
  rw [le_gaussVal_iff]
  intro i
  rw [coeff_gaussPoly a f hl]
  split_ifs with h
  · obtain ⟨⟨m, rfl⟩, -⟩ := h
    rw [Nat.mul_div_cancel_left m hl]
    have hfm : v (f ^ m) = (((l * m : ℕ) : ℝ) : WithTop ℝ) := by
      have := (v.toAddValuation).map_pow f m
      simp only [SourceRealValuation.toAddValuation_apply] at this
      rw [this, hf, ← WithTop.coe_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      ring
    have hmul : v (a m / f ^ m) + v (f ^ m) = v (a m) := by
      rw [← SourceRealValuation.map_mul', div_mul_cancel₀ _ (pow_ne_zero m hf0)]
    rw [hfm] at hmul
    rw [hmul]
    exact ha m
  · rw [SourceRealValuation.map_zero, WithTop.top_add]
    exact le_top

/-- Upper bound: `σ(v)(∑_{k<D} (a_k / f^k) t^{kλ}) ≤ v(a_m)` for `m < D`. -/
theorem gaussVal_gaussPoly_le (a : ℕ → K) {f : K} (hf0 : f ≠ 0) {l : ℕ} (hl : 0 < l)
    (hf : v f = ((l : ℝ) : WithTop ℝ)) {D m : ℕ} (hm : m < D) :
    gaussVal v (gaussPoly a f l D) ≤ v (a m) := by
  refine (gaussVal_le v _ (m * l)).trans (le_of_eq ?_)
  rw [coeff_gaussPoly a f hl, if_pos ⟨⟨m, mul_comm m l⟩, by rwa [Nat.mul_div_cancel m hl]⟩,
    Nat.mul_div_cancel m hl]
  have hfm : v (f ^ m) = (((m * l : ℕ) : ℝ) : WithTop ℝ) := by
    have := (v.toAddValuation).map_pow f m
    simp only [SourceRealValuation.toAddValuation_apply] at this
    rw [this, hf, ← WithTop.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hmul : v (a m / f ^ m) + v (f ^ m) = v (a m) := by
    rw [← SourceRealValuation.map_mul', div_mul_cancel₀ _ (pow_ne_zero m hf0)]
  rwa [hfm] at hmul

/-- Evaluation of a polynomial in `(u, t^λ / f)` as `∑_k P_k(u) (t^λ/f)^k`, `P_k ∈ ℂ[u]` the
coefficients of `P` in the variable `none`. -/
theorem aeval_gaussFamily {ι : Type*} (u : ι → K) (f : K) (l : ℕ)
    (P : MvPolynomial (Option ι) ℂ) :
    MvPolynomial.aeval (gaussFamily u f l) P =
      polyEmb (gaussPoly (fun k => MvPolynomial.aeval u
        ((MvPolynomial.optionEquivLeft ℂ ι P).coeff k)) f l
        ((MvPolynomial.optionEquivLeft ℂ ι P).natDegree + 1)) := by
  set Q := MvPolynomial.optionEquivLeft ℂ ι P
  let ψ : K →+* FractionRing K[X] := polyEmb.comp C
  let g : MvPolynomial ι ℂ →ₐ[ℂ] FractionRing K[X] :=
    MvPolynomial.aeval fun i => polyEmb (C (u i))
  have hg : ∀ Q' : MvPolynomial ι ℂ, g Q' = ψ (MvPolynomial.aeval u Q') := by
    intro Q'
    induction Q' using MvPolynomial.induction_on with
    | C a =>
      simp only [g, ψ, MvPolynomial.aeval_C, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℂ K[X] (FractionRing K[X]), Polynomial.algebraMap_apply]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [g, ψ]
  let φ₂ : MvPolynomial (Option ι) ℂ →+* FractionRing K[X] :=
    (Polynomial.eval₂RingHom g.toRingHom (gaussRatio f l)).comp
      (MvPolynomial.optionEquivLeft ℂ ι).toRingEquiv.toRingHom
  have hφ : (MvPolynomial.aeval (gaussFamily u f l)).toRingHom = φ₂ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ₂, g]
    · intro o
      cases o with
      | none =>
        simp [φ₂, gaussFamily, MvPolynomial.optionEquivLeft_X_none]
      | some i =>
        simp [φ₂, gaussFamily, MvPolynomial.optionEquivLeft_X_some, g]
  have hφP := congrArg (fun F : MvPolynomial (Option ι) ℂ →+* FractionRing K[X] => F P) hφ
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hφP
  rw [hφP]
  change Polynomial.eval₂ g.toRingHom (gaussRatio f l) Q = _
  rw [Polynomial.eval₂_eq_sum_range, gaussPoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show g.toRingHom (Q.coeff k) = g (Q.coeff k) from rfl, hg, gaussRatio, map_mul, map_pow,
    map_pow, div_pow]
  change ψ _ * _ = ψ (_ / _) * _
  rw [map_div₀, map_pow, pow_mul]
  simp only [ψ, RingHom.coe_comp, Function.comp_apply]
  ring

/-- **Residual independence for the Gauss extension** ([BJ22, §1.3]; residue field of `σ(v)`):
if `u` is residually independent for `v` and `v(f) = λ` with `λ ∈ ℕ_{>0}`, then `u` together with
`t^λ / f` is residually independent for `σ(v)`. -/
theorem residuallyIndependent_gaussExtension {ι : Type*} {u : ι → K}
    (hu : ResiduallyIndependent v u) {f : K} (hf0 : f ≠ 0) {l : ℕ} (hl : 0 < l)
    (hf : v f = ((l : ℝ) : WithTop ℝ)) :
    ResiduallyIndependent (gaussExtension v) (gaussFamily u f l) := by
  intro P hP
  set Q := MvPolynomial.optionEquivLeft ℂ ι P with hQ
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP
    have := congrArg (MvPolynomial.optionEquivLeft ℂ ι).symm h
    rwa [hQ, AlgEquiv.symm_apply_apply, map_zero] at this
  obtain ⟨m, hm⟩ : ∃ m, Q.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ0 (Polynomial.ext h)
  rw [aeval_gaussFamily, gaussExtension_algebraMap, ← gaussVal]
  refine le_antisymm ?_ (le_gaussVal_gaussPoly v _ hf0 hl hf _ 0 fun k => hu.nonneg_aeval _)
  refine (gaussVal_gaussPoly_le v _ hf0 hl hf (m := m) ?_).trans (le_of_eq (hu _ hm))
  exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hm)

end gauss

end SGPT.NAPotential.BJCharge
