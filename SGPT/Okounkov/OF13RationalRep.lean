import SGPT.Okounkov.OF9RationalEmbedding

/-!
# Rational functions as ratios of homogeneous polynomials

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]): the resolution step principalizes the ideals of the numerators and
denominators of rational functions `u₁, …, uₙ ∈ ℂ(X)`; on a projective `X ⊆ ℙᴺ` these are the ideal
sheaves of homogeneous polynomials `P, Q` of the same degree with `u = P/Q`.

* `homogenizeAt i d A`: the homogenization of `A` to degree `d` with respect to `xᵢ`; it is
  homogeneous of degree `d` for `d ≥ deg A` (`isHomogeneous_homogenizeAt`) and has the same
  dehomogenization at `xᵢ = 1` (`eval₂_homogenizeAt`);
* `exists_homogeneous_ratio`: every rational function `q` of an integral `X` with a closed
  projective embedding is `q = P(x/x_l) / Q(x/x_l)` for homogeneous `P, Q` of the same degree,
  simultaneously in every affine chart `U_l` meeting the generic point, with `Q(x/x_l) ≠ 0`
  (the `polyFF`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S SGPT.Okounkov.OF9

/-! ### Homogenization -/

section Homogenize

variable {N : ℕ}

/-- The homogenization of `A` to degree `d` with respect to the variable `xᵢ`. -/
def homogenizeAt (i : Fin (N + 1)) (d : ℕ) (A : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ m ∈ A.support, monomial m (coeff m A) * X i ^ (d - m.degree)

theorem isHomogeneous_homogenizeAt (i : Fin (N + 1)) {d : ℕ} {A : MvPolynomial (Fin (N + 1)) ℂ}
    (hd : A.totalDegree ≤ d) : (homogenizeAt i d A).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m hm
  have hle : m.degree ≤ d := by
    change (m.sum fun _ e => e) ≤ d
    exact (le_totalDegree hm).trans hd
  have h := (isHomogeneous_monomial (coeff m A) (rfl : m.degree = m.degree)).mul
    (isHomogeneous_X_pow i (d - m.degree))
  rwa [Nat.add_sub_cancel' hle] at h

theorem eval₂_homogenizeAt {R : Type*} [CommRing R] (φ : ℂ →+* R) (x : Fin (N + 1) → R)
    (i : Fin (N + 1)) (hx : x i = 1) (d : ℕ) (A : MvPolynomial (Fin (N + 1)) ℂ) :
    eval₂ φ x (homogenizeAt i d A) = eval₂ φ x A := by
  conv_rhs => rw [A.as_sum]
  simp only [homogenizeAt, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_X, hx, one_pow, mul_one]

end Homogenize

/-! ### Ratios of homogeneous polynomials -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

omit [IsIntegral X] in
/-- `P(x/xᵢ)` for `P` the variables renamed by `succAbove` is the affine presentation. -/
theorem polyCoef_rename_succAbove (i : Fin (E.ambientDimension + 1))
    (A : MvPolynomial (Fin E.ambientDimension) ℂ) :
    polyCoef E i (rename i.succAbove A) = affinePresentation f E i A := by
  have h : (eval₂Hom (constMap E i) (fun k => ratio E i k)).comp
      (rename i.succAbove).toRingHom = affinePresentation f E i := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C,
        coe_eval₂Hom, eval₂_C]
      exact (affinePresentation_C f E i b).symm
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        coe_eval₂Hom, eval₂_X]
      exact (affinePresentation_X f E i a).symm
  exact congrArg (fun φ : MvPolynomial (Fin E.ambientDimension) ℂ →+* _ => φ A) h

omit [IsIntegral X] in
/-- Homogenization does not change `P(x/xᵢ)`. -/
theorem polyCoef_homogenizeAt (i : Fin (E.ambientDimension + 1)) (d : ℕ)
    (A : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) :
    polyCoef E i (homogenizeAt i d A) = polyCoef E i A :=
  eval₂_homogenizeAt (constMap E i) (fun k => ratio E i k) i (ratio_self E i) d A

/-- The rational function `P(x/xᵢ)` is the generic germ of the section `polyCoef`. -/
theorem polyFF_eq_germToFunctionField (i : Fin (E.ambientDimension + 1))
    (hi : genericPoint X ∈ coordOpen E i) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) :
    haveI : Nonempty (coordOpen E i) := ⟨⟨genericPoint X, hi⟩⟩
    polyFF f E i hi P = algebraMap Γ(X, coordOpen E i) X.functionField (polyCoef E i P) :=
  rfl

/-- **Rational functions are ratios of homogeneous polynomials.** For every `q ∈ ℂ(X)` there are
homogeneous polynomials `P, Q` of the same degree with `q · Q(x/x_l) = P(x/x_l)` and
`Q(x/x_l) ≠ 0` in every chart `U_l` containing the generic point. -/
theorem exists_homogeneous_ratio (q : X.functionField) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ),
      P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧
      ∀ (l : Fin (E.ambientDimension + 1)) (hl : genericPoint X ∈ coordOpen E l),
        polyFF f E l hl Q ≠ 0 ∧ q * polyFF f E l hl Q = polyFF f E l hl P := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ coordOpen E i := by
    obtain ⟨i, hi⟩ := (hyperplaneAtlas E).covers (genericPoint X)
    exact ⟨i, hi⟩
  have : Nonempty (coordOpen E i) := ⟨⟨genericPoint X, hi⟩⟩
  have hU := isAffineOpen_coordOpen E i
  have := functionField_isFractionRing_of_isAffineOpen X (coordOpen E i) hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, coordOpen E i)) q
  obtain ⟨A, rfl⟩ := affinePresentation_surjective f E i a
  obtain ⟨B, rfl⟩ := affinePresentation_surjective f E i b
  let A' := rename i.succAbove A
  let B' := rename i.succAbove B
  let d := max A'.totalDegree B'.totalDegree
  let P := homogenizeAt i d A'
  let Q := homogenizeAt i d B'
  have hP : P.IsHomogeneous d := isHomogeneous_homogenizeAt i (le_max_left _ _)
  have hQ : Q.IsHomogeneous d := isHomogeneous_homogenizeAt i (le_max_right _ _)
  have hPi : polyFF f E i hi P = algebraMap _ X.functionField (affinePresentation f E i A) := by
    rw [polyFF_eq_germToFunctionField, polyCoef_homogenizeAt, polyCoef_rename_succAbove]
  have hQi : polyFF f E i hi Q = algebraMap _ X.functionField (affinePresentation f E i B) := by
    rw [polyFF_eq_germToFunctionField, polyCoef_homogenizeAt, polyCoef_rename_succAbove]
  have hb0 : algebraMap Γ(X, coordOpen E i) X.functionField (affinePresentation f E i B) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hb)
  refine ⟨d, P, Q, hP, hQ, fun l hl => ⟨?_, ?_⟩⟩
  · intro h0
    have hback := OF9.polyFF_transition f E l i hl hi hQ
    rw [h0, mul_zero, hQi] at hback
    exact hb0 hback
  · rw [OF9.polyFF_transition f E i l hi hl hQ, OF9.polyFF_transition f E i l hi hl hP, hPi, hQi]
    field_simp

end Scheme

end SGPT.Okounkov.OF13
