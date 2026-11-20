import SGPT.Foundations.Schemes.PolynomialProjectiveCanonical
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Actual projective canonical transition determinants

The coordinate quotient Jacobian is derived from literal normalized
homogeneous coordinate ratios. Its determinant is proved by the actual
single-pivot Laplace expansion, and proves the genuine canonical generator transition on actual coordinate
intersections. Normalizing the produced frames and gluing the global dual
to twisting O(n+1) are subsequent producers.
-/

open CategoryTheory Opposite AlgebraicGeometry Algebra

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section QuotientJacobian
variable {R : Type*} [CommRing R]

/-- The literal Jacobian of normalized homogeneous quotient coordinates,
with their actual ascending coordinate orders on the two charts. -/
def projectiveQuotientJacobian (n : ℕ) (i j : Fin (n + 1))
    (q : Fin (n + 1) → R) (u : Rˣ) : Matrix (Fin n) (Fin n) R := fun a b ↦
  (↑(u⁻¹) : R) * (if j.succAbove a = i.succAbove b then 1 else 0) -
    q (j.succAbove a) * (↑(u⁻¹) : R) ^ 2 * (if j = i.succAbove b then 1 else 0)

/-- On one actual normalized coordinate chart its own quotient change
has precisely the identity Jacobian. -/
theorem projectiveQuotientJacobian_self (n : ℕ) (i : Fin (n + 1))
    (q : Fin (n + 1) → R) (hi : q i = 1) (u : Rˣ) (hu : (u : R) = q i) :
    projectiveQuotientJacobian n i i q u = 1 := by
  have hu1 : u = 1 := Units.ext (hu.trans hi)
  subst u
  ext a b
  simp [projectiveQuotientJacobian, Matrix.one_apply]

/-- The actual quotient Jacobian row for the old distinguished coordinate
has exactly one nonzero entry, with its actual inverse-square value. -/
theorem projectiveQuotientJacobian_pivotRow (n : ℕ) (i j : Fin (n + 1))
    (q : Fin (n + 1) → R) (hi : q i = 1) (u : Rˣ) (a b : Fin n)
    (ha : j.succAbove a = i) (hb : i.succAbove b = j) (c : Fin n) :
    projectiveQuotientJacobian n i j q u a c =
      if c = b then -(↑(u⁻¹) : R) ^ 2 else 0 := by
  unfold projectiveQuotientJacobian
  rw [ha, hi]
  by_cases hc : c = b
  · subst c
    simp [← hb]
  · have hbc : i.succAbove b ≠ i.succAbove c := fun h ↦ hc (Fin.succAbove_right_injective h).symm
    simp [← hb, hc, hbc]

/-- The two genuine ascending maps deleting the same two coordinates
agree literally, by the native finite-index double-hole identity. -/
theorem projectiveDoubleCoordinateDeletion (m : ℕ) (i j : Fin (m + 2))
    (a b : Fin (m + 1)) (ha : j.succAbove a = i) (hb : i.succAbove b = j) (k : Fin m) :
    j.succAbove (a.succAbove k) = i.succAbove (b.succAbove k) := by
  have hb' : a.predAbove j = b := by
    apply Fin.succAbove_right_injective
    have h := Fin.succAbove_succAbove_predAbove j a
    rw [ha] at h
    exact h.trans hb.symm
  have h := Fin.succAbove_succAbove_succAbove_predAbove j a k
  rw [ha, hb'] at h
  exact h.symm

/-- Deleting the actual pivot row and column leaves precisely the
inverse-coordinate scalar diagonal matrix in the genuine remaining order. -/
theorem projectiveQuotientJacobian_pivotMinor (m : ℕ) (i j : Fin (m + 2))
    (q : Fin (m + 2) → R) (u : Rˣ) (a b : Fin (m + 1))
    (ha : j.succAbove a = i) (hb : i.succAbove b = j) :
    (projectiveQuotientJacobian (m + 1) i j q u).submatrix a.succAbove b.succAbove =
      Matrix.diagonal (fun _ : Fin m ↦ (↑(u⁻¹) : R)) := by
  ext k l
  have hne : j ≠ i.succAbove (b.succAbove l) := by
    rw [← hb]
    exact fun h ↦ b.ne_succAbove l (Fin.succAbove_right_injective h)
  have hdouble := projectiveDoubleCoordinateDeletion m i j a b ha hb k
  simp [Matrix.submatrix_apply, projectiveQuotientJacobian, hdouble, hne,
    Matrix.diagonal_apply]

/-- Actual pivot row and column positions have exactly the orientation
parity of the original ordered homogeneous coordinate indices. -/
theorem projectiveCoordinateDeletion_index_sum (n : ℕ) (i j : Fin (n + 1))
    (a b : Fin n) (ha : j.succAbove a = i) (hb : i.succAbove b = j) :
    a.val + b.val + 1 = i.val + j.val := by
  have ha' := congrArg Fin.val ha
  have hb' := congrArg Fin.val hb
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ] at ha' hb'
  split_ifs at ha' hb' <;> simp only [Fin.lt_def, Fin.val_castSucc] at * <;> omega


/-- The literal quotient-coordinate Jacobian has its actual orientation
sign and inverse-coordinate power determinant, proved by the true pivot row
and scalar diagonal minor, rather than supplied as a transition premise. -/
theorem projectiveQuotientJacobian_det (n : ℕ) (i j : Fin (n + 1))
    (q : Fin (n + 1) → R) (hi : q i = 1) (u : Rˣ) (hu : (u : R) = q j) :
    (projectiveQuotientJacobian n i j q u).det =
      (-1 : R) ^ (i.val + j.val) * (↑(u⁻¹) : R) ^ (n + 1) := by
  classical
  by_cases hij : i = j
  · subst j
    have hu1 : u = 1 := Units.ext (hu.trans hi)
    rw [projectiveQuotientJacobian_self n i q hi u hu, Matrix.det_one, hu1]
    simp only [inv_one, Units.val_one, one_pow, mul_one, pow_add, ← mul_pow]
    simp
  · cases n with
    | zero => exact (hij (Fin.ext (by omega))).elim
    | succ m =>
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hij
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
      rw [Matrix.det_succ_row _ a, Finset.sum_eq_single b]
      · rw [projectiveQuotientJacobian_pivotRow (m + 1) i j q hi u a b ha hb b,
          if_pos rfl, projectiveQuotientJacobian_pivotMinor m i j q u a b ha hb,
          Matrix.det_diagonal]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hindex := projectiveCoordinateDeletion_index_sum (m + 1) i j a b ha hb
        rw [← hindex]
        simp only [pow_add, pow_one]
        ring
      · intro c _ hcb
        rw [projectiveQuotientJacobian_pivotRow (m + 1) i j q hi u a b ha hb c,
          if_neg hcb, mul_zero, zero_mul]
      · simp


/-- The literal universal derivation differentiates the actual inverse
of a ring unit by its actual negative inverse-square formula. -/
theorem projectiveUnitInverse_differential {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (u : Aˣ) :
    KaehlerDifferential.D K A (↑(u⁻¹) : A) =
      -(↑(u⁻¹) : A) ^ 2 • KaehlerDifferential.D K A (u : A) :=
  (KaehlerDifferential.D K A).leibniz_of_mul_eq_one (Units.inv_mul u)

/-- Literal coordinate quotient differentials have their actual universal
Leibniz expansion; no coordinate derivative formula is a premise. -/
theorem projectiveQuotient_differential {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (q : A) (u : Aˣ) :
    KaehlerDifferential.D K A (q * (↑(u⁻¹) : A)) =
      (↑(u⁻¹) : A) • KaehlerDifferential.D K A q -
        (q * (↑(u⁻¹) : A) ^ 2) • KaehlerDifferential.D K A (u : A) := by
  rw [(KaehlerDifferential.D K A).leibniz, projectiveUnitInverse_differential]
  simp [smul_smul, sub_eq_add_neg, add_comm]

/-- Any genuine derivation of normalized coordinates is the actual
Kronecker expansion in the ordered other-coordinate differentials. -/
theorem projectiveNormalizedDifferential_sum {K A M : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup M] [Module A M] [Module K M]
    (D : Derivation K A M) (n : ℕ) (i : Fin (n + 1)) (q : Fin (n + 1) → A)
    (hi : q i = 1) (k : Fin (n + 1)) :
    D (q k) = ∑ b : Fin n, (if k = i.succAbove b then 1 else 0 : A) • D (q (i.succAbove b)) := by
  classical
  by_cases hk : k = i
  · subst k
    rw [hi, D.map_one_eq_zero]
    simp
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hk
    subst k
    simp

/-- Literal quotient differentials have exactly the actual Jacobian
expansion, for every universal or ordinary derivation. -/
theorem projectiveQuotientDifferential_jacobian {K A M : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup M] [Module A M] [Module K M]
    (D : Derivation K A M) (n : ℕ) (i j : Fin (n + 1)) (q : Fin (n + 1) → A)
    (hi : q i = 1) (u : Aˣ) (hu : (u : A) = q j) (a : Fin n) :
    D (q (j.succAbove a) * (↑(u⁻¹) : A)) =
      ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b • D (q (i.succAbove b)) := by
  classical
  have hInv := D.leibniz_of_mul_eq_one (Units.inv_mul u)
  rw [D.leibniz, hInv, hu]
  rw [projectiveNormalizedDifferential_sum D n i q hi (j.succAbove a),
    projectiveNormalizedDifferential_sum D n i q hi j]
  simp only [projectiveQuotientJacobian, sub_smul, Finset.smul_sum,
    smul_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_neg, neg_smul, sub_eq_add_neg, add_comm, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  split_ifs <;> simp

/-- The determinant formula for actual alternating products of a literal
matrix linear combination, proved on the genuine free coordinate basis. -/
theorem projectiveAlternating_matrix {A M N : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (n : ℕ) (ω : AlternatingMap A M N (Fin n)) (v : Fin n → M)
    (B : Matrix (Fin n) (Fin n) A) :
    ω (fun a ↦ ∑ b : Fin n, B a b • v b) = B.det • ω v := by
  classical
  let e := Pi.basisFun A (Fin n)
  let ψ := ω.compLinearMap (e.constr A v)
  have hψ : ψ = e.det.smulRight (ψ e) := by
    apply e.ext_alternating
    intro f hf
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    change ψ (e ∘ σ) = (e.det.smulRight (ψ e)) (e ∘ σ)
    rw [ψ.map_perm]
    change Equiv.Perm.sign σ • ψ e = e.det (e ∘ σ) • ψ e
    rw [e.det.map_perm, e.det_self]
    simp
  have h := congrArg (fun θ : AlternatingMap A (Fin n → A) N (Fin n) ↦ θ B) hψ
  simpa [ψ, e, AlternatingMap.compLinearMap_apply, Module.Basis.constr_apply_fintype,
    Pi.basisFun_det_apply, AlternatingMap.smulRight, Matrix.det] using h

/-- Actual alternating products of quotient differentials change by the
proved oriented inverse-coordinate power, with no transition determinant premise. -/
theorem projectiveQuotientDifferential_alternating {K A M N : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module K M] [Module A N]
    (D : Derivation K A M) (n : ℕ) (ω : AlternatingMap A M N (Fin n))
    (i j : Fin (n + 1)) (q : Fin (n + 1) → A) (hi : q i = 1)
    (u : Aˣ) (hu : (u : A) = q j) :
    ω (fun a ↦ D (q (j.succAbove a) * (↑(u⁻¹) : A))) =
      ((-1 : A) ^ (i.val + j.val) * (↑(u⁻¹) : A) ^ (n + 1)) •
        ω (fun b ↦ D (q (i.succAbove b))) := by
  have h : (fun a ↦ D (q (j.succAbove a) * (↑(u⁻¹) : A))) =
      fun a ↦ ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b • D (q (i.succAbove b)) :=
    funext (projectiveQuotientDifferential_jacobian D n i j q hi u hu)
  rw [h, projectiveAlternating_matrix, projectiveQuotientJacobian_det n i j q hi u hu]

/-- The same proved determinant formula for actual categorical relative
derivations, retaining their native coefficient-ring module structures. -/
theorem projectiveCategoricalQuotientDifferential_alternating {R A : CommRingCat}
    (φ : R ⟶ A) (M N : ModuleCat A) (D : M.Derivation φ)
    (n : ℕ) (ω : AlternatingMap A M N (Fin n))
    (i j : Fin (n + 1)) (q : Fin (n + 1) → A) (hi : q i = 1)
    (u : Aˣ) (hu : (u : A) = q j) :
    ω (fun a ↦ D.d (q (j.succAbove a) * (↑(u⁻¹) : A))) =
      ((-1 : A) ^ (i.val + j.val) * (↑(u⁻¹) : A) ^ (n + 1)) •
        ω (fun b ↦ D.d (q (i.succAbove b))) := by
  let := φ.hom.toAlgebra
  let := Module.compHom M φ.hom
  exact projectiveQuotientDifferential_alternating D n ω i j q hi u hu

end QuotientJacobian

section ActualProjectiveOverlap
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine homogeneous coordinate intersection ring. -/
abbrev polynomialProjOverlapRing (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X i * MvPolynomial.X j)

/-- The actual left chart restriction homomorphism retains the literal base-field scalars. -/
def polynomialProjOverlapLeft (i j : Fin (n + 1)) :
    polynomialProjCoordinateRing K n i →ₐ[K] polynomialProjOverlapRing K n i j where
  toRingHom := HomogeneousLocalization.awayMap _ (MvPolynomial.isHomogeneous_X K j) rfl
  commutes' r := HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _
    (homogeneousPolynomialDegreeZeroConstants r)

/-- The actual right chart restriction has the same genuine intersection target. -/
def polynomialProjOverlapRight (i j : Fin (n + 1)) :
    polynomialProjCoordinateRing K n j →ₐ[K] polynomialProjOverlapRing K n i j where
  toRingHom := HomogeneousLocalization.awayMap _ (MvPolynomial.isHomogeneous_X K i)
    (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
  commutes' r := HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _
    (homogeneousPolynomialDegreeZeroConstants r)

/-- The literal overlap coordinates satisfy the actual quotient transition,
proved by equality of genuine homogeneous fractions. -/
theorem polynomialProjOverlap_ratio_mul (i j k : Fin (n + 1)) :
    polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i j) *
      polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j k) =
        polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i k) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, polynomialProjOverlapLeft,
    polynomialProjOverlapRight, AlgHom.coe_mk,
    polynomialProjCoordinateRatio, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one]
  ring

/-- The two true opposite ratios multiply to one on the genuine overlap. -/
theorem polynomialProjOverlap_ratio_inv (i j : Fin (n + 1)) :
    polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i j) *
      polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j i) = 1 := by
  rw [polynomialProjOverlap_ratio_mul, polynomialProjCoordinateRatio_self, map_one]

/-- The actual distinguished overlap coordinate is a unit with its literal
opposite chart ratio as inverse. -/
def polynomialProjOverlapCoordinateUnit (i j : Fin (n + 1)) :
    (polynomialProjOverlapRing K n i j)ˣ where
  val := polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i j)
  inv := polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j i)
  val_inv := polynomialProjOverlap_ratio_inv K n i j
  inv_val := (mul_comm _ _).trans (polynomialProjOverlap_ratio_inv K n i j)

/-- Every genuine right-chart coordinate is the actual left normalized
coordinate divided by the actual distinguished unit. -/
theorem polynomialProjOverlap_ratio_quotient (i j k : Fin (n + 1)) :
    polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j k) =
      polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i k) *
        (↑((polynomialProjOverlapCoordinateUnit K n i j)⁻¹) : polynomialProjOverlapRing K n i j) := by
  have h := polynomialProjOverlap_ratio_mul K n i j k
  change (↑(polynomialProjOverlapCoordinateUnit K n i j) : polynomialProjOverlapRing K n i j) * _ = _ at h
  rw [← h, mul_assoc, mul_comm (polynomialProjOverlapRight K n i j _),
    ← mul_assoc, Units.mul_inv, one_mul]

/-- The actual homogeneous coordinate intersection is its native affine
open immersion into the genuine projective scheme. -/
def polynomialProjOverlapImmersion (i j : Fin (n + 1)) :
    Spec (.of (polynomialProjOverlapRing K n i j)) ⟶ polynomialProj K n :=
  Proj.awayι _ (MvPolynomial.X i * MvPolynomial.X j)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X K j)) (by decide)

instance polynomialProjOverlapImmersion_isOpenImmersion (i j : Fin (n + 1)) :
    IsOpenImmersion (polynomialProjOverlapImmersion K n i j) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι _ _ _ _))

/-- The actual left restriction map factors the actual projective overlap immersion. -/
theorem polynomialProjOverlapLeft_fac (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (polynomialProjOverlapLeft K n i j).toRingHom) ≫
      polynomialProjCoordinateImmersion K n i = polynomialProjOverlapImmersion K n i j :=
  Proj.SpecMap_awayMap_awayι _ (MvPolynomial.isHomogeneous_X K i) (by decide)
    (MvPolynomial.isHomogeneous_X K j) rfl

/-- The actual right restriction map factors the same projective overlap immersion. -/
theorem polynomialProjOverlapRight_fac (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (polynomialProjOverlapRight K n i j).toRingHom) ≫
      polynomialProjCoordinateImmersion K n j = polynomialProjOverlapImmersion K n i j :=
  Proj.SpecMap_awayMap_awayι _ (MvPolynomial.isHomogeneous_X K j) (by decide)
    (MvPolynomial.isHomogeneous_X K i) (mul_comm _ _)

/-- The literal quotient differential matrix on the actual affine intersection. -/
def polynomialProjOverlapJacobian (i j : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) (polynomialProjOverlapRing K n i j) :=
  projectiveQuotientJacobian n i j
    (fun k ↦ polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i k))
    (polynomialProjOverlapCoordinateUnit K n i j)

/-- The actual overlap Jacobian determinant is the true oriented inverse
coordinate power in the actual overlap ring. -/
theorem polynomialProjOverlapJacobian_det (i j : Fin (n + 1)) :
    (polynomialProjOverlapJacobian K n i j).det =
      (-1 : polynomialProjOverlapRing K n i j) ^ (i.val + j.val) *
        (↑((polynomialProjOverlapCoordinateUnit K n i j)⁻¹) : polynomialProjOverlapRing K n i j) ^ (n + 1) :=
  projectiveQuotientJacobian_det n i j _
    (by rw [polynomialProjCoordinateRatio_self, map_one]) _ rfl

/-- The genuine structure section map on the actual coordinate intersection. -/
def polynomialProjOverlapSectionMap (i j : Fin (n + 1)) :
    polynomialProjOverlapRing K n i j →+*
      Γ(polynomialProj K n, Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j)) :=
  (Proj.awayToSection _ (MvPolynomial.X i * MvPolynomial.X j)).hom

/-- Genuine left normalized homogeneous coordinate sections on the actual intersection. -/
def polynomialProjOverlapRegularRatio (i j k : Fin (n + 1)) :=
  polynomialProjOverlapSectionMap K n i j
    (polynomialProjOverlapLeft K n i j (polynomialProjCoordinateRatio K n i k))

/-- The actual distinguished overlap coordinate is a unit of the actual regular-section ring. -/
def polynomialProjOverlapRegularUnit (i j : Fin (n + 1)) :
    Γ(polynomialProj K n, Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j))ˣ :=
  Units.map (polynomialProjOverlapSectionMap K n i j) (polynomialProjOverlapCoordinateUnit K n i j)

/-- The normalized distinguished regular coordinate is exactly one. -/
theorem polynomialProjOverlapRegularRatio_self (i j : Fin (n + 1)) :
    polynomialProjOverlapRegularRatio K n i j i = 1 := by
  simp [polynomialProjOverlapRegularRatio, polynomialProjCoordinateRatio_self]

/-- Genuine right ratio sections are the actual left ratio divided by the
actual distinguished regular unit. -/
theorem polynomialProjOverlapRegularRatio_quotient (i j k : Fin (n + 1)) :
    polynomialProjOverlapSectionMap K n i j
        (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j k)) =
      polynomialProjOverlapRegularRatio K n i j k *
        (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹) :
          Γ(polynomialProj K n, Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j))) := by
  rw [polynomialProjOverlap_ratio_quotient, map_mul]
  rfl

/-- The literal ordered top differentials of actual homogeneous ratios,
as a section of the genuine exterior cotangent sheaf on the true intersection. -/
def polynomialProjOverlapCanonicalGenerator (i j : Fin (n + 1)) :
    bundleSections (exteriorCotangentSheaf (polynomialProjStructureMap K n) n)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X i * MvPolynomial.X j)) :=
  exteriorSheafSection (cotangentPresheaf (polynomialProjStructureMap K n)) n _
    (fun a ↦ (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
      (polynomialProjOverlapRegularRatio K n i j (i.succAbove a)))

/-- The genuine right-chart top differential product on the same actual intersection. -/
def polynomialProjOverlapRightCanonicalGenerator (i j : Fin (n + 1)) :
    bundleSections (exteriorCotangentSheaf (polynomialProjStructureMap K n) n)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X i * MvPolynomial.X j)) :=
  exteriorSheafSection (cotangentPresheaf (polynomialProjStructureMap K n)) n _
    (fun a ↦ (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
      (polynomialProjOverlapSectionMap K n i j
        (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j (j.succAbove a)))))

/-- Actual canonical differential products on genuine projective chart
intersections satisfy the literal determinant transition in the genuine sheaf. -/
theorem polynomialProjOverlapCanonicalGenerator_transition (i j : Fin (n + 1)) :
    polynomialProjOverlapRightCanonicalGenerator K n i j =
      ((-1 : Γ(polynomialProj K n, Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j))) ^
        (i.val + j.val) * (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹)) ^ (n + 1)) •
          polynomialProjOverlapCanonicalGenerator K n i j := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X i * MvPolynomial.X j)
  let f := polynomialProjStructureMap K n
  let φ := (schemeConstantPresheafMap f).app (.op U)
  let D := CommRingCat.KaehlerDifferential.D φ
  let ω := exteriorSheafSection (cotangentPresheaf f) n U
  have hq : (fun a : Fin n ↦ polynomialProjOverlapSectionMap K n i j
      (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j (j.succAbove a)))) =
      fun a ↦ polynomialProjOverlapRegularRatio K n i j (j.succAbove a) *
        (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹)) :=
    funext (fun a ↦ polynomialProjOverlapRegularRatio_quotient K n i j (j.succAbove a))
  change ω (fun a ↦ D.d (polynomialProjOverlapSectionMap K n i j
      (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j (j.succAbove a))))) = _
  rw [show (fun a ↦ D.d (polynomialProjOverlapSectionMap K n i j
      (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j (j.succAbove a))))) =
      fun a ↦ D.d (polynomialProjOverlapRegularRatio K n i j (j.succAbove a) *
        (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹))) from congrArg (fun q ↦ D.d ∘ q) hq]
  exact projectiveCategoricalQuotientDifferential_alternating φ _ _ D n ω i j _
    (polynomialProjOverlapRegularRatio_self K n i j) (polynomialProjOverlapRegularUnit K n i j) rfl

/-- The actual chart's homogeneous fractions are genuine regular sections. -/
def polynomialProjCoordinateSectionMap (i : Fin (n + 1)) :
    polynomialProjCoordinateRing K n i →+*
      Γ(polynomialProj K n, Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)) :=
  (Proj.awayToSection _ (MvPolynomial.X i)).hom

/-- Literal genuine ratio sections on the original coordinate chart. -/
def polynomialProjCoordinateRegularRatio (i k : Fin (n + 1)) :=
  polynomialProjCoordinateSectionMap K n i (polynomialProjCoordinateRatio K n i k)

/-- The actual normalized distinguished coordinate is the regular constant one. -/
theorem polynomialProjCoordinateRegularRatio_self (i : Fin (n + 1)) :
    polynomialProjCoordinateRegularRatio K n i i = 1 := by
  simp [polynomialProjCoordinateRegularRatio, polynomialProjCoordinateRatio_self]

/-- The literal canonical top differential section on its actual coordinate open. -/
def polynomialProjCanonicalCoordinateGenerator (i : Fin (n + 1)) :
    bundleSections (exteriorCotangentSheaf (polynomialProjStructureMap K n) n)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)) :=
  exteriorSheafSection (cotangentPresheaf (polynomialProjStructureMap K n)) n _
    (fun a ↦ (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
      (polynomialProjCoordinateRegularRatio K n i (i.succAbove a)))

/-- The true coordinate intersection inclusion into its left chart. -/
def polynomialProjOverlapLeftInclusion (i j : Fin (n + 1)) :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X i * MvPolynomial.X j) ⟶
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i) :=
  homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩)

/-- The true coordinate intersection inclusion into its right chart. -/
def polynomialProjOverlapRightInclusion (i j : Fin (n + 1)) :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X i * MvPolynomial.X j) ⟶
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) :=
  homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, mul_comm _ _⟩)

/-- Actual left ratio sections restrict to their actual homogeneous overlap images. -/
theorem polynomialProjCoordinateRegularRatio_restrict_left (i j k : Fin (n + 1)) :
    (polynomialProj K n).presheaf.map (polynomialProjOverlapLeftInclusion K n i j).op
      (polynomialProjCoordinateRegularRatio K n i k) = polynomialProjOverlapRegularRatio K n i j k := by
  have h := Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.isHomogeneous_X K j) (f := MvPolynomial.X i) rfl
  exact (congr($(h).hom (polynomialProjCoordinateRatio K n i k))).symm

/-- Actual right ratio sections restrict through the same genuine overlap ring. -/
theorem polynomialProjCoordinateRegularRatio_restrict_right (i j k : Fin (n + 1)) :
    (polynomialProj K n).presheaf.map (polynomialProjOverlapRightInclusion K n i j).op
      (polynomialProjCoordinateRegularRatio K n j k) = polynomialProjOverlapSectionMap K n i j
        (polynomialProjOverlapRight K n i j (polynomialProjCoordinateRatio K n j k)) := by
  have h := Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.isHomogeneous_X K i) (f := MvPolynomial.X j) (mul_comm _ _)
  exact (congr($(h).hom (polynomialProjCoordinateRatio K n j k))).symm

/-- The genuine left canonical generator restricts to the literal overlap differential product. -/
theorem polynomialProjCanonicalCoordinateGenerator_restrict_left (i j : Fin (n + 1)) :
    (exteriorCotangentSheaf (polynomialProjStructureMap K n) n).val.map
      (polynomialProjOverlapLeftInclusion K n i j).op (polynomialProjCanonicalCoordinateGenerator K n i) =
        polynomialProjOverlapCanonicalGenerator K n i j := by
  refine (exteriorSheafSection_restrict (cotangentPresheaf (polynomialProjStructureMap K n)) n
    (polynomialProjOverlapLeftInclusion K n i j)
    (fun a ↦ (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
      (polynomialProjCoordinateRegularRatio K n i (i.succAbove a)))).trans ?_
  congr 1
  funext a
  exact ((cotangentPresheafDerivation (polynomialProjStructureMap K n)).d_map
    (polynomialProjOverlapLeftInclusion K n i j).op _).symm.trans
      (congrArg (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
        (polynomialProjCoordinateRegularRatio_restrict_left K n i j (i.succAbove a)))

/-- The genuine right canonical generator restricts to its literal product on the same overlap. -/
theorem polynomialProjCanonicalCoordinateGenerator_restrict_right (i j : Fin (n + 1)) :
    (exteriorCotangentSheaf (polynomialProjStructureMap K n) n).val.map
      (polynomialProjOverlapRightInclusion K n i j).op (polynomialProjCanonicalCoordinateGenerator K n j) =
        polynomialProjOverlapRightCanonicalGenerator K n i j := by
  refine (exteriorSheafSection_restrict (cotangentPresheaf (polynomialProjStructureMap K n)) n
    (polynomialProjOverlapRightInclusion K n i j)
    (fun a ↦ (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
      (polynomialProjCoordinateRegularRatio K n j (j.succAbove a)))).trans ?_
  congr 1
  funext a
  exact ((cotangentPresheafDerivation (polynomialProjStructureMap K n)).d_map
    (polynomialProjOverlapRightInclusion K n i j).op _).symm.trans
      (congrArg (cotangentPresheafDerivation (polynomialProjStructureMap K n)).d
        (polynomialProjCoordinateRegularRatio_restrict_right K n i j (j.succAbove a)))

/-- Genuine projective canonical generators restrict with the proved actual
Jacobian determinant, as an equality of actual canonical sheaf sections. -/
theorem polynomialProjCanonicalCoordinateGenerator_overlap (i j : Fin (n + 1)) :
    (exteriorCotangentSheaf (polynomialProjStructureMap K n) n).val.map
      (polynomialProjOverlapRightInclusion K n i j).op (polynomialProjCanonicalCoordinateGenerator K n j) =
      ((-1 : Γ(polynomialProj K n, Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j))) ^
        (i.val + j.val) * (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹)) ^ (n + 1)) •
          (exteriorCotangentSheaf (polynomialProjStructureMap K n) n).val.map
            (polynomialProjOverlapLeftInclusion K n i j).op (polynomialProjCanonicalCoordinateGenerator K n i) := by
  rw [polynomialProjCanonicalCoordinateGenerator_restrict_left,
    polynomialProjCanonicalCoordinateGenerator_restrict_right,
    polynomialProjOverlapCanonicalGenerator_transition]

end ActualProjectiveOverlap
end
end SGPT.Foundations.Schemes
