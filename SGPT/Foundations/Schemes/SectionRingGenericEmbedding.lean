import SGPT.Foundations.Schemes.LineBundleSectionRing
import SGPT.Foundations.Schemes.SchemeGenericSections
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # The actual section ring in the function-field polynomial ring

One native chart containing the generic point is chosen from the genuine atlas.
Every tensor power uses the tensor power of that same frame. Products are the
actual sheaf-glued products, and their generic coefficient identity is derived.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsIntegral X]

/-- The degree-`n` generic coefficient uses the SAME native base frame in every degree. -/
def IntrinsicLineBundle.genericCoefficient (L : IntrinsicLineBundle X) (n : ℕ) :
    bundlePowerGlobalSections L.sheaf n →ₗ[Γ(X, ⊤)] X.functionField :=
  globalSectionToFunctionField ((L.atlas.frame L.atlas.genericIndex).tensorPower n)

/-- The generic coefficient is literally a chart coefficient followed by the native germ. -/
theorem IntrinsicLineBundle.genericCoefficient_eq_germ (L : IntrinsicLineBundle X) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    L.genericCoefficient n s = X.germToFunctionField (L.atlas.opens L.atlas.genericIndex)
      (atlasPowerGlobalCoefficients L.atlas n L.atlas.genericIndex s) := rfl

/-- Faithfulness follows from integral-scheme restriction and germ injectivity. -/
theorem IntrinsicLineBundle.genericCoefficient_injective (L : IntrinsicLineBundle X) (n : ℕ) :
    Function.Injective (L.genericCoefficient n) :=
  globalSectionToFunctionField_injective (L.atlas.tensorPower n)
    ((L.atlas.frame L.atlas.genericIndex).tensorPower n)

/-- The actual sheaf-glued multiplication gives multiplication of generic coefficients. -/
theorem IntrinsicLineBundle.genericCoefficient_mul (L : IntrinsicLineBundle X) (m n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf m) (t : bundlePowerGlobalSections L.sheaf n) :
    L.genericCoefficient (m + n) (atlasPowerGlobalMul L.atlas m n s t) =
      L.genericCoefficient m s * L.genericCoefficient n t := by
  simp only [L.genericCoefficient_eq_germ, atlasPowerGlobalMul_coefficients, map_mul]

/-- The actual degree-zero unit has generic coefficient one. -/
theorem IntrinsicLineBundle.genericCoefficient_one (L : IntrinsicLineBundle X) :
    L.genericCoefficient 0 (bundlePowerGlobalOne L.sheaf) = 1 := by
  rw [L.genericCoefficient_eq_germ, atlasPowerGlobalCoefficients_one, map_one]

/-- Degree-zero regular sections are represented by their actual generic germs. -/
theorem IntrinsicLineBundle.genericCoefficient_degree_zero (L : IntrinsicLineBundle X)
    (r : Γ(X, ⊤)) : L.genericCoefficient 0 r = X.germToFunctionField ⊤ r := by
  rw [L.genericCoefficient_eq_germ, atlasPowerGlobalCoefficients_degree_zero]
  exact germToFunctionField_restrict (homOfLE le_top) r

/-- A genuine homogeneous section gives its monomial in the actual function-field polynomial ring. -/
def IntrinsicLineBundle.genericMonomial (L : IntrinsicLineBundle X) (n : ℕ) :
    bundlePowerGlobalSections L.sheaf n →+ Polynomial X.functionField :=
  (Polynomial.monomial n).toAddMonoidHom.comp (L.genericCoefficient n).toAddMonoidHom

theorem IntrinsicLineBundle.genericMonomial_apply (L : IntrinsicLineBundle X) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    L.genericMonomial n s = Polynomial.monomial n (L.genericCoefficient n s) := rfl

/-- The actual section ring maps to polynomials by its genuine homogeneous coefficients. -/
def IntrinsicLineBundle.genericPolynomial (L : IntrinsicLineBundle X) :
    L.sectionRing →+* Polynomial X.functionField := by
  let := atlasPowerGradedCommRing L.atlas
  exact DirectSum.toSemiring (L.genericMonomial)
    (by
      change Polynomial.monomial 0 (L.genericCoefficient 0
        (bundlePowerGlobalOne L.sheaf)) = 1
      rw [L.genericCoefficient_one]
      rfl)
    (by
      intro m n s t
      change Polynomial.monomial (m + n)
        (L.genericCoefficient (m + n) (atlasPowerGlobalMul L.atlas m n s t)) =
        Polynomial.monomial m (L.genericCoefficient m s) *
          Polynomial.monomial n (L.genericCoefficient n t)
      rw [L.genericCoefficient_mul, Polynomial.monomial_mul_monomial])

/-- Homogeneous sections map to the monomial of their SAME-frame generic coefficient. -/
theorem IntrinsicLineBundle.genericPolynomial_ofSection (L : IntrinsicLineBundle X) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    L.genericPolynomial (L.ofSection n s) =
      Polynomial.monomial n (L.genericCoefficient n s) := by
  let := atlasPowerGradedCommRing L.atlas
  change DirectSum.toAddMonoid L.genericMonomial
    (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) = _
  exact DirectSum.toAddMonoid_of _ n s

/-- The literal degree component of the actual direct-sum section ring. -/
def IntrinsicLineBundle.degreeComponent (L : IntrinsicLineBundle X) (n : ℕ) :
    L.sectionRing →+ bundlePowerGlobalSections L.sheaf n where
  toFun x := (show ⨁ j : ℕ, bundlePowerGlobalSections L.sheaf j from x) n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extracting a polynomial coefficient recovers the actual degree component's generic coefficient. -/
theorem IntrinsicLineBundle.genericPolynomial_coeff (L : IntrinsicLineBundle X)
    (x : L.sectionRing) (n : ℕ) :
    (L.genericPolynomial x).coeff n = L.genericCoefficient n (L.degreeComponent n x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j s =>
    change (L.genericPolynomial (L.ofSection j s)).coeff n = _
    rw [L.genericPolynomial_ofSection]
    by_cases h : j = n
    · subst j
      simp [IntrinsicLineBundle.degreeComponent]
    · simp [Polynomial.coeff_monomial, h, IntrinsicLineBundle.degreeComponent,
        DirectSum.of_eq_of_ne j n s (Ne.symm h)]
  | add x y hx hy => simp only [map_add, Polynomial.coeff_add, hx, hy]

/-- Integral geometry and distinct polynomial degrees make the whole section-ring map faithful. -/
theorem IntrinsicLineBundle.genericPolynomial_injective (L : IntrinsicLineBundle X) :
    Function.Injective L.genericPolynomial := by
  intro x y h
  apply DFinsupp.ext
  intro n
  apply L.genericCoefficient_injective n
  exact (L.genericPolynomial_coeff x n).symm.trans
    ((congrArg (fun p : Polynomial X.functionField => p.coeff n) h).trans
      (L.genericPolynomial_coeff y n))

section BaseField

variable {K : Type u} [Field K]

/-- SAME-frame generic coefficient evaluation with its actual structural base-field action. -/
def IntrinsicLineBundle.genericCoefficientOverBase (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    letI := schemeFunctionFieldAlgebra f
    bundlePowerGlobalSections L.sheaf n →ₗ[K] X.functionField :=
  globalSectionToFunctionFieldOverBase f
    ((L.atlas.frame L.atlas.genericIndex).tensorPower n)

/-- The structural linear map retains the literal generic coefficient function. -/
theorem IntrinsicLineBundle.genericCoefficientOverBase_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.genericCoefficientOverBase f n s = L.genericCoefficient n s := rfl

theorem IntrinsicLineBundle.genericCoefficientOverBase_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) :
    Function.Injective (L.genericCoefficientOverBase f n) :=
  L.genericCoefficient_injective n

/-- The homogeneous coefficient space is the ACTUAL linear image of global sections. -/
def IntrinsicLineBundle.genericCoefficientSpace (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    Submodule K X.functionField := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  letI := schemeFunctionFieldAlgebra f
  exact LinearMap.range (L.genericCoefficientOverBase f n)

/-- Integral geometry identifies actual global sections with their actual coefficient image. -/
def IntrinsicLineBundle.genericCoefficientEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    letI := schemeFunctionFieldAlgebra f
    bundlePowerGlobalSections L.sheaf n ≃ₗ[K] L.genericCoefficientSpace f n := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  letI := schemeFunctionFieldAlgebra f
  exact LinearEquiv.ofInjective (L.genericCoefficientOverBase f n)
    (L.genericCoefficientOverBase_injective f n)

theorem IntrinsicLineBundle.genericCoefficientEquiv_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    (L.genericCoefficientEquiv f n s : X.functionField) = L.genericCoefficient n s := rfl

/-- Products of actual coefficient images lie in the corresponding actual sum degree. -/
theorem IntrinsicLineBundle.genericCoefficientSpace_mul_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (m n : ℕ) {x y : X.functionField} :
    x ∈ L.genericCoefficientSpace f m → y ∈ L.genericCoefficientSpace f n →
      x * y ∈ L.genericCoefficientSpace f (m + n) := by
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  refine ⟨atlasPowerGlobalMul L.atlas m n s t, ?_⟩
  change L.genericCoefficient (m + n) (atlasPowerGlobalMul L.atlas m n s t) = x * y
  exact (L.genericCoefficient_mul m n s t).trans (congrArg₂ (· * ·) hs ht)

/-- The degree-zero actual image contains the actual unit. -/
theorem IntrinsicLineBundle.genericCoefficientSpace_one_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) : (1 : X.functionField) ∈ L.genericCoefficientSpace f 0 :=
  ⟨bundlePowerGlobalOne L.sheaf, L.genericCoefficient_one⟩

/-- The actual polynomial representation preserves the actual structural K algebra. -/
def IntrinsicLineBundle.genericPolynomialOverBase (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) :
    letI := L.sectionRingAlgebra f
    letI := schemeFunctionFieldAlgebra f
    L.sectionRing →ₐ[K] Polynomial X.functionField := by
  letI := L.sectionRingAlgebra f
  letI := schemeFunctionFieldAlgebra f
  exact { L.genericPolynomial with
    commutes' := fun r => by
      change L.genericPolynomial (L.sectionRingBaseMap f r) =
        Polynomial.C (X.germToFunctionField ⊤ (schemeGlobalConstants f r))
      rw [L.sectionRingBaseMap_apply, L.genericPolynomial_ofSection,
        L.genericCoefficient_degree_zero, Polynomial.monomial_zero_left]
      rfl }

theorem IntrinsicLineBundle.genericPolynomialOverBase_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : L.sectionRing) :
    L.genericPolynomialOverBase f x = L.genericPolynomial x := rfl

theorem IntrinsicLineBundle.genericPolynomialOverBase_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) : Function.Injective (L.genericPolynomialOverBase f) :=
  L.genericPolynomial_injective

/-- The homogeneous polynomial representation has its actual coefficient-times-fiber factorization. -/
theorem IntrinsicLineBundle.genericPolynomialOverBase_ofSection (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.genericPolynomialOverBase f (L.ofSection n s) =
      Polynomial.C (L.genericCoefficient n s) * Polynomial.X ^ n :=
  (L.genericPolynomial_ofSection n s).trans Polynomial.C_mul_X_pow_eq_monomial.symm

/-- The actual section-ring K action agrees with the native degreewise K-module action. -/
def IntrinsicLineBundle.sectionRingDecomposition (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) :
    letI : ∀ n, Module K (bundlePowerGlobalSections L.sheaf n) :=
      fun n => schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    letI := L.sectionRingAlgebra f
    (⨁ n : ℕ, bundlePowerGlobalSections L.sheaf n) ≃ₗ[K] L.sectionRing := by
  letI : ∀ n, Module K (bundlePowerGlobalSections L.sheaf n) :=
    fun n => schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  letI := L.sectionRingAlgebra f
  exact {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro c x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n s =>
        rw [← DirectSum.of_smul]
        exact (L.sectionRing_smul_ofSection f n c s).symm
      | add x y hx hy =>
        simp only [smul_add]
        exact congrArg₂ (· + ·) hx hy }

omit [IsIntegral X] in
/-- The decomposition is literally the identity on the underlying actual direct sum. -/
theorem IntrinsicLineBundle.sectionRingDecomposition_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : ⨁ n : ℕ, bundlePowerGlobalSections L.sheaf n) :
    L.sectionRingDecomposition f x = x := rfl

omit [IsIntegral X] in
/-- Each native homogeneous inclusion under the actual linear decomposition is the section-ring inclusion. -/
theorem IntrinsicLineBundle.sectionRingDecomposition_of (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.sectionRingDecomposition f (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) =
      L.ofSection n s := rfl

/-- Replacing each actual section space by its actual coefficient image gives a genuine decomposition. -/
def IntrinsicLineBundle.genericImageDecomposition (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) :
    letI := schemeFunctionFieldAlgebra f
    letI := L.sectionRingAlgebra f
    (⨁ n : ℕ, L.genericCoefficientSpace f n) ≃ₗ[K] L.sectionRing := by
  letI := schemeFunctionFieldAlgebra f
  letI := L.sectionRingAlgebra f
  letI : ∀ n, Module K (bundlePowerGlobalSections L.sheaf n) :=
    fun n => schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  exact (DirectSum.congrLinearEquiv (fun n => (L.genericCoefficientEquiv f n).symm)).trans
    (L.sectionRingDecomposition f)

/-- The image decomposition takes a homogeneous coefficient back to its genuine global section. -/
theorem IntrinsicLineBundle.genericImageDecomposition_of (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : L.genericCoefficientSpace f n) :
    L.genericImageDecomposition f
        (DirectSum.of (fun j => L.genericCoefficientSpace f j) n s) =
      L.ofSection n ((L.genericCoefficientEquiv f n).symm s) := by
  change DirectSum.map (fun j => (L.genericCoefficientEquiv f j).symm.toAddMonoidHom)
    (DirectSum.of (fun j => L.genericCoefficientSpace f j) n s) = _
  exact DirectSum.map_of (α := fun j => L.genericCoefficientSpace f j)
    (β := bundlePowerGlobalSections L.sheaf)
    (fun j => (L.genericCoefficientEquiv f j).symm.toAddMonoidHom) n s

/-- The actual image-space decomposition has coefficient-times-fiber factorization, derived from gluing. -/
theorem IntrinsicLineBundle.genericPolynomial_image_factorization (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : L.genericCoefficientSpace f n) :
    L.genericPolynomialOverBase f (L.genericImageDecomposition f
        (DirectSum.of (fun j => L.genericCoefficientSpace f j) n s)) =
      Polynomial.C (s : X.functionField) * Polynomial.X ^ n := by
  rw [L.genericImageDecomposition_of, L.genericPolynomialOverBase_ofSection]
  apply congrArg (fun c : X.functionField => Polynomial.C c * Polynomial.X ^ n)
  exact (L.genericCoefficientEquiv_apply f n ((L.genericCoefficientEquiv f n).symm s)).symm.trans
    (congrArg (fun t : L.genericCoefficientSpace f n => (t : X.functionField))
      ((L.genericCoefficientEquiv f n).apply_symm_apply s))

/-- Every polynomial coefficient lies in the ACTUAL section coefficient image for that degree. -/
theorem IntrinsicLineBundle.genericPolynomial_coeff_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : L.sectionRing) (n : ℕ) :
    (L.genericPolynomialOverBase f x).coeff n ∈ L.genericCoefficientSpace f n :=
  ⟨L.degreeComponent n x, (L.genericPolynomial_coeff x n).symm⟩

end BaseField

end

end SGPT.Foundations.Schemes
