import SGPT.Unibranch.GAGA2Normalization
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import SGPT.Foundations.Schemes.NativeFanoAffineChartDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.Integer

/-! Actual original affine normalization in the SAME function field,
finite and with a manufactured nonzero conductor. No smoothness required.
Blueprint: original-finite-normalization-conductor.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped nonZeroDivisors

/-- Actual integral closure finiteness for ANY prescribed actual fraction
field, not silently renamed FractionRing. Genuine field/closure isos. -/
theorem originalIntegralClosure_finite_in_sameFractionField
    (k R K : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let : Module.Finite R (integralClosure R (FractionRing R)) :=
    SGPT.Unibranch.finite_integralClosure_of_finiteType k R
  exact Module.Finite.equiv ((FractionRing.algEquiv R K).mapIntegralClosure).toLinearEquiv

/-- A true finite original subalgebra of a fraction field has one NONZERO
original denominator clearing EVERY element, manufactured from actual finite
generators. No conductor, localization-isomorphism or comparison input. -/
theorem originalFiniteSubalgebra_exists_nonzero_conductor
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) [Module.Finite R S] :
    ∃ c : R, c ≠ 0 ∧ ∀ x : S, ∃ r : R, algebraMap R K r = algebraMap R K c * (x : K) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples R⁰ s (fun x : S => (x : K))
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.property, ?_⟩
  intro x
  have hx : x ∈ Submodule.span R (s : Set S) := by rw [hs]; trivial
  have h : ∀ y ∈ Submodule.span R (s : Set S),
      ∃ r : R, algebraMap R K r = (c : R) • (y : K) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => exact ⟨0, by simp⟩
    | add y z hy hz iy iz =>
      obtain ⟨a, ha⟩ := iy
      obtain ⟨b, hb⟩ := iz
      exact ⟨a + b, by simp only [map_add, Subalgebra.coe_add, smul_add, ha, hb]⟩
    | smul a y hy iy =>
      obtain ⟨b, hb⟩ := iy
      refine ⟨a * b, ?_⟩
      rw [map_mul, hb]
      rw [Subalgebra.coe_smul]
      simp only [Algebra.smul_def]
      ring
  simpa only [Algebra.smul_def] using h x hx

/-- The original affine normalization's genuine nonzero conductor is
manufactured without a finiteness/conductor premise. -/
theorem originalIntegralClosure_exists_nonzero_conductor
    (k R K : Type*) [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ c : R, c ≠ 0 ∧ ∀ x : integralClosure R K,
      ∃ r : R, algebraMap R K r = algebraMap R K c * (x : K) := by
  let := originalIntegralClosure_finite_in_sameFractionField k R K
  exact originalFiniteSubalgebra_exists_nonzero_conductor R K (integralClosure R K)

section OriginalScheme
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]

include f E hU in
/-- ANY SAME original nonempty affine chart of an arbitrary integral
projective scheme has finite normalization in the SAME ORIGINAL function
field. In particular this applies to every singular integral projective
curve chart. No smoothness or normalization finiteness input. -/
theorem originalAffineNormalization_finite :
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) := by
  let := E.isProper
  let := affineChartAlgebra f U
  let : Algebra.FiniteType ℂ Γ(X, U) := affineChartAlgebra_finiteType f hU
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  exact originalIntegralClosure_finite_in_sameFractionField ℂ Γ(X, U) X.functionField

include f E hU in
/-- Actual original affine normalization rings are Noetherian, with all
finiteness supplied by SAME original projective data. -/
theorem originalAffineNormalization_isNoetherian :
    IsNoetherianRing (integralClosure Γ(X, U) X.functionField) := by
  let := E.affineSections_isNoetherian hU
  let := originalAffineNormalization_finite f E hU
  exact IsNoetherianRing.of_finite Γ(X, U) _

include hU in
/-- Actual original affine normalization is a NORMAL domain in the SAME
original fraction field; no normality/normalization output certificate. -/
theorem originalAffineNormalization_isIntegrallyClosed :
    IsIntegrallyClosed (integralClosure Γ(X, U) X.functionField) := by
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  exact integralClosure.isIntegrallyClosedOfFiniteExtension X.functionField

include f E hU in
/-- An ACTUAL nonzero original chart function clears EVERY element of the
ENTIRE SAME actual affine normalization, for arbitrary integral projective
schemes, including singular curves. No conductor certificate is assumed. -/
theorem originalAffineNormalization_exists_nonzero_conductor :
    ∃ c : Γ(X, U), c ≠ 0 ∧ ∀ x : integralClosure Γ(X, U) X.functionField,
      ∃ r : Γ(X, U), algebraMap Γ(X, U) X.functionField r =
        algebraMap Γ(X, U) X.functionField c * (x : X.functionField) := by
  let := originalAffineNormalization_finite f E hU
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  exact originalFiniteSubalgebra_exists_nonzero_conductor Γ(X, U) X.functionField _

end OriginalScheme
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
