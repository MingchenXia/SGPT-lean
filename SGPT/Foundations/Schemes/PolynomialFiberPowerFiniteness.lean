import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
/-!
# PolynomialFiberPowerFiniteness

The actual polynomial homomorphism fixing coefficients and sending the variable to its positive qth power is finite. The target carries its actual nonidentity source algebra and module actions; integrality of the variable and actual monomial generation give finiteness.
-/

open Polynomial
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option maxHeartbeats 400000

/-- The literal polynomial coefficient map of fiberwise qth powers. -/
def polynomialFiberPowerHom (R : Type u) [CommRing R] (q : ℕ) : R[X] →+* R[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ q)

@[simp]
theorem polynomialFiberPowerHom_C (R : Type u) [CommRing R] (q : ℕ) (r : R) :
    polynomialFiberPowerHom R q (Polynomial.C r) = Polynomial.C r := by
  simp [polynomialFiberPowerHom]

@[simp]
theorem polynomialFiberPowerHom_X (R : Type u) [CommRing R] (q : ℕ) :
    polynomialFiberPowerHom R q Polynomial.X = (Polynomial.X : R[X]) ^ q := by
  simp [polynomialFiberPowerHom]

/-- Positive fiber powers give finite actual polynomial ring homomorphisms over arbitrary bases. -/
theorem polynomialFiberPowerHom_finite (R : Type u) [CommRing R] (q : ℕ) (hq : 0 < q) :
    (polynomialFiberPowerHom R q).Finite := by
  let f := polynomialFiberPowerHom R q
  let := f.toAlgebra
  let : Module R[X] R[X] := f.toAlgebra.toModule
  have hpow : IsIntegral R[X] ((Polynomial.X : R[X]) ^ q) := by
    have h : IsIntegral R[X] (algebraMap R[X] R[X] Polynomial.X) := isIntegral_algebraMap
    simpa only [RingHom.algebraMap_toAlgebra, f, polynomialFiberPowerHom_X] using h
  have hX : IsIntegral R[X] (Polynomial.X : R[X]) := hpow.of_pow hq
  have hall (p : R[X]) : p ∈ Algebra.adjoin R[X] ({Polynomial.X} : Set R[X]) := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => exact add_mem hp hr
    | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      apply mul_mem
      · have hc := (Algebra.adjoin R[X] ({Polynomial.X} : Set R[X])).algebraMap_mem (Polynomial.C r)
        simpa only [RingHom.algebraMap_toAlgebra, f, polynomialFiberPowerHom_C] using hc
      · exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton Polynomial.X)) n
  have htop : Algebra.adjoin R[X] ({Polynomial.X} : Set R[X]) = ⊤ := top_unique (fun p _ ↦ hall p)
  have hfg := hX.fg_adjoin_singleton
  rw [htop] at hfg
  exact ⟨hfg⟩

end
end SGPT.Foundations.Schemes
