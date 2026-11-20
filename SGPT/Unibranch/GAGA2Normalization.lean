import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Finiteness of the normalization of a finitely generated domain in characteristic zero

Let `R` be a domain that is a finitely generated algebra over a field `k` of characteristic
zero. Then the integral closure `R'` of `R` in its fraction field is a finite `R`-module
(`finite_integralClosure_of_finiteType`).

Proof: Noether normalization (Mathlib `exists_finite_inj_algHom_of_fg`) gives a finite
injective `k[y₁, …, y_s] → R`. The fraction field `K` of `R` is a finite extension of
`F = k(y₁, …, y_s)` (localization of a finite module), separable because the characteristic
is zero. As `k[y]` is a Noetherian integrally closed domain, its integral closure in `K` is a
Noetherian `k[y]`-module (Mathlib `IsIntegralClosure.isNoetherian`, via the trace form). This
integral closure contains `R'`, since `R` is integral over `k[y]`.

This is step U3(b) of the plan of `claude-serre-gaga.tex` (the normalization of
`𝒪_{𝒳,x}` in `prop:unibranch_gaga`).
-/

set_option autoImplicit false

open scoped nonZeroDivisors
open Algebra

namespace SGPT.Unibranch

attribute [local instance] FractionRing.liftAlgebra

/-- **Finiteness of the normalization.** The integral closure of a finitely generated domain
over a field of characteristic zero in its fraction field is a finite module. -/
theorem finite_integralClosure_of_finiteType (k R : Type*) [Field k] [CharZero k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin s) k
  let K := FractionRing R
  let : Algebra P R := g.toRingHom.toAlgebra
  have : Module.Finite P R := hfin
  have : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hinj
  have : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective R K).comp hinj)
  have : Algebra.IsIntegral P R := Algebra.IsIntegral.of_finite P R
  have : IsLocalization (algebraMapSubmonoid R P⁰) K := inferInstance
  have : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  have : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P R P⁰
  have : CharZero (FractionRing P) :=
    charZero_of_injective_algebraMap (algebraMap k (FractionRing P)).injective
  have : Algebra.IsIntegral (FractionRing P) K := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsSeparable (FractionRing P) K := Algebra.IsSeparable.of_integral _ _
  have hN : IsNoetherian P (integralClosure P K) :=
    IsIntegralClosure.isNoetherian P (FractionRing P) K (integralClosure P K)
  -- every element of the integral closure of `R` is integral over `P`
  have hle : ∀ x : integralClosure R K, IsIntegral P (x : K) := fun x =>
    isIntegral_trans (R := P) (A := R) _ x.property
  let f : integralClosure R K →ₗ[P] integralClosure P K :=
    { toFun := fun x => ⟨x, hle x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun p x => by
        apply Subtype.ext
        simp only [RingHom.id_apply]
        rfl }
  have hf : Function.Injective f := by
    intro x y h
    have h' : ((f x : integralClosure P K) : K) = ((f y : integralClosure P K) : K) := by rw [h]
    exact Subtype.ext h'
  have : IsNoetherian P (integralClosure R K) := isNoetherian_of_injective f hf
  exact Module.Finite.of_restrictScalars_finite P R _

end SGPT.Unibranch
