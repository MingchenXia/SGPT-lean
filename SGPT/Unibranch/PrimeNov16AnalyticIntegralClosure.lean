import SGPT.Foundations.Analysis.Pending.GermNoetherNormalization
import SGPT.Foundations.Analysis.Pending.GermIntegrallyClosed
import SGPT.Foundations.Analysis.Pending.HolomorphicGermNoetherian
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.RingHom.Finite

/-! Canonical finite normal algebra of an ACTUAL irreducible analytic germ.
Local branch algebra only: no analytic space, finite map, or coherence supplied.
Blueprint: prime-nov16-analytic-integral-closure.tex. -/
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open Algebra
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolGerm
namespace SGPT.Unibranch.PrimeNov16AnalyticIntegralClosure

attribute [local instance] FractionRing.liftAlgebra

/-- Finite injective analytic Noether bases prove finiteness of the canonical
closure of A itself. No integral-closure finiteness is an input. -/
theorem finite_closure_of_finite_normal_base
    (R A : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing A] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    ((IsFractionRing.injective A K).comp hinj)
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have : IsLocalization (algebraMapSubmonoid A R⁰) K := inferInstance
  have : IsScalarTower R (FractionRing R) K := FractionRing.isScalarTower_liftAlgebra R K
  have : FiniteDimensional (FractionRing R) K := Module.Finite.of_isLocalization R A R⁰
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have : Algebra.IsIntegral (FractionRing R) K := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsSeparable (FractionRing R) K := Algebra.IsSeparable.of_integral _ _
  have : IsNoetherian R (integralClosure R K) :=
    IsIntegralClosure.isNoetherian R (FractionRing R) K (integralClosure R K)
  have hle : ∀ x : integralClosure A K, IsIntegral R (x : K) := fun x =>
    isIntegral_trans (R := R) (A := A) _ x.property
  let f : integralClosure A K →ₗ[R] integralClosure R K := {
    toFun := fun x => ⟨x,hle x⟩
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r x
      apply Subtype.ext
      simp only [RingHom.id_apply]
      rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : integralClosure R K => (z : K)) h)
  have : IsNoetherian R (integralClosure A K) := isNoetherian_of_injective f hf
  exact Module.Finite.of_restrictScalars_finite R A _

/-- SAME fraction-ring elements are integral over either finite base or A. -/
theorem integral_iff_finite_base
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] (x : FractionRing A) :
    IsIntegral R x ↔ IsIntegral A x := by
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  exact ⟨fun h => h.tower_top, fun h => isIntegral_trans (R := R) (A := A) x h⟩

/-- Analytic Weierstrass Noether normalization produces a genuine finite
injective map to the ORIGINAL quotient, not merely its coordinate transform. -/
theorem exists_original_finite_analytic_base {n : ℕ}
    (P : Ideal (HolGerm (ComplexModel n))) [P.IsPrime] :
    ∃ d : ℕ, d ≤ n ∧ ∃ f : HolGerm (ComplexModel d) →+* (HolGerm (ComplexModel n) ⧸ P),
      Function.Injective f ∧ f.Finite := by
  obtain ⟨d,hd,L,-,-,-,hinj,hfin,-⟩ := exists_noetherNormalization P
  let e := Ideal.quotientEquiv P (P.map (comapEquiv L)) (comapEquiv L) rfl
  let f := e.symm.toRingHom.comp (quotientStructureMap (P.map (comapEquiv L)) d)
  refine ⟨d,hd,f,e.symm.injective.comp hinj,?_⟩
  exact (RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective).comp hfin

/-- The canonical closure is literally attached to the ACTUAL analytic germ
quotient, independent of every Noether coordinate/base choice in the proof. -/
theorem finite_analytic_germ_integralClosure {n : ℕ}
    (P : Ideal (HolGerm (ComplexModel n))) [P.IsPrime] :
    Module.Finite (HolGerm (ComplexModel n) ⧸ P)
      (integralClosure (HolGerm (ComplexModel n) ⧸ P)
        (FractionRing (HolGerm (ComplexModel n) ⧸ P))) := by
  obtain ⟨d,-,f,hinj,hfin⟩ := exists_original_finite_analytic_base P
  let R := HolGerm (ComplexModel d)
  let A := HolGerm (ComplexModel n) ⧸ P
  let : Algebra R A := f.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  have : IsNoetherianRing R := isNoetherianRing_holGerm_euclidean d
  let : Algebra ℂ R := (HolGerm.constHom (E := ComplexModel d)).toAlgebra
  have : CharZero R := charZero_of_injective_algebraMap
    (algebraMap ℂ R).injective
  exact finite_closure_of_finite_normal_base R A

/-- Genuine normality of the canonical branch algebra, not a normality field. -/
theorem normal_analytic_germ_integralClosure {n : ℕ}
    (P : Ideal (HolGerm (ComplexModel n))) [P.IsPrime] :
    IsIntegrallyClosed (integralClosure (HolGerm (ComplexModel n) ⧸ P)
      (FractionRing (HolGerm (ComplexModel n) ⧸ P))) := by
  exact integralClosure.isIntegrallyClosedOfFiniteExtension
    (FractionRing (HolGerm (ComplexModel n) ⧸ P))

end SGPT.Unibranch.PrimeNov16AnalyticIntegralClosure
