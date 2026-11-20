import SGPT.Unibranch.PrimeNov16AnalyticNormalizationPrimeQuotients

/-! Canonical finite NORMAL BRANCH algebra for EVERY actual original reduced
stalk. Not yet a total-fraction dictionary or an analytic normalization space.
Blueprint: prime-nov16-analytic-normalization-reduced-algebra.tex. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationBranches

/-- The literal coefficient composition is the A-algebra structure on a normal
branch factor; no scalar/coherence certificate is supplied. -/
instance branchClosureAlgebra (A : Type*) [CommRing A] (p : minimalPrimes A) :
    Algebra A (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) :=
  ((algebraMap (A ⧸ p.val) (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val)))).comp
    (Ideal.Quotient.mk p.val)).toAlgebra

instance branchClosureTower (A : Type*) [CommRing A] (p : minimalPrimes A) :
    IsScalarTower A (A ⧸ p.val)
      (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) :=
  IsScalarTower.of_algebraMap_eq' rfl

abbrev NormalBranchAlgebra (A : Type*) [CommRing A] :=
  ∀ p : minimalPrimes A, integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))

def normalBranchMap (A : Type*) [CommRing A] : A →+* NormalBranchAlgebra A :=
  algebraMap A (NormalBranchAlgebra A)

/-- All actual normal factors are proved integrally closed in their actual
fraction fields. Domainhood is derived from the actual minimal prime. -/
theorem normal_branch_factor (A : Type*) [CommRing A] (p : minimalPrimes A) :
    IsIntegrallyClosed (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) := by
  have : p.val.IsPrime := p.property.isPrime
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (A ⧸ p.val))

/-- No unibranch assumption: reducedness plus actual branch fraction injection
makes the SAME original coefficient map injective. -/
theorem normalBranchMap_injective (A : Type*) [CommRing A] [IsReduced A] :
    Function.Injective (normalBranchMap A) := by
  intro a b hab
  apply branchMap_injective A
  funext p
  have : p.val.IsPrime := p.property.isPrime
  have he := congrArg (fun z : NormalBranchAlgebra A =>
    ((z p : integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) : FractionRing (A ⧸ p.val))) hab
  apply IsFractionRing.injective (A ⧸ p.val) (FractionRing (A ⧸ p.val))
  exact he

/-- Actual original reduced stalks internally produce a finite normal branch
algebra. This includes all multibranch points and all local dimensions. -/
theorem original_normal_branch_algebra_finite (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Module.Finite (X.obj.left.presheaf.stalk x).carrier
      (NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier) := by
  let A := (X.obj.left.presheaf.stalk x).carrier
  have : IsNoetherianRing A := original_stalk_noetherian X x
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hfp : ∀ p : minimalPrimes A,
      Module.Finite A (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) := by
    intro p
    have : p.val.IsPrime := p.property.isPrime
    have := PrimeNov16AnalyticNormalizationPrimeQuotients.finite_original_prime_quotient_closure
      X x p.val
    exact Module.Finite.trans (A ⧸ p.val) _
  exact Module.Finite.pi (h := hfp)

theorem original_normalBranchMap_injective (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Function.Injective (normalBranchMap (X.obj.left.presheaf.stalk x).carrier) := by
  have := X.isReduced_stalk x
  exact normalBranchMap_injective _

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra
