import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedDenominator

/-! Literal reduced canonical integral closure, including every actual branch.
Blueprint: prime-nov16-analytic-normalization-reduced-canonical-closure.tex. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedCanonicalClosure
open PrimeNov16AnalyticNormalizationBranches
open PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationTotalFractionBranches
open PrimeNov16AnalyticNormalizationReducedDenominator

def branchFractionProjection (A : Type*) [CommRing A] (p : minimalPrimes A) :
    BranchFractionProduct A →ₐ[A] FractionRing (A ⧸ p.val) where
  toFun u := u p
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def branchCanonicalMap (A : Type*) [CommRing A] [IsReduced A] [IsNoetherianRing A]
    [Module.Finite A (NormalBranchAlgebra A)] :
    NormalBranchAlgebra A →ₐ[A] integralClosure A (FractionRing A) :=
  (branchTotalFractionEmbedding A).codRestrict (integralClosure A (FractionRing A))
    (fun b => (Algebra.IsIntegral.isIntegral b).map (branchTotalFractionEmbedding A))

theorem branchCanonicalMap_bijective (A : Type*) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] [Module.Finite A (NormalBranchAlgebra A)] :
    Function.Bijective (branchCanonicalMap A) := by
  refine ⟨fun b c h => branchTotalFractionEmbedding_injective A (congrArg Subtype.val h),?_⟩
  intro x
  let e := fractionBranchEquiv A
  have hi (p : minimalPrimes A) : IsIntegral (A ⧸ p.val) (e x.val p) := by
    apply IsIntegral.map_of_comp_eq (Ideal.Quotient.mk p.val)
      ((branchFractionProjection A p).comp e.toAlgHom).toRingHom ?_ x.property
    ext a
    change branchFractionMap A a p = e (algebraMap A (FractionRing A) a) p
    exact congrFun (e.commutes a).symm p
  let b : NormalBranchAlgebra A := fun p => ⟨e x.val p,hi p⟩
  refine ⟨b,Subtype.ext ?_⟩
  change e.symm (branchFieldInclusion A b) = x.val
  apply e.injective
  rw [e.apply_symm_apply]
  rfl

def branchCanonicalEquiv (A : Type*) [CommRing A] [IsReduced A] [IsNoetherianRing A]
    [Module.Finite A (NormalBranchAlgebra A)] :
    NormalBranchAlgebra A ≃ₐ[A] integralClosure A (FractionRing A) :=
  AlgEquiv.ofBijective (branchCanonicalMap A) (branchCanonicalMap_bijective A)

theorem branchCanonicalEquiv_coefficients (A : Type*) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] [Module.Finite A (NormalBranchAlgebra A)] (a : A) :
    branchCanonicalEquiv A (normalBranchMap A a) =
      algebraMap A (integralClosure A (FractionRing A)) a :=
  (branchCanonicalEquiv A).commutes a

def original_stalk_canonical_closure_equiv (X : SourceReducedComplexSpace) (x : X.obj.left) :
    NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier ≃ₐ[(X.obj.left.presheaf.stalk x).carrier]
      integralClosure (X.obj.left.presheaf.stalk x).carrier
        (FractionRing (X.obj.left.presheaf.stalk x).carrier) := by
  let A := (X.obj.left.presheaf.stalk x).carrier
  have := X.isReduced_stalk x
  let : IsNoetherianRing A := original_stalk_noetherian X x
  let : Module.Finite A (NormalBranchAlgebra A) := original_normal_branch_algebra_finite X x
  exact branchCanonicalEquiv A

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedCanonicalClosure
