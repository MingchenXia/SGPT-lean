import SGPT.Unibranch.PrimeNov16AnalyticNormalizationJointFractions
import Mathlib.Algebra.Group.Pi.Units

/-! Actual canonical total-fraction/all-minimal-branch field algebra equivalence.
Blueprint: prime-nov16-analytic-normalization-total-fraction-branches.tex. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationTotalFractionBranches
open PrimeNov16AnalyticNormalizationBranches
open PrimeNov16AnalyticNormalizationBranchSeparators
open PrimeNov16AnalyticNormalizationJointFractions

instance branchFractionAlgebra (A : Type*) [CommRing A] (p : minimalPrimes A) :
    Algebra A (FractionRing (A ⧸ p.val)) :=
  ((algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val))).comp (Ideal.Quotient.mk p.val)).toAlgebra

abbrev BranchFractionProduct (A : Type*) [CommRing A] := ∀ p : minimalPrimes A,FractionRing (A ⧸ p.val)

def branchFractionMap (A : Type*) [CommRing A] : A →+* BranchFractionProduct A :=
  algebraMap A (BranchFractionProduct A)

theorem branchFractionMap_injective (A : Type*) [CommRing A] [IsReduced A] :
    Function.Injective (branchFractionMap A) := by
  intro a b hab
  apply branchMap_injective A
  funext p
  exact IsFractionRing.injective (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (congrFun hab p)

theorem branchFractionMap_units (A : Type*) [CommRing A] (h : nonZeroDivisors A) :
    IsUnit (branchFractionMap A h.val) := by
  apply Pi.isUnit_iff.mpr
  intro p
  let : p.val.IsPrime := p.property.isPrime
  have hn : Ideal.Quotient.mk p.val h.val ≠ 0 := fun hz =>
    nonZeroDivisor_avoids_minimal_primes A h.val h.property p (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  change IsUnit (algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val h.val))
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (IsFractionRing.injective (A ⧸ p.val) (FractionRing (A ⧸ p.val))).ne hn

def fractionBranchEquiv (A : Type*) [CommRing A] [IsReduced A] [IsNoetherianRing A] :
    FractionRing A ≃ₐ[A] BranchFractionProduct A := by
  let j : FractionRing A →+* BranchFractionProduct A :=
    IsLocalization.lift (branchFractionMap_units A)
  have hj : Function.Injective j := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := nonZeroDivisors A) (S := FractionRing A) j
    intro a ha
    have hz : a=0 := by
      apply branchFractionMap_injective A
      rw [map_zero]
      simpa only [j,IsLocalization.lift_eq] using ha
    rw [hz,map_zero]
  have hs : Function.Surjective j := by
    apply (IsLocalization.lift_surjective_iff (branchFractionMap_units A)).mpr
    intro u
    obtain ⟨h,hh,g,hgu⟩ := exists_joint_fraction_denominator A u
    refine ⟨(g,⟨h,hh⟩),?_⟩
    funext p
    change u p*algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val h) =
      algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val g)
    exact (mul_comm _ _).trans (hgu p).symm
  let J : FractionRing A →ₐ[A] BranchFractionProduct A :=
    { j with commutes' := fun a => IsLocalization.lift_eq (branchFractionMap_units A) a }
  exact AlgEquiv.ofBijective J ⟨hj,hs⟩

theorem fractionBranchEquiv_coefficients (A : Type*) [CommRing A] [IsReduced A] [IsNoetherianRing A]
    (a : A) : fractionBranchEquiv A (algebraMap A (FractionRing A) a) = branchFractionMap A a :=
  (fractionBranchEquiv A).commutes a

def original_stalk_fraction_branch_equiv (X : SourceReducedComplexSpace) (x : X.obj.left) :
    FractionRing (X.obj.left.presheaf.stalk x).carrier ≃ₐ[(X.obj.left.presheaf.stalk x).carrier]
      BranchFractionProduct (X.obj.left.presheaf.stalk x).carrier := by
  let : IsNoetherianRing (X.obj.left.presheaf.stalk x).carrier := original_stalk_noetherian X x
  have := X.isReduced_stalk x
  exact fractionBranchEquiv _

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationTotalFractionBranches
