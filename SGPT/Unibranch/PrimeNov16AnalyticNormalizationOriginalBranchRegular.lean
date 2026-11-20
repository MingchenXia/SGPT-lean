import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedDenominator

/-! A genuine original NZD is regular on ALL actual canonical normal branches.
Blueprint: prime-nov16-analytic-normalization-original-branch-regular.tex. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRegular
open PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationReducedDenominator
open PrimeNov16AnalyticNormalizationTotalFractionBranches

theorem normalBranchMap_regular_of_original_nzd (A : Type*) [CommRing A]
    (q : A) (hq : q ∈ nonZeroDivisors A) :
    normalBranchMap A q ∈ nonZeroDivisors (NormalBranchAlgebra A) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro b hb
  apply branchFieldInclusion_injective A
  rw [map_zero]
  have hz := congrArg (branchFieldInclusion A) hb
  rw [map_mul,map_zero] at hz
  have hcoeff : branchFieldInclusion A (normalBranchMap A q)=branchFractionMap A q :=
    (branchFieldInclusion A).commutes q
  rw [hcoeff] at hz
  exact (IsUnit.mul_left_eq_zero (branchFractionMap_units A ⟨q,hq⟩)).mp ((mul_comm _ _).trans hz)

theorem original_stalk_all_branch_regular (X : SourceReducedComplexSpace)
    (x : X.obj.left) (q : (X.obj.left.presheaf.stalk x).carrier)
    (hq : q ∈ nonZeroDivisors (X.obj.left.presheaf.stalk x).carrier) :
    normalBranchMap (X.obj.left.presheaf.stalk x).carrier q ∈
      nonZeroDivisors (NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier) :=
  normalBranchMap_regular_of_original_nzd _ q hq

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRegular
