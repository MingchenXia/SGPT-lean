import SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalBranchProduct
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra

/-! Genuine reduced ORIGINAL stalk test; all canonical branches are internally produced.
Blueprint: prime-nov16-analytic-normalization-original-reduced-test.tex.
Actual power-denominator and all-branch regularity remain geometric premises. -/
set_option autoImplicit false
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedTest
open PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationBranches

theorem original_stalk_normal_of_actual_radical_test (X : SourceReducedComplexSpace)
    (x : X.obj.left) (h : (X.obj.left.presheaf.stalk x).carrier)
    (hreg : normalBranchMap (X.obj.left.presheaf.stalk x).carrier h ∈
      nonZeroDivisors (NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier))
    (hpower : ∃ N : ℕ,∀ b : NormalBranchAlgebra (X.obj.left.presheaf.stalk x).carrier,
      ∃ a : (X.obj.left.presheaf.stalk x).carrier,
        normalBranchMap (X.obj.left.presheaf.stalk x).carrier (h^N)*b =
          normalBranchMap (X.obj.left.presheaf.stalk x).carrier a)
    (htest : (((Ideal.span {h}).radical)*Ideal.span {h}).colon
      ((Ideal.span {h}).radical : Set (X.obj.left.presheaf.stalk x).carrier) = Ideal.span {h}) :
    IsDomain (X.obj.left.presheaf.stalk x).carrier ∧ IsIntegrallyClosed (X.obj.left.presheaf.stalk x).carrier := by
  let A := (X.obj.left.presheaf.stalk x).carrier
  let B := NormalBranchAlgebra A
  let : IsNoetherianRing A := original_stalk_noetherian X x
  let : Module.Finite A B := original_normal_branch_algebra_finite X x
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : ∀ p : minimalPrimes A,IsDomain (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) := fun p => by
    let : IsDomain (A ⧸ p.val) := branch_isDomain A p
    infer_instance
  let : ∀ p : minimalPrimes A,IsIntegrallyClosed (integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val))) :=
    fun p => normal_branch_factor A p
  have hf := original_normalBranchMap_injective X x
  have hs := PrimeNov16AnalyticNormalizationIntegralExtensionTest.surjective_of_radical_test_and_power_denominator
    hf h hreg hpower htest
  exact PrimeNov16AnalyticNormalizationLocalBranchProduct.local_of_bijective_normal_product
    (fun p : minimalPrimes A => integralClosure (A ⧸ p.val) (FractionRing (A ⧸ p.val)))
    (normalBranchMap A) hf hs

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedTest
