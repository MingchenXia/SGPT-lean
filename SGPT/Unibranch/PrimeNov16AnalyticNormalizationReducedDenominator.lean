import SGPT.Unibranch.PrimeNov16AnalyticNormalizationTotalFractionBranches
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra
import Mathlib.RingTheory.Localization.Integer

/-! Entire original reduced normal branch algebra in the literal total fraction ring.
Blueprint: prime-nov16-analytic-normalization-reduced-denominator.tex. -/
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedDenominator
open PrimeNov16AnalyticNormalizationBranches
open PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationTotalFractionBranches

def branchFieldInclusion (A : Type*) [CommRing A] :
    NormalBranchAlgebra A →ₐ[A] BranchFractionProduct A where
  toFun b p := (b p).val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem branchFieldInclusion_injective (A : Type*) [CommRing A] :
    Function.Injective (branchFieldInclusion A) := by
  intro b c h
  funext p
  exact Subtype.ext (congrFun h p)

def branchTotalFractionEmbedding (A : Type*) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] : NormalBranchAlgebra A →ₐ[A] FractionRing A :=
  (fractionBranchEquiv A).symm.toAlgHom.comp (branchFieldInclusion A)

theorem branchTotalFractionEmbedding_injective (A : Type*) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] : Function.Injective (branchTotalFractionEmbedding A) :=
  (fractionBranchEquiv A).symm.injective.comp (branchFieldInclusion_injective A)

theorem exists_entire_branch_denominator (A : Type*) [CommRing A] [IsReduced A]
    [IsNoetherianRing A] [Module.Finite A (NormalBranchAlgebra A)] :
    ∃ h : nonZeroDivisors A, ∀ b : NormalBranchAlgebra A, ∃ a : A,
      algebraMap A (FractionRing A) a =
        algebraMap A (FractionRing A) h.val * branchTotalFractionEmbedding A b := by
  classical
  let E := branchTotalFractionEmbedding A
  obtain ⟨N,s,hs⟩ := Module.Finite.exists_fin (R := A) (M := NormalBranchAlgebra A)
  obtain ⟨h,hh⟩ := IsLocalization.exist_integer_multiples_of_finite A⁰
    (fun i : Fin N => E (s i))
  let S : Submodule A (NormalBranchAlgebra A) := {
    carrier := fun b => IsLocalization.IsInteger A (h.val • E b)
    zero_mem' := by
      change IsLocalization.IsInteger A (h.val • E 0)
      simpa using (IsLocalization.isInteger_zero (R := A) (S := FractionRing A))
    add_mem' := by
      intro b c hb hc
      change IsLocalization.IsInteger A (h.val • E (b+c))
      simpa only [map_add,smul_add] using IsLocalization.isInteger_add hb hc
    smul_mem' := by
      intro a b hb
      change IsLocalization.IsInteger A (h.val • E (a • b))
      rw [map_smul,smul_comm]
      exact IsLocalization.isInteger_smul hb }
  have hspan : Submodule.span A (Set.range s) ≤ S := by
    apply Submodule.span_le.mpr
    rintro b ⟨i,rfl⟩
    exact hh i
  rw [hs] at hspan
  refine ⟨h,fun b => ?_⟩
  obtain ⟨a,ha⟩ := hspan (show b ∈ (⊤ : Submodule A (NormalBranchAlgebra A)) from trivial)
  exact ⟨a,by simpa only [Algebra.smul_def] using ha⟩

theorem original_stalk_entire_branch_denominator (X : SourceReducedComplexSpace)
    (x : X.obj.left) :
    let A := (X.obj.left.presheaf.stalk x).carrier
    let _ : IsReduced A := X.isReduced_stalk x
    let _ : IsNoetherianRing A := original_stalk_noetherian X x
    ∃ h : nonZeroDivisors A, ∀ b : NormalBranchAlgebra A, ∃ a : A,
      algebraMap A (FractionRing A) a =
        algebraMap A (FractionRing A) h.val * branchTotalFractionEmbedding A b := by
  let A := (X.obj.left.presheaf.stalk x).carrier
  have := X.isReduced_stalk x
  let : IsNoetherianRing A := original_stalk_noetherian X x
  let : Module.Finite A (NormalBranchAlgebra A) := original_normal_branch_algebra_finite X x
  exact exists_entire_branch_denominator A

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedDenominator
