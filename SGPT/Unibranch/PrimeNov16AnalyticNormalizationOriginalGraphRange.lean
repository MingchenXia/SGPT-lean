import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGoodIso
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper

/-! Actual full good-locus inverse and proper closed range.
Blueprint: prime-nov16-analytic-normalization-original-graph-range.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRange
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGoodIso
open HironakaActualAnalyticSubspaceOpenRestriction

variable {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
  (hC : IsComplexAnalyticSubset (n := n) C)
  (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
  (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)

theorem original_good_point_mem_range (b : C) (hb : H b.val.val ≠ 0) :
    b ∈ range (projection U hC H G hH hG).hom.left.base := by
  let x : ((Subtype.val : goodBase U H hH → U) ⁻¹' C) := ⟨⟨b.val,hb⟩,b.property⟩
  let q := (goodIso U hC H G hH hG).hom.base x
  let p : graphClosure U C H G := ⟨q.val.val,q.property⟩
  refine ⟨p,?_⟩
  have he := congrArg (fun f => f.base x) (goodIso_hom_over U hC H G hH hG)
  exact he

theorem original_closure_good_subset_range
    (hp : IsProperMap (projection U hC H G hH hG).hom.left.base) :
    closure {b : C | H b.val.val ≠ 0} ⊆
      range (projection U hC H G hH hG).hom.left.base := by
  apply closure_minimal
  · intro b hb
    exact original_good_point_mem_range U hC H G hH hG b hb
  · exact hp.isClosed_range

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRange
