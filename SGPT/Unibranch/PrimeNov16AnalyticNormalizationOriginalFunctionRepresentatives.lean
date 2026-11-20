import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDivisionIdeal

/-! Actual arbitrary original stalk representatives and the ENTIRE original carrier kernel.
Blueprint: prime-nov16-analytic-normalization-original-function-representatives.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_original_stalk_function_representative (C : Set M) (p : C)
    (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier) :
    ∃ (F : M → ℂ) (hF : HolomorphicAt n F p.val),originalFunctionImage C p F hF=r := by
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective (e r)
  obtain ⟨F,hF,hFa⟩ := exists_original_function_chart p.val a
  refine ⟨F,hF,e.injective ?_⟩
  change e (e.symm (Ideal.Quotient.mk _
    (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) F hF))) = e r
  rw [e.apply_symm_apply,hFa,ha]

theorem original_function_image_zero_iff (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (p : C) (F : M → ℂ) (hF : HolomorphicAt n F p.val) :
    originalFunctionImage C p F hF=0 ↔ (vanishingIdeal (n := n) C).mem p.val F := by
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  have hE : e (originalFunctionImage C p F hF) =
      Ideal.Quotient.mk _ (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) F hF) :=
    e.apply_symm_apply _
  have hPC : (vanishingIdeal (n := n) C).IsCoherent := CartanIrreducible.cartanCoherence C hC
  rw [← chart_mem_whole_iff _ hPC p.val F hF,← Ideal.Quotient.eq_zero_iff_mem]
  rw [← hE]
  exact (map_eq_zero_iff e e.injective).symm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
