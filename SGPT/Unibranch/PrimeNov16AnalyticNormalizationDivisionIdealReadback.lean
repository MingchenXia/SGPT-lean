import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDivisionIdeal

/-! Entire functional ideal membership is equivalent to actual original whole-stalk division.
Blueprint: prime-nov16-analytic-normalization-division-ideal-readback.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationDivisionIdealReadback
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
open RestrictedIdealExtension HironakaAnalyticBaseChangeQuotientModel
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_functional_mem_iff_division (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x : C) (D F : M → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D) (hF : HolomorphicAt n F x.val) :
    (sumIdeal (principalIdeal (n := n) D) (vanishingIdeal (n := n) C)).mem x.val F ↔
      ∃ q : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier,
        originalFunctionImage C x F hF = originalFunctionImage C x D
          (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)*q := by
  constructor
  · intro hf
    have hP := CartanIrreducible.cartanCoherence C hC
    have hDco := principalIdeal_coherent D hD
    have hmem := (chart_mem_whole_iff _ (isCoherent_sumIdeal hDco hP) x.val F hF).mpr hf
    rw [wholeChartStalkIdeal_sum _ _ hDco hP,wholeChartStalkIdeal_principal D hD] at hmem
    obtain ⟨u,hu,v,hv,hs⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hu
    let e := actualSubspaceStalkChartEquiv (n := n) C x
    let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) x.val x.val (mem_chart_source _ x.val)
    refine ⟨e.symm (Ideal.Quotient.mk P a),e.injective ?_⟩
    rw [map_mul]
    have hEF : e (originalFunctionImage C x F hF) =
        Ideal.Quotient.mk P (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) F hF) :=
      e.apply_symm_apply _
    have hED : e (originalFunctionImage C x D
        (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)) =
        Ideal.Quotient.mk P (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) D
          (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)) := e.apply_symm_apply _
    rw [hEF,hED]
    rw [e.apply_symm_apply,← hs,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hv,add_zero,ha,map_mul]
  · exact original_division_functional_mem C hC x D F hD hF

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationDivisionIdealReadback
