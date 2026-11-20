import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction

/-! ENTIRE actual open stalk comparison retains literal restrictions of EVERY original function.
Blueprint: prime-nov16-analytic-normalization-original-open-function-readback.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationGraphStalkChart
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
open HironakaActualOpenIntrinsicHS HironakaActualWholeStalkHolomorphicPullback
open HironakaHolomorphicJetRankLoci HironakaActualVanishingIntrinsicHSTransport
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_open_intrinsic_germ (C : Set M) (U : Opens M)
    (x : ((Subtype.val : U → M) ⁻¹' C)) (a : HolGerm (ComplexModel n)) :
    actualOpenSubspaceStalkEquiv (n := n) C U x
      (intrinsicGermMap C ((actualOpenSubspaceMap (n := n) C U).base x) a) =
        intrinsicGermMap ((Subtype.val : U → M) ⁻¹' C) x a := by
  let p := (actualOpenSubspaceMap (n := n) C U).base x
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  let es := actualSubspaceStalkChartEquiv (n := n) ((Subtype.val : U → M) ⁻¹' C) x
  let h := (wholeChartStalkIdeal_vanishing_actual_open (n := n) U C x.val).symm
  change es.symm ((Ideal.quotEquivOfEq h) (e (e.symm (Ideal.Quotient.mk _ a)))) =
    es.symm (Ideal.Quotient.mk _ a)
  rw [e.apply_symm_apply]
  exact congrArg es.symm (Ideal.quotEquivOfEq_mk h a)

theorem original_open_chart_function (U : Opens M) (x : U) (F : M → ℂ)
    (hF : HolomorphicAt n F x.val) :
    chartTranslatedGerm x x (mem_chart_source _ x) (F ∘ Subtype.val)
      (hF.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)) =
      chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) F hF := by
  have h := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : U → M)) contMDiff_subtype_val x F hF
  rw [actualHolomorphicGermPullback_val U x] at h
  exact h.symm

theorem original_open_function_image (C : Set M) (U : Opens M)
    (x : ((Subtype.val : U → M) ⁻¹' C)) (F : M → ℂ)
    (hF : HolomorphicAt n F x.val.val) :
    actualOpenSubspaceStalkEquiv (n := n) C U x
      (originalFunctionImage C ((actualOpenSubspaceMap (n := n) C U).base x) F hF) =
        originalFunctionImage ((Subtype.val : U → M) ⁻¹' C) x (F ∘ Subtype.val)
          (hF.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)) := by
  unfold originalFunctionImage
  rw [original_open_intrinsic_germ]
  exact congrArg (intrinsicGermMap ((Subtype.val : U → M) ⁻¹' C) x)
    (original_open_chart_function U x.val F hF).symm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
