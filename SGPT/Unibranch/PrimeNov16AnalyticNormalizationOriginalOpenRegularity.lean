import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback

/-! Genuine original multiplication-kernel transport under actual ambient open restriction.
Blueprint: prime-nov16-analytic-normalization-original-open-regularity.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenRegularity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_open_multiplier_regular (C : Set M) (U : Opens M)
    (x : ((Subtype.val : U → M) ⁻¹' C)) (F : M → ℂ)
    (hF : HolomorphicAt n F x.val.val)
    (hx : ∀ r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk
        ((actualOpenSubspaceMap (n := n) C U).base x)).carrier,
      originalFunctionImage C ((actualOpenSubspaceMap (n := n) C U).base x) F hF*r=0 → r=0) :
    ∀ r : ((actualSubspaceSheaf (n := n) ((Subtype.val : U → M) ⁻¹' C)).presheaf.stalk x).carrier,
      originalFunctionImage ((Subtype.val : U → M) ⁻¹' C) x (F ∘ Subtype.val)
        (hF.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt))*r=0 → r=0 := by
  let e := actualOpenSubspaceStalkEquiv (n := n) C U x
  intro r hr
  apply e.symm.injective
  rw [map_zero]
  apply hx
  apply e.injective
  rw [map_mul,original_open_function_image,e.apply_symm_apply,map_zero]
  exact hr

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenRegularity
