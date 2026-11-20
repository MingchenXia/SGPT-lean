import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion

/-! Literal carrier restriction manufactures actual original function-germ nonvanishing transport.
Blueprint: prime-nov16-analytic-normalization-original-window-function-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowFunctionGerm
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal

theorem original_function_image_nonzero_of_smaller_window {n : ℕ}
    (B : Set (ComplexModel n)) (U V : Opens (ComplexModel n)) (hUV : U ≤ V)
    (hU : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' B))
    (hV : IsComplexAnalyticSubset (n := n) ((Subtype.val : V → ComplexModel n) ⁻¹' B))
    (p : ((Subtype.val : U → ComplexModel n) ⁻¹' B)) (F : ComplexModel n → ℂ)
    (hFU : HolomorphicAt n (F ∘ Subtype.val : U → ℂ) p.val)
    (hFV : HolomorphicAt n (F ∘ Subtype.val : V → ℂ)
      (⟨p.val.val,hUV p.val.property⟩ : V))
    (hn : originalFunctionImage ((Subtype.val : U → ComplexModel n) ⁻¹' B) p
      (F ∘ Subtype.val) hFU ≠ 0) :
    originalFunctionImage ((Subtype.val : V → ComplexModel n) ⁻¹' B)
      (⟨⟨p.val.val,hUV p.val.property⟩,p.property⟩ : ((Subtype.val : V → ComplexModel n) ⁻¹' B))
      (F ∘ Subtype.val) hFV ≠ 0 := by
  intro hz
  have hvan := (original_function_image_zero_iff
    ((Subtype.val : V → ComplexModel n) ⁻¹' B) hV
    (⟨⟨p.val.val,hUV p.val.property⟩,p.property⟩ : ((Subtype.val : V → ComplexModel n) ⁻¹' B))
    (F ∘ Subtype.val) hFV).mp hz
  apply hn
  apply (original_function_image_zero_iff ((Subtype.val : U → ComplexModel n) ⁻¹' B) hU p
    (F ∘ Subtype.val) hFU).mpr
  refine ⟨hFU,?_⟩
  have ht : Filter.Tendsto (Opens.inclusion hUV) (𝓝 p.val)
      (𝓝 (⟨p.val.val,hUV p.val.property⟩ : V)) :=
    (show Continuous (Opens.inclusion hUV) from
      continuous_subtype_val.subtype_mk (fun y => hUV y.property)).continuousAt
  filter_upwards [ht hvan.2] with y hy hyB
  exact hy hyB

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowFunctionGerm
