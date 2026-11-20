import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseRegular
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseDensity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRange

/-! SAME original denominator and proper closed range give onto on ONE true base open.
Blueprint: prime-nov16-analytic-normalization-original-base-onto.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseOnto
open PrimeNov16AnalyticNormalizationOriginalBaseRegular
open PrimeNov16AnalyticNormalizationOriginalBaseDensity
open PrimeNov16AnalyticNormalizationOriginalGraphRange
open PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
open PrimeNov16AnalyticNormalizationDenominatorGraph

theorem exists_original_open_onto {n k : ℕ} {Z : Set (ComplexModel n)}
    (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' Z))
    (p : ((Subtype.val : U → ComplexModel n) ⁻¹' Z)) (hp : p.val.val=0)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (hHg : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ H z)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → H z=0)
    (hproper : IsProperMap (projection U hC H G hH hG).hom.left.base) :
    ∃ V : Set U,IsOpen V ∧ p.val ∈ V ∧
      ∀ b : ((Subtype.val : U → ComplexModel n) ⁻¹' Z),b.val ∈ V →
        b ∈ range (projection U hC H G hH hG).hom.left.base := by
  have hHs : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (H ∘ Subtype.val : U → ℂ) :=
    (contDiffOn_of_differentiableOn_complex hH U.isOpen).contMDiffOn.comp_contMDiff
      contMDiff_subtype_val (fun z => z.property)
  obtain ⟨V,hV,hpV,hreg⟩ := exists_original_open_entire_stalk_regular
    ((Subtype.val : U → ComplexModel n) ⁻¹' Z) hC p (H ∘ Subtype.val) hHs
    (original_central_denominator_regular hZ U p hp H hHg hne
      (Eventually.of_forall fun z => hHs.mdifferentiable (by simp) z))
  refine ⟨V,hV,hpV,fun b hb => ?_⟩
  exact original_closure_good_subset_range U hC H G hH hG hproper
    (original_denominator_dense _ hC (H ∘ Subtype.val) hHs V hreg b hb)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseOnto
