import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedBaseRegular
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseDensity

/-! Actual central reduced branch avoidance spreads to ONE entire-original-stalk regular dense window.
Blueprint: prime-nov16-analytic-normalization-original-reduced-regular-window.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedRegularWindow
open PrimeNov16AnalyticNormalizationOriginalReducedBaseRegular
open PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
open PrimeNov16AnalyticNormalizationOriginalBaseDensity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue

theorem exists_original_reduced_regular_dense_window {n k : ℕ} {Z : Set (ComplexModel n)}
    (B : Fin k → Set (ComplexModel n)) (hB : ∀ i,AnalyticGermDecomposition.IsIrreducibleGerm (B i))
    (hcover : Z =ᶠ[𝓝 (0 : ComplexModel n)] (⋃ i,B i))
    (P : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
    (p : ((Subtype.val : P → ComplexModel n) ⁻¹' Z)) (hp : p.val.val=0)
    (Q : ComplexModel n → ℂ)
    (hQ : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ Q z)
    (hne : ∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → Q z=0)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (Q ∘ Subtype.val : P → ℂ)) :
    ∃ V : Set P,IsOpen V ∧ p.val ∈ V ∧
      (∀ y : ((Subtype.val : P → ComplexModel n) ⁻¹' Z),y.val ∈ V →
        originalFunctionImage _ y (Q ∘ Subtype.val)
          (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0) ∧
      (∀ y : ((Subtype.val : P → ComplexModel n) ⁻¹' Z),y.val ∈ V →
        ∀ r : ((actualSubspaceSheaf (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z)).presheaf.stalk y).carrier,
          originalFunctionImage _ y (Q ∘ Subtype.val)
            (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)*r=0 → r=0) ∧
      ∀ y : ((Subtype.val : P → ComplexModel n) ⁻¹' Z),y.val ∈ V →
        y ∈ closure {z : ((Subtype.val : P → ComplexModel n) ⁻¹' Z) | Q z.val.val ≠ 0} := by
  let C := (Subtype.val : P → ComplexModel n) ⁻¹' Z
  have hc := original_central_reduced_denominator_regular B hB hcover P p hp Q hQ hne
    (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)
  obtain ⟨V,hV,hpV,hreg⟩ := exists_original_open_entire_stalk_regular C hC p
    (Q ∘ Subtype.val) hD hc
  refine ⟨V,hV,hpV,?_,hreg,?_⟩
  · intro y hy hz
    let : Nontrivial ((actualSubspaceSheaf (n := n) C).presheaf.stalk y).carrier :=
      (actualSubspaceStalkEval (n := n) C y).domain_nontrivial
    have hz1 : (1 : ((actualSubspaceSheaf (n := n) C).presheaf.stalk y).carrier)=0 :=
      hreg y hy 1 (by rw [hz,zero_mul])
    exact one_ne_zero hz1
  · exact original_denominator_dense C hC (Q ∘ Subtype.val) hD V hreg

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedRegularWindow
