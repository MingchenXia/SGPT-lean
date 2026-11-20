import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives

/-! Actual original-stalk denominator regularity gives genuine carrier density.
Blueprint: prime-nov16-analytic-normalization-original-base-density.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseDensity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open HironakaActualAnalyticSubspace

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_denominator_dense (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (H : M → ℂ)
    (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H)
    (V : Set M)
    (hreg : ∀ p : C,p.val ∈ V →
      ∀ r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier,
        originalFunctionImage C p H
          (Eventually.of_forall fun z => hH.mdifferentiable (by simp) z)*r=0 → r=0) :
    ∀ p : C,p.val ∈ V → p ∈ closure {q : C | H q.val ≠ 0} := by
  intro p hp
  rw [mem_closure_iff]
  intro O hO hpO
  by_contra hempty
  obtain ⟨W,hW,hWO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hO
  have hpW : p.val ∈ W := by
    change p ∈ Subtype.val ⁻¹' W
    rw [hWO]
    exact hpO
  have hz : originalFunctionImage C p H
      (Eventually.of_forall fun z => hH.mdifferentiable (by simp) z)=0 := by
    apply (original_function_image_zero_iff C hC p H _).mpr
    refine ⟨Eventually.of_forall fun z => hH.mdifferentiable (by simp) z,?_⟩
    filter_upwards [hW.mem_nhds hpW] with y hy hyC
    by_contra hny
    apply hempty
    refine ⟨⟨y,hyC⟩,?_,hny⟩
    rw [← hWO]
    exact hy
  let : IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier :=
    actualSubspaceStalk_isLocalRing C p
  have hone := hreg p hp 1 (by rw [hz,zero_mul])
  exact one_ne_zero hone

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseDensity
