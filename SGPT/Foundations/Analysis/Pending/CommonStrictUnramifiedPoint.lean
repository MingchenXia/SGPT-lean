import SGPT.Foundations.Analysis.Pending.ConstantRankImage
import SGPT.Foundations.Analysis.Pending.HolomorphicIntrinsicExceptionalAnalytic


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.CommonStrictUnramifiedPoint

open FirstPass FirstPass.BlowupSequences

universe u

variable {n : ℕ} {Y₀ Y₁ Z : Type u}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

omit [IsComplexManifold n Z] in
/-- A literal nonempty strict transform supplies a point outside its actual differential exceptional locus. -/
private theorem not_subset_exceptional_of_strict {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {g : Z → Y} (V : Set Y) (W : Set Z) (hW : W.Nonempty)
    (hstrict : W = strictTransform n g V) : ¬ W ⊆ exceptionalLocus n g := by
  have hseed : (g ⁻¹' V \ exceptionalLocus n g).Nonempty := by
    apply closure_nonempty_iff.mp
    change (strictTransform n g V).Nonempty
    rwa [← hstrict]
  obtain ⟨z, hzV, hzE⟩ := hseed
  intro hsub
  apply hzE
  apply hsub
  rw [hstrict]
  exact subset_closure ⟨hzV, hzE⟩

/-- Actual strict-transform density and analytic irreducibility produce one regular point unramified for BOTH maps. -/
theorem exists_common_regular_unramified_point
    {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀)
    (hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁)
    (V₀ : ClosedIrreducibleAnalyticSubvariety n Y₀)
    (V₁ : ClosedIrreducibleAnalyticSubvariety n Y₁)
    (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (hstrict₀ : W.carrier = strictTransform n g₀ V₀.carrier)
    (hstrict₁ : W.carrier = strictTransform n g₁ V₁.carrier) :
    ∃ z, RegularAtDim (n := n) W.carrier z W.dim ∧
      z ∉ exceptionalLocus n g₀ ∧ z ∉ exceptionalLocus n g₁ := by
  have hE₀ := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg₀
  have hE₁ := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg₁
  have hnot₀ : ¬ W.carrier ⊆ exceptionalLocus n g₀ :=
    not_subset_exceptional_of_strict V₀.carrier W.carrier W.nonempty hstrict₀
  have hnot₁ : ¬ W.carrier ⊆ exceptionalLocus n g₁ :=
    not_subset_exceptional_of_strict V₁.carrier W.carrier W.nonempty hstrict₁
  have hnot : ¬ W.carrier ⊆ exceptionalLocus n g₀ ∪ exceptionalLocus n g₁ := by
    intro hsub
    have heq : W.carrier = (W.carrier ∩ exceptionalLocus n g₀) ∪
        (W.carrier ∩ exceptionalLocus n g₁) := by
      ext z
      constructor
      · intro hz
        exact (hsub hz).elim (fun he => Or.inl ⟨hz, he⟩) (fun he => Or.inr ⟨hz, he⟩)
      · exact fun hz => hz.elim And.left And.left
    rcases W.irreducible_carrier.eq_left_or_eq_right (W.analytic.inter hE₀)
      (W.analytic.inter hE₁) inter_subset_left inter_subset_left heq with h | h
    · apply hnot₀
      intro z hz
      have hz' : z ∈ W.carrier ∩ exceptionalLocus n g₀ := h ▸ hz
      exact hz'.2
    · apply hnot₁
      intro z hz
      have hz' : z ∈ W.carrier ∩ exceptionalLocus n g₁ := h ▸ hz
      exact hz'.2
  obtain ⟨z, hz, hzE⟩ := AnalyticIrreducibleComponents.exists_mem_regularLocus_not_mem_of_not_subset
    W (ConstantRankImage.IsComplexAnalyticSubset.union hE₀ hE₁) hnot
  exact ⟨z, hz, fun he => hzE (Or.inl he), fun he => hzE (Or.inr he)⟩

end SGPT.Foundations.Analysis.Pending.CommonStrictUnramifiedPoint
