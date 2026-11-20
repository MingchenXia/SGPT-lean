import SGPT.Unibranch.ComplexSpaceBimeromorphicComponents
import SGPT.Unibranch.ComplexSpaceProperDiscCriterion

/-! ALL actual original printed FN hypotheses and whole disk tests for
original proper PSH descent. Singular ambient extension is NOT assumed/proved.
Blueprint: complex-space-proper-fn-descent.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry Metric
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- ONLY original ψ,π,hπ,hX internally manufacture every ORIGINAL source FN
hypothesis and exact whole-disk criterion for the SAME unique descended function.
This does not replace the missing singular local ambient extension theorem. -/
theorem IsPSH.exists_unique_usc_descent_with_original_FN_hypotheses
    {X Y : SourceReducedComplexSpace} {ψ : Y.obj.left → EReal} (hψ : Y.IsPSH ψ)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    ∃! φ : X.obj.left → EReal,
      (∀ x : X.obj.left,φ x ≠ ⊤) ∧
      (∀ Z : Set X.obj.left,X.IsIrreducibleComponent Z → ∃ z ∈ Z,φ z ≠ ⊥) ∧
      UpperSemicontinuous φ ∧
      (∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) ∧
      ∀ f : unitDisc ⟶ X,(∃ z ∈ ball (0 : ℂ) 1,discPullback f φ z ≠ ⊥) →
        SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1) := by
  obtain ⟨φ,⟨hφ,hcoh,hdisc⟩,hunique⟩ := hψ.exists_unique_usc_descent_with_diskCriterion π hπ hX
  have htop : ∀ x : X.obj.left,φ x ≠ ⊤ := by
    intro x
    obtain ⟨y,hy⟩ := hπ.surjective x
    rw [← hy,hcoh]
    exact hψ.ne_top y
  have hcomp := hψ.componentNondegenerate_descent_of_isProperBimeromorphic π hπ hX hcoh
  refine ⟨φ,⟨htop,hcomp,hφ,hcoh,hdisc⟩,?_⟩
  intro χ hχ
  exact hunique χ ⟨hχ.2.2.1,hχ.2.2.2.1,hχ.2.2.2.2⟩

end SGPT.Unibranch.SourceReducedComplexSpace
