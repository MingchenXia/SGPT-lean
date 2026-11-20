import SGPT.Foundations.Analysis.Pending.GlobalComponents
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

/-! # Finite genuine global analytic components on the compact manifold

The actual locally finite global-component family supplies a finite exact
enumeration by compactness. Divisor and Siu-current assembly are separate.
-/

noncomputable section
open Set
namespace SGPT.Foundations.Analysis.Pending.ActualCompactAnalyticGlobalComponents
open FirstPass GlobalComponents RegularLocusComponent

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual compact manifold internally supplies a finite exact enumeration
of all its analytic subset's genuine global irreducible components. -/
theorem exists_finite_exact_global_components {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    ∃ (N : ℕ) (B : Fin N → Set M),
      Function.Injective B ∧ range B = globalComponents (n := n) A ∧
      (∀ j, IsComplexAnalyticallyIrreducible (n := n) (B j) ∧
        B j ⊆ A ∧ (B j).Nonempty) ∧ (⋃ j, B j) = A := by
  classical
  let C := globalComponents (n := n) A
  have hne : ∀ S : C, (S : Set M).Nonempty := by
    rintro ⟨S, ⟨c, ⟨k, hk⟩, rfl⟩⟩
    exact ⟨c, subset_closure (mem_component_self hk)⟩
  let : Fintype C := (locallyFinite_globalComponents hA).fintypeOfCompact hne
  let N := Fintype.card C
  let E : Fin N ≃ C := (Fintype.equivFin C).symm
  let B : Fin N → Set M := fun j => (E j).val
  have hrange : range B = globalComponents (n := n) A := by
    ext S
    constructor
    · rintro ⟨j, rfl⟩
      exact (E j).property
    · intro hS
      refine ⟨E.symm ⟨S, hS⟩, ?_⟩
      exact congrArg Subtype.val (E.apply_symm_apply ⟨S, hS⟩)
  refine ⟨N, B, Subtype.val_injective.comp E.injective, hrange, ?_, ?_⟩
  · intro j
    exact ⟨isComplexAnalyticallyIrreducible_of_mem_globalComponents hA (E j).property,
      subset_of_mem_globalComponents hA (E j).property, hne (E j)⟩
  · rw [← sUnion_globalComponents hA, ← hrange, sUnion_range]

end SGPT.Foundations.Analysis.Pending.ActualCompactAnalyticGlobalComponents
