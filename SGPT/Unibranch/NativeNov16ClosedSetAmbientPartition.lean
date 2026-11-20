import SGPT.Foundations.Analysis.Pending.RegularLocusCutoffPartitionReduction

/-! Actual finite ambient cutoff data from an arbitrary RELATIVE open cover.
The EXISTING compact cutoff producer/type is reused, not reimplemented.
Blueprint FIRST: native-nov16-closed-set-ambient-partition.tex.
-/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.RegularLocusCutoffPartitionReduction
namespace SGPT.Unibranch.NativeNov16ClosedSetAmbientPartition

theorem exists_ambient_partition {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    (C : Set M) (hC : IsClosed C) {ι : Type}
    (S : ι → Opens C) (hcover : ∀ c : C, ∃ i, c ∈ S i) :
    ∃ (r : ℕ) (idx : Fin r → ι) (U : Fin r → Opens M),
      (∀ j, (Subtype.val : C → M) ⁻¹' (U j : Set M) = (S (idx j) : Set C)) ∧
      Nonempty (CompactCutoffPartition (n := n) C U) := by
  classical
  choose V hV hPre using fun i => isOpen_induced_iff.mp (S i).isOpen
  have hAmbientCover : C ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover ⟨x,hx⟩
    refine mem_iUnion.mpr ⟨i,?_⟩
    have H : (⟨x,hx⟩ : C) ∈ (Subtype.val : C → M) ⁻¹' V i := by
      rw [hPre i]
      exact hi
    exact H
  obtain ⟨s,hs⟩ := hC.isCompact.elim_finite_subcover V hV hAmbientCover
  let idx : Fin s.card → ι := fun j => (s.equivFin.symm j).val
  let U : Fin s.card → Opens M := fun j => ⟨V (idx j),hV (idx j)⟩
  have hFiniteCover : C ⊆ ⋃ j, (U j : Set M) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨s.equivFin ⟨i,hi⟩,?_⟩
    change x ∈ V (idx (s.equivFin ⟨i,hi⟩))
    simpa only [idx,Equiv.symm_apply_apply] using hxi
  refine ⟨s.card,idx,U,?_,exists_compactCutoffPartition C hC U hFiniteCover⟩
  intro j
  exact hPre (idx j)

end SGPT.Unibranch.NativeNov16ClosedSetAmbientPartition
