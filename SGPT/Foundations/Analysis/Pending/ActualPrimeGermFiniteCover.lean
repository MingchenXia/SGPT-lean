import SGPT.Foundations.Analysis.Pending.ActualPrimeGermGenericAvoidance

set_option autoImplicit false

/-!
# An original prime zero germ selects a member of a finite analytic cover

Complete mathematical statement and ENTIRE proof precede the baseline.
The whole finite cover is input; its selected member is internally produced.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualPrimeGermFiniteCover

open FirstPass AnalyticGermDecomposition

variable {n : ℕ}

private theorem isAnalyticGerm_finset_union {ι : Type*}
    (A : ι → Set (ComplexModel n)) :
    ∀ s : Finset ι, (∀ i ∈ s, IsAnalyticGerm (A i)) →
      IsAnalyticGerm (⋃ i ∈ s, A i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] using
      (isAnalyticGerm_empty : IsAnalyticGerm (∅ : Set (ComplexModel n)))
  | insert i s hi ih =>
    intro hA
    rw [Finset.set_biUnion_insert]
    exact (hA i (Finset.mem_insert_self i s)).union
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

private theorem exists_member_of_irreducible_finset_cover {ι : Type*}
    {B : Set (ComplexModel n)} (hB : IsIrreducibleGerm B)
    (A : ι → Set (ComplexModel n)) :
    ∀ s : Finset ι, (∀ i ∈ s, IsAnalyticGerm (A i)) →
      B ≤ᶠ[𝓝 0] (⋃ i ∈ s, A i) → ∃ i ∈ s, B ≤ᶠ[𝓝 0] A i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ hcover
    have hsub : B ≤ᶠ[𝓝 0] (∅ : Set (ComplexModel n)) := by
      simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] using hcover
    exfalso
    apply hB.2.1
    exact Filter.eventuallyEq_set.mpr (hsub.mono fun x hx => ⟨hx, fun hx => hx.elim⟩)
  | insert i s hi ih =>
    intro hA hcover
    rw [Finset.set_biUnion_insert] at hcover
    have hD : IsAnalyticGerm (⋃ j ∈ s, A j) :=
      isAnalyticGerm_finset_union A s (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have heq : B =ᶠ[𝓝 0] ((B ∩ A i) ∪ (B ∩ (⋃ j ∈ s, A j)) : Set (ComplexModel n)) := by
      apply Filter.eventuallyEq_set.mpr
      filter_upwards [hcover] with x hx
      exact ⟨fun hxB => (hx hxB).elim (fun hxi => Or.inl ⟨hxB, hxi⟩)
        (fun hxD => Or.inr ⟨hxB, hxD⟩), fun hx => hx.elim And.left And.left⟩
    rcases hB.2.2 (B ∩ A i) (B ∩ (⋃ j ∈ s, A j))
      (hB.1.inter (hA i (Finset.mem_insert_self i s))) (hB.1.inter hD) heq with hleft | hright
    · refine ⟨i, Finset.mem_insert_self i s, ?_⟩
      exact (Filter.eventuallyEq_set.mp hleft).mono fun x hx hxB => (hx.mp hxB).2
    · have hsub : B ≤ᶠ[𝓝 0] (⋃ j ∈ s, A j) :=
        (Filter.eventuallyEq_set.mp hright).mono fun x hx hxB => (hx.mp hxB).2
      obtain ⟨j, hj, hBj⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)) hsub
      exact ⟨j, Finset.mem_insert_of_mem hj, hBj⟩

/-- The whole finite analytic cover selects its member internally and yields
actual defining-ideal divisibility by the original prime equation. -/
theorem exists_member_and_vanishingIdeal_le {ι : Type*} [Fintype ι]
    (q : ComplexModel n → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq))
    (A : ι → Set (ComplexModel n)) (hA : ∀ i, IsAnalyticGerm (A i))
    (hcover : {x | q x = 0} ≤ᶠ[𝓝 0] (⋃ i, A i)) :
    ∃ i, ({x | q x = 0} ≤ᶠ[𝓝 0] A i) ∧
      vanishingIdeal (A i) ≤ Ideal.span {HolGerm.mk q hq} := by
  have hB := ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ
  have hcover' : {x | q x = 0} ≤ᶠ[𝓝 0] (⋃ i ∈ (Finset.univ : Finset ι), A i) := by
    simpa only [Finset.mem_univ, iUnion_true] using hcover
  obtain ⟨i, _hi, hBi⟩ := exists_member_of_irreducible_finset_cover hB.2 A Finset.univ
    (fun i _ => hA i) hcover'
  refine ⟨i, hBi, ?_⟩
  rw [← hB.1]
  exact vanishingIdeal_anti hBi

end SGPT.Foundations.Analysis.Pending.ActualPrimeGermFiniteCover
