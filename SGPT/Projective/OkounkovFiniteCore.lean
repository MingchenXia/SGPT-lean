import SGPT.AlmostSemigroup.BodyGeometry
import Mathlib.Algebra.BigOperators.Pi

/-! Fixed ACTUAL positive source finite core, before ambient boundedness.
Blueprint: okounkov-finite-core.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set Filter MeasureTheory SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.BodyGeometry
open scoped BigOperators Pointwise Topology

/-- Actual closure membership manufactures a finite subset of the SAME original generators. -/
theorem exists_finite_closure_witness {A : Type*} [AddCommGroup A] (S : Set A)
    {x : A} (hx : x ∈ AddSubgroup.closure S) :
    ∃ t : Finset A, (t : Set A) ⊆ S ∧ x ∈ AddSubgroup.closure (t : Set A) := by
  classical
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨{x}, by simpa using hx, AddSubgroup.subset_closure (Finset.mem_singleton_self x)⟩
  | zero => exact ⟨∅, by simp, AddSubgroup.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨t,ht,hxt⟩ := ihx
    obtain ⟨u,hu,hyu⟩ := ihy
    refine ⟨t∪u, ?_, AddSubgroup.add_mem _
      (AddSubgroup.closure_mono (show (t:Set A) ⊆ (↑(t∪u):Set A) from fun _ h => Finset.mem_union_left u h) hxt)
      (AddSubgroup.closure_mono (show (u:Set A) ⊆ (↑(t∪u):Set A) from fun _ h => Finset.mem_union_right t h) hyu)⟩
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact ht h
    · exact hu h
  | neg x hx ih =>
    obtain ⟨t,ht,hxt⟩ := ih
    exact ⟨t,ht,AddSubgroup.neg_mem _ hxt⟩

/-- SAME original full lattice has one internally manufactured finite original core. -/
theorem exists_finite_fullGroup_core {n : ℕ} (S : Set ((Fin n → ℤ) × ℤ))
    (hG : AddSubgroup.closure S = ⊤) :
    ∃ t : Finset ((Fin n → ℤ) × ℤ), (↑t : Set ((Fin n → ℤ) × ℤ)) ⊆ S ∧ AddSubgroup.closure (↑t : Set ((Fin n → ℤ) × ℤ)) = ⊤ := by
  classical
  have hh (i : Option (Fin n)) : ∃ t : Finset ((Fin n → ℤ) × ℤ), (↑t : Set ((Fin n → ℤ) × ℤ)) ⊆ S ∧
      degreeOneSimplex n i ∈ AddSubgroup.closure (↑t : Set ((Fin n → ℤ) × ℤ)) :=
    exists_finite_closure_witness S (by rw [hG]; trivial)
  choose t ht hmem using hh
  let R := Finset.univ.biUnion t
  have hR : (R : Set ((Fin n → ℤ) × ℤ)) ⊆ S := by
    intro z hz
    obtain ⟨i,-,hz⟩ := Finset.mem_biUnion.mp hz
    exact ht i hz
  let H := AddSubgroup.closure (R : Set ((Fin n → ℤ) × ℤ))
  have hi (i : Option (Fin n)) : degreeOneSimplex n i ∈ H :=
    AddSubgroup.closure_mono (show (t i : Set ((Fin n → ℤ) × ℤ)) ⊆ (R : Set _) from
      fun _ h => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,h⟩) (hmem i)
  have h01 : ((0 : Fin n → ℤ),(1:ℤ)) ∈ H := hi none
  have he (i : Fin n) : (Pi.single i (1:ℤ),(0:ℤ)) ∈ H := by
    convert H.sub_mem (hi (some i)) h01 using 1
    ext <;> simp [degreeOneSimplex]
  have hhorizontal (z : Fin n → ℤ) : (z,(0:ℤ)) ∈ H := by
    have hsum : (∑ i : Fin n, (z i) • (Pi.single i (1:ℤ),(0:ℤ))) ∈ H :=
      H.sum_mem (fun i _ => H.zsmul_mem (he i) (z i))
    convert hsum using 1
    apply Prod.ext
    · funext j
      simp [Prod.fst_sum,Finset.sum_apply,Pi.single_apply]
    · simp [Prod.snd_sum]
  refine ⟨R,hR,eq_top_iff.mpr ?_⟩
  rintro ⟨z,k⟩ _
  have h := H.add_mem (hhorizontal z) (H.zsmul_mem h01 k)
  simpa using h

/-- A fixed finite full-group core consists of ACTUAL original positive source elements. -/
theorem exists_positive_finite_fullGroup_core {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    ∃ t : Finset ((Fin n → ℤ) × ℤ), (↑t : Set ((Fin n → ℤ) × ℤ)) ⊆ positiveSource S ∧
      AddSubgroup.closure (↑t : Set ((Fin n → ℤ) × ℤ)) = ⊤ := by
  have hle : LatticeSlices.generatedGroup S ≤ AddSubgroup.closure (positiveSource S) := by
    apply (AddSubgroup.closure_le _).mpr
    intro z hz
    rcases hpositive z hz with hzero | hpos
    · rw [hzero]; exact AddSubgroup.zero_mem _
    · exact AddSubgroup.subset_closure ⟨hz,hpos⟩
  have hp : AddSubgroup.closure (positiveSource S) = ⊤ := by
    apply top_unique
    rw [← hG]
    exact hle
  exact exists_finite_fullGroup_core (positiveSource S) hp

/-- Actual semigroup generation retains EXACTLY the subgroup of its SAME original generators. -/
theorem generatedGroup_addSubsemigroup_closure {n : ℕ} (R : Set ((Fin n → ℤ) × ℤ)) :
    LatticeSlices.generatedGroup (AddSubsemigroup.closure R) = AddSubgroup.closure R := by
  change AddSubgroup.closure (AddSubsemigroup.closure R : Set ((Fin n → ℤ) × ℤ)) = AddSubgroup.closure R
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    change AddSubsemigroup.closure R ≤ (AddSubgroup.closure R).toAddSubsemigroup
    exact AddSubsemigroup.closure_le.mpr (fun _ h => AddSubgroup.subset_closure h)
  · exact AddSubgroup.closure_mono AddSubsemigroup.subset_closure

end SGPT.Okounkov.BodyFromGrowth
