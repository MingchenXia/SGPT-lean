import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Genuine finite closed-image weight sums from matching actual local
basis tests; no measure/Euler/degree definition is changed. Blueprint:
original-finite-closed-point-sums.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open TopologicalSpace
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite point weights genuinely group over their actual image support. -/
theorem originalFiniteWeightSum_group_by_image
    {A X : Type*} [Fintype A] [DecidableEq X]
    (a : A → X) (w : A → ℕ) (F : Finset X) (hF : ∀ z, a z ∈ F) :
    (∑ z, w z) = ∑ x ∈ F, ∑ z, if a z=x then w z else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (a z)]
  · simp
  · intro x _ hxa
    exact if_neg (fun h => hxa h.symm)
  · intro hn
    exact (hn (hF z)).elim

/-- A genuine original neighborhood basis and matching local weighted
point sums determine the FULL finite sums, even in a non-T1 ambient space.
Only the ACTUAL finite image points are closed. -/
theorem originalFiniteClosedPointSums_eq_of_basis
    {A B X : Type*} [Fintype A] [Fintype B] [TopologicalSpace X]
    (a : A → X) (b : B → X) (w : A → ℕ) (v : B → ℕ)
    (ha : ∀ z, IsClosed ({a z}:Set X)) (hb : ∀ z, IsClosed ({b z}:Set X))
    (Basis : Set (Opens X))
    (hBasis : ∀ x (O : Opens X), x∈O → ∃ U∈Basis, x∈U ∧ U≤O)
    (hlocal : ∀ U∈Basis,
      (∑ z, if a z∈U then w z else 0) = ∑ z, if b z∈U then v z else 0) :
    (∑ z, w z) = ∑ z, v z := by
  classical
  let F : Finset X := Finset.univ.image a ∪ Finset.univ.image b
  have hFa (z : A) : a z∈F := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩)
  have hFb (z : B) : b z∈F := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩)
  have hclosed (x : X) (hx : x∈F) : IsClosed ({x}:Set X) := by
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha z
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
      exact hb z
  have hatom (x : X) (hx : x∈F) :
      (∑ z, if a z=x then w z else 0) = ∑ z, if b z=x then v z else 0 := by
    let C : Set X := ⋃ y∈F.erase x, ({y}:Set X)
    have hC : IsClosed C := isClosed_biUnion_finset fun y hy => hclosed y (Finset.mem_of_mem_erase hy)
    let O : Opens X := ⟨Cᶜ,hC.isOpen_compl⟩
    have hxO : x∈O := by
      change x∉C
      simp only [C,Set.mem_iUnion,Set.mem_singleton_iff]
      rintro ⟨y,hy,hxy⟩
      have hye : y≠x := (Finset.mem_erase.mp hy).1
      exact hye (show x=y from hxy).symm
    obtain ⟨U,hUB,hxU,hUO⟩ := hBasis x O hxO
    have haU (z : A) : a z∈U ↔ a z=x := by
      constructor
      · intro hz
        by_contra hne
        apply hUO hz
        simp only [C,Set.mem_iUnion,Set.mem_singleton_iff]
        exact ⟨a z,Finset.mem_erase.mpr ⟨hne,hFa z⟩,rfl⟩
      · intro he; rw [he]; exact hxU
    have hbU (z : B) : b z∈U ↔ b z=x := by
      constructor
      · intro hz
        by_contra hne
        apply hUO hz
        simp only [C,Set.mem_iUnion,Set.mem_singleton_iff]
        exact ⟨b z,Finset.mem_erase.mpr ⟨hne,hFb z⟩,rfl⟩
      · intro he; rw [he]; exact hxU
    simpa only [haU,hbU] using hlocal U hUB
  rw [originalFiniteWeightSum_group_by_image a w F hFa,
    originalFiniteWeightSum_group_by_image b v F hFb]
  exact Finset.sum_congr rfl fun x hx => hatom x hx

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
