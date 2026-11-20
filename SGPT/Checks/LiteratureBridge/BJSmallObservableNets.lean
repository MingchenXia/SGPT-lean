import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Directed
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Internally produced SMALL observable indices for decreasing nets of
arbitrary universe. Preserve the entire actual image filter, not an assumed
smallness of the original sheaf/Picard/numerical-class objects. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.SmallObservable
open Set Filter
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {B V P : Type} [Preorder P] (q : I → B) (a : B → V → P)

/-- All fields are actual small labels/sets and ordinary membership proofs.
The original possibly large index only occurs in propositions. -/
structure Index (q : I → B) (a : B → V → P) where
  neighborhood : Set B
  mem_filter : neighborhood ∈ Filter.map q atTop
  value : B
  mem_neighborhood : value ∈ neighborhood
  mem_range : value ∈ Set.range q

instance indexPreorder : Preorder (Index q a) where
  le x y := y.neighborhood ⊆ x.neighborhood ∧ ∀ v,a y.value v ≤ a x.value v
  le_refl _ := ⟨Subset.rfl,fun _ => le_rfl⟩
  le_trans _ _ _ hxy hyz := ⟨hyz.1.trans hxy.1,fun v => (hyz.2 v).trans (hxy.2 v)⟩

instance indexNonempty : Nonempty (Index q a) := by
  let i : I := Classical.choice inferInstance
  exact ⟨⟨Set.univ,Filter.univ_mem,q i,Set.mem_univ _,⟨i,rfl⟩⟩⟩

/-- The original decreasing input and original directedness themselves
manufacture every upper bound of the actual small output index. -/
theorem indexDirected (hanti : ∀ v,Antitone fun i => a (q i) v) :
    IsDirectedOrder (Index q a) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨ix,hix⟩ := x.mem_range
  obtain ⟨iy,hiy⟩ := y.mem_range
  have hU : ∀ᶠ i in atTop,q i ∈ x.neighborhood∩y.neighborhood :=
    Filter.inter_mem x.mem_filter y.mem_filter
  obtain ⟨i₀,hi₀⟩ := eventually_atTop.mp hU
  obtain ⟨i₁,hx₁,hy₁⟩ := exists_ge_ge ix iy
  obtain ⟨i₂,h₀₂,h₁₂⟩ := exists_ge_ge i₀ i₁
  let z : Index q a := ⟨x.neighborhood∩y.neighborhood,
    Filter.inter_mem x.mem_filter y.mem_filter,q i₂,hi₀ i₂ h₀₂,⟨i₂,rfl⟩⟩
  refine ⟨z,⟨Set.inter_subset_left,?_⟩,⟨Set.inter_subset_right,?_⟩⟩
  · intro v
    change a (q i₂) v ≤ a x.value v
    rw [← hix]
    exact hanti v (hx₁.trans h₁₂)
  · intro v
    change a (q i₂) v ≤ a y.value v
    rw [← hiy]
    exact hanti v (hy₁.trans h₁₂)

omit [Nonempty I] [IsDirectedOrder I] in
theorem value_antitone (v : V) : Antitone fun j : Index q a => a j.value v :=
  fun _ _ h => h.2 v

/-- The small output label map retains the ENTIRE original image filter,
so every genuine original limit factoring through labels is preserved. -/
theorem value_tendsto (hanti : ∀ v,Antitone fun i => a (q i) v) :
    Tendsto (Index.value (q := q) (a := a)) atTop (Filter.map q atTop) := by
  have : IsDirectedOrder (Index q a) := indexDirected q a hanti
  apply tendsto_def.mpr
  intro U hU
  have hU' : ∀ᶠ i in atTop,q i ∈ U := hU
  obtain ⟨i₀,hi₀⟩ := eventually_atTop.mp hU'
  let j₀ : Index q a := ⟨U,hU,q i₀,hi₀ i₀ le_rfl,⟨i₀,rfl⟩⟩
  exact eventually_atTop.mpr ⟨j₀,fun j hj => hj.1 j.mem_neighborhood⟩

/-- A genuine original preimage, internally selected from actual range
membership; no monotonicity/cofinality of preimages is falsely asserted. -/
def sourceIndex (j : Index q a) : I := Classical.choose j.mem_range

omit [Nonempty I] [IsDirectedOrder I] [Preorder P] in
theorem sourceIndex_spec (j : Index q a) : q (sourceIndex q a j)=j.value :=
  Classical.choose_spec j.mem_range

end SGPT.NAPotential.BJ.SmallObservable
