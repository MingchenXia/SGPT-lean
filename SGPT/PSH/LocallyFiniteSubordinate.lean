import SGPT.PSH.GeometricQDivisor

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open scoped Topology

/-- Local finiteness of the original outer family and each actual inner
family, with genuine subordination, supplies the entire dependent family. -/
theorem locallyFinite_sigma_of_subordinate {X ι : Type*} {J : ι → Type*}
    [TopologicalSpace X] (A : ι → Set X) (B : ∀ i, J i → Set X)
    (hA : LocallyFinite A) (hB : ∀ i, LocallyFinite (B i))
    (hsub : ∀ i j, B i j ⊆ A i) :
    LocallyFinite (fun t : (i : ι) × J i => B t.1 t.2) := by
  classical
  intro x
  obtain ⟨N, hN, hS⟩ := hA x
  choose O hO hT using fun i => hB i x
  let S := {i | (A i ∩ N).Nonempty}
  let T := fun i => {j | (B i j ∩ O i).Nonempty}
  have hfinite : (⋃ i ∈ S, Sigma.mk i '' T i).Finite :=
    hS.biUnion (fun i _ => (hT i).image (Sigma.mk i))
  have hON : (⋂ i ∈ S, O i) ∈ 𝓝 x := (Filter.biInter_mem hS).mpr (fun i _ => hO i)
  refine ⟨N ∩ ⋂ i ∈ S, O i, inter_mem hN hON, hfinite.subset ?_⟩
  intro t ht
  obtain ⟨z, hzB, hzN⟩ := ht
  have hi : t.1 ∈ S := ⟨z, hsub t.1 t.2 hzB, hzN.1⟩
  exact mem_iUnion₂.mpr ⟨t.1, hi, mem_image_of_mem (Sigma.mk t.1)
    ⟨z, hzB, mem_iInter₂.mp hzN.2 t.1 hi⟩⟩

end SGPT.PSH
