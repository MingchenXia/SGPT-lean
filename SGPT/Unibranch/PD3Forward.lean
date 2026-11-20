import SGPT.Unibranch.ComplexSpaceBimeromorphicComponents
import SGPT.Unibranch.ComplexSpaceBimeromorphicDense

/-!
# Pull-back of psh functions by proper bimeromorphic maps onto unibranch spaces

Source `cor:PSH` (Appendix B, `appendix_unibranch.tex`), case `θ = 0`, the forward map
`π^* : PSH(X) → PSH(Y)`: for a proper bimeromorphic morphism `π : Y → X` onto a unibranch complex
space `X` and `v ∈ PSH(X)`, the pull-back `v ∘ π` is plurisubharmonic on `Y` in the sense of
`def:unibranch:L105`, including the **global** condition 1 (`v ∘ π` is not identically `-∞` on any
irreducible component of the possibly singular `Y`).

Condition 2 (local ambient representatives) is the existing
`IsPSH.locallyAmbient_pullback_of_isProperBimeromorphic`. For condition 1 we show that every
irreducible component of `Y` is the preimage `π⁻¹(K)` of a connected component `K` of `X`
(`IsProperBimeromorphic.eq_preimage_connectedComponent_of_isIrreducibleComponent`): the sets
`π⁻¹(K)` are clopen irreducible components of `Y` (existing,
`isIrreducibleComponent_preimage_connectedComponent`), an irreducible analytic set meeting a clopen
set lies in it, and components are maximal. In particular every irreducible component of `Y` is
open and nonempty (`IsProperBimeromorphic.isOpen_of_isIrreducibleComponent`). Since `K` is an
irreducible component of the unibranch `X`, `v` is not identically `-∞` on `K`, and `π` is onto.

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.PD3

open SourceReducedComplexSpace

/-- An irreducible analytic subset meeting a clopen set is contained in it. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsIrreducibleAnalyticSubset.subset_of_isClopen {Y : SourceReducedComplexSpace}
    {A W : Set Y.obj.left} (hA : Y.IsIrreducibleAnalyticSubset A) (hW : IsClopen W)
    (hmeet : (A ∩ W).Nonempty) : A ⊆ W := by
  have h1 := OriginalAnalyticClopen.isAnalyticSubset_inter hA.1 hW
  have h2 := OriginalAnalyticClopen.isAnalyticSubset_inter hA.1 hW.compl
  have hunion : A = A ∩ W ∪ A ∩ Wᶜ := by
    rw [← inter_union_distrib_left, union_compl_self, inter_univ]
  rcases hA.2.2 _ _ h1 h2 inter_subset_left inter_subset_left hunion with h | h
  · rw [h]
    exact inter_subset_right
  · exfalso
    obtain ⟨y, hyA, hyW⟩ := hmeet
    rw [h] at hyA
    exact hyA.2 hyW

/-- **Irreducible components of the source of a proper bimeromorphic map onto a unibranch space.**
Every irreducible component of `Y` is the preimage of the connected component (= irreducible
component) of `X` containing the image of any of its points. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsProperBimeromorphic.eq_preimage_connectedComponent_of_isIrreducibleComponent
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) {Z : Set Y.obj.left} (hZ : Y.IsIrreducibleComponent Z)
    {y : Y.obj.left} (hy : y ∈ Z) :
    Z = π.hom.left.base ⁻¹' connectedComponent (π.hom.left.base y) := by
  let _ := hX.locallyConnectedSpace
  let K : Set X.obj.left := connectedComponent (π.hom.left.base y)
  have hK : IsClopen K := ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  set A : Set Y.obj.left := π.hom.left.base ⁻¹' K
  have hA : Y.IsIrreducibleComponent A :=
    hπ.isIrreducibleComponent_preimage_connectedComponent hX (π.hom.left.base y)
  have hAc : IsClopen A :=
    ⟨hK.isClosed.preimage π.hom.left.base.hom.continuous,
      hK.isOpen.preimage π.hom.left.base.hom.continuous⟩
  have hZA : Z ⊆ A := IsIrreducibleAnalyticSubset.subset_of_isClopen hZ.1 hAc
    ⟨y, hy, mem_connectedComponent⟩
  exact (hZ.2 A hA.1 hZA).symm

/-- Every irreducible component of the source of a proper bimeromorphic map onto a unibranch
space is open (and nonempty), so in particular it has nonempty interior. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsProperBimeromorphic.isOpen_of_isIrreducibleComponent
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) {Z : Set Y.obj.left} (hZ : Y.IsIrreducibleComponent Z) :
    IsOpen Z := by
  let _ := hX.locallyConnectedSpace
  obtain ⟨y, hy⟩ := hZ.1.2.1
  let K : Set X.obj.left := connectedComponent (π.hom.left.base y)
  have hK : IsOpen K := isOpen_connectedComponent
  rw [hπ.eq_preimage_connectedComponent_of_isIrreducibleComponent hX hZ hy]
  exact hK.preimage π.hom.left.base.hom.continuous

/-- Every irreducible component of the source of a proper bimeromorphic map onto a unibranch
space has nonempty interior. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsProperBimeromorphic.interior_nonempty_of_isIrreducibleComponent
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) {Z : Set Y.obj.left} (hZ : Y.IsIrreducibleComponent Z) :
    (interior Z).Nonempty := by
  rw [(hπ.isOpen_of_isIrreducibleComponent hX hZ).interior_eq]
  exact hZ.1.2.1

/-- **Global component clause of the pull-back.** For `π : Y → X` proper bimeromorphic onto a
unibranch space and `v ∈ PSH(X)`, the pull-back `v ∘ π` is not identically `-∞` on any irreducible
component of `Y` (condition 1 of `def:unibranch:L105` on `Y`). -/
theorem componentNondegenerate_comp {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) {v : X.obj.left → EReal}
    (hv : X.IsPSH v) :
    ∀ Z : Set Y.obj.left, Y.IsIrreducibleComponent Z → ∃ z ∈ Z, v (π.hom.left.base z) ≠ ⊥ := by
  intro Z hZ
  obtain ⟨y, hy⟩ := hZ.1.2.1
  have hZeq := hπ.eq_preimage_connectedComponent_of_isIrreducibleComponent hX hZ hy
  obtain ⟨x, hxK, hx⟩ := hv.1 _ (hX.isIrreducibleComponent_connectedComponent (π.hom.left.base y))
  obtain ⟨z, rfl⟩ := hπ.surjective x
  refine ⟨z, ?_, hx⟩
  rw [hZeq]
  exact hxK

/-- **Source `cor:PSH`, `θ = 0`, the forward map.** For a proper bimeromorphic morphism
`π : Y → X` onto a unibranch complex space and `v ∈ PSH(X)`, the pull-back `π^*v = v ∘ π` is in
`PSH(Y)` (`def:unibranch:L105`, both conditions, on the possibly singular `Y`). -/
theorem isPSH_comp_of_isProperBimeromorphic {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) {v : X.obj.left → EReal}
    (hv : X.IsPSH v) : Y.IsPSH (fun y => v (π.hom.left.base y)) :=
  ⟨componentNondegenerate_comp π hπ hX hv,
    hv.locallyAmbient_pullback_of_isProperBimeromorphic hX hπ⟩

/-- Injectivity of `v ↦ v ∘ π` (surjectivity of `π`). -/
theorem pullback_injective {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) {v w : X.obj.left → EReal}
    (h : (fun y => v (π.hom.left.base y)) = fun y => w (π.hom.left.base y)) : v = w := by
  funext x
  obtain ⟨y, rfl⟩ := hπ.surjective x
  exact congrFun h y

end SGPT.Unibranch.PD3
