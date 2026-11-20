import SGPT.Unibranch.ComplexSpaceModelComponents
import SGPT.Unibranch.ComplexSpaceBimeromorphicComponents
import SGPT.Unibranch.ComplexSpaceThetaPSH
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-!
# Irreducible components through points of embedded models; poles of `θ`-psh functions

Two auxiliary facts for the component clause of `def:unibranch:L105` in `cor:PSH`.

* `exists_isIrreducibleComponent_model_mem`: every point `c` of an embedded model `(U, C)` lies on
  an irreducible component of the model (in the sense of `ComplexSpaceAnalyticSubsets`). If `c` is
  an accumulation point of `C` this is the positive-dimensional component of
  `AnalyticIrreducibleComponents.exists_isIrreducibleComponent_pos_dim_of_accPt`, transported to
  complex-space components (maximality via `isIrreducibleAnalyticSubset_model_iff`); if `c` is
  isolated, `{c}` is a clopen irreducible analytic subset, hence a component.
* `IsThetaPSH.exists_ne_bot_of_isClopen`: a `θ`-psh function (`def:unibranch:L105`, second part) on
  an arbitrary complex space is not identically `-∞` on a nonempty clopen subset. Indeed in the
  local model at a point of the clopen set, an irreducible component through that point is
  irreducible, hence contained in the (clopen) trace of the set, and the component clause of
  `PSH(V)` applies.

Lane PD2, blueprint `pd2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

namespace SGPT.Unibranch.PD2

open SourceReducedComplexSpace

noncomputable section

/-- Every point of an embedded model `(U, C)` lies on an irreducible component of the model. -/
theorem exists_isIrreducibleComponent_model_mem {n : ℕ} {U : Opens (ComplexModel n)}
    {C : Set U} {hC : IsComplexAnalyticSubset (n := n) C} (c : C) :
    ∃ Z : Set C, (sourceReducedComplexSpaceModel U C hC).IsIrreducibleComponent Z ∧ c ∈ Z := by
  by_cases hacc : AccPt (c : U) (𝓟 C)
  · obtain ⟨V, hVC, -, hcV⟩ :=
      AnalyticIrreducibleComponents.exists_isIrreducibleComponent_pos_dim_of_accPt hC
        c.property hacc
    let Z : Set C := Subtype.val ⁻¹' V.carrier
    have hZimg : (Subtype.val '' Z : Set U) = V.carrier := by
      apply Subset.antisymm (image_preimage_subset _ _)
      intro a ha
      exact ⟨⟨a, hVC.1 ha⟩, ha, rfl⟩
    have hZirr : (sourceReducedComplexSpaceModel U C hC).IsIrreducibleAnalyticSubset Z := by
      rw [isIrreducibleAnalyticSubset_model_iff, hZimg]
      exact V.irreducible_carrier
    refine ⟨Z, ⟨hZirr, fun B hB hZB => ?_⟩, hcV⟩
    have hB' := (isIrreducibleAnalyticSubset_model_iff B).mp hB
    obtain ⟨a, ha⟩ := hB'.2.1
    obtain ⟨p, -, k, hp⟩ :=
      RegularLocusDense.exists_regularAtDim_mem_of_isOpen hB'.1 isOpen_univ ha (mem_univ a)
    let W : ClosedIrreducibleAnalyticSubvariety n U := {
      carrier := Subtype.val '' B
      isClosed_carrier := hB'.1.isClosed
      irreducible_carrier := hB'
      dim := k
      dim_le := hp.1
      regularLocus_nonempty := ⟨p, hp⟩ }
    have hVW : V.carrier ⊆ W.carrier := by
      rw [← hZimg]
      exact image_mono hZB
    have hWC : W.carrier ⊆ C := by
      rintro _ ⟨b, -, rfl⟩
      exact b.property
    have heq : W.carrier = V.carrier := hVC.2 W hVW hWC
    apply Subtype.val_injective.image_injective
    change W.carrier = _
    rw [heq, hZimg]
  · have hopen : IsOpen ({c} : Set C) := by
      rw [isOpen_iff_mem_nhds]
      intro c' hc'
      rw [mem_singleton_iff] at hc'
      subst hc'
      rw [accPt_iff_nhds] at hacc
      push Not at hacc
      obtain ⟨N, hN, hNC⟩ := hacc
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hN] with d hd
      exact Subtype.val_injective (hNC d.val ⟨hd, d.property⟩)
    have hclopen : IsClopen ({c} : Set C) := ⟨isClosed_singleton, hopen⟩
    refine ⟨{c}, isIrreducibleComponent_of_clopen_irreducible hclopen
      ⟨OriginalAnalyticClopen.isAnalyticSubset hclopen, singleton_nonempty c, ?_⟩, rfl⟩
    intro B D _ _ hBc hDc hBD
    have hc : c ∈ B ∪ D := by
      rw [← hBD]
      exact mem_singleton c
    rcases hc with h | h
    · exact Or.inl (Subset.antisymm (singleton_subset_iff.mpr h) hBc)
    · exact Or.inr (Subset.antisymm (singleton_subset_iff.mpr h) hDc)

/-- An irreducible component which meets a clopen subset is contained in it. -/
theorem IsIrreducibleComponent.subset_of_isClopen {X : SourceReducedComplexSpace}
    {Z A : Set X.obj.left} (hZ : X.IsIrreducibleComponent Z) (hA : IsClopen A) {z : X.obj.left}
    (hzZ : z ∈ Z) (hzA : z ∈ A) : Z ⊆ A := by
  have h1 := OriginalAnalyticClopen.isAnalyticSubset_inter hZ.1.1 hA
  have h2 := OriginalAnalyticClopen.isAnalyticSubset_inter hZ.1.1 hA.compl
  have hUnion : Z = Z ∩ A ∪ Z ∩ Aᶜ := by
    rw [← inter_union_distrib_left, union_compl_self, inter_univ]
  rcases hZ.1.2.2 _ _ h1 h2 inter_subset_left inter_subset_left hUnion with h | h
  · rw [h]
    exact inter_subset_right
  · exfalso
    have hz := hzZ
    rw [h] at hz
    exact hz.2 hzA

/-- **Poles of `θ`-psh functions.** On an arbitrary complex space, a `θ`-psh function is not
identically `-∞` on any nonempty clopen subset. -/
theorem IsThetaPSH.exists_ne_bot_of_isClopen {Y : SourceReducedComplexSpace}
    {θ : SpaceForm Y 2} {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH θ u)
    {A : Set Y.obj.left} (hA : IsClopen A) (hne : A.Nonempty) : ∃ y ∈ A, u y ≠ ⊥ := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨e, ⟨c, rfl⟩, -, g, -, -, hpsh⟩ := hu y
  let A' : Set e.carrier := e.toPoint ⁻¹' A
  have hA' : IsClopen A' := hA.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨Z, hZ, hcZ⟩ := exists_isIrreducibleComponent_model_mem (hC := e.analytic) c
  have hZA : Z ⊆ A' := IsIrreducibleComponent.subset_of_isClopen hZ hA' hcZ hy
  obtain ⟨z, hzZ, hz⟩ := hpsh.1 Z hZ
  refine ⟨e.toPoint z, hZA hzZ, fun hbot => hz ?_⟩
  change (g z.val.val : EReal) + u (e.toPoint z) = ⊥
  rw [hbot]
  exact EReal.add_bot _

end

end SGPT.Unibranch.PD2
