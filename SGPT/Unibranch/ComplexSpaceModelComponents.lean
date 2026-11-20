import SGPT.Unibranch.ComplexSpaceAnalyticSubsets
import SGPT.Foundations.Analysis.Pending.IrreducibleComponentFilling

/-! Actual original/native irreducibility and component interior for
singular embedded models. Blueprint: complex-space-model-components.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Literal irreducibility dictionary for the SAME original singular model,
not a smooth replacement or component certificate. -/
theorem isIrreducibleAnalyticSubset_model_iff {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset C}
    (A : Set C) :
    (sourceReducedComplexSpaceModel U C hC).IsIrreducibleAnalyticSubset A ↔
      IsComplexAnalyticallyIrreducible (n := n) (Subtype.val '' A : Set U) := by
  constructor
  · intro hA
    refine ⟨(isAnalyticSubset_model_iff A).mp hA.1,hA.2.1.image _,?_⟩
    intro B D hB hD hBA hDA heq
    let B' : Set C := Subtype.val ⁻¹' B
    let D' : Set C := Subtype.val ⁻¹' D
    have hB'A : B' ⊆ A := by
      intro a ha
      obtain ⟨b,hb,hab⟩ := hBA ha
      exact Subtype.val_injective hab ▸ hb
    have hD'A : D' ⊆ A := by
      intro a ha
      obtain ⟨b,hb,hab⟩ := hDA ha
      exact Subtype.val_injective hab ▸ hb
    have hcover : A = B' ∪ D' := by
      ext a
      constructor
      · intro ha
        have hv : a.val ∈ Subtype.val '' A := ⟨a,ha,rfl⟩
        rw [heq] at hv
        exact hv
      · exact fun ha => ha.elim (fun hb => hB'A hb) (fun hd => hD'A hd)
    have hIB : Subtype.val '' B' = B := by
      apply Subset.antisymm (image_preimage_subset _ _)
      intro b hb
      obtain ⟨a,_ha,rfl⟩ := hBA hb
      exact ⟨a,hb,rfl⟩
    have hID : Subtype.val '' D' = D := by
      apply Subset.antisymm (image_preimage_subset _ _)
      intro b hb
      obtain ⟨a,_ha,rfl⟩ := hDA hb
      exact ⟨a,hb,rfl⟩
    rcases hA.2.2 B' D'
      (isAnalyticSubset_model_of_isComplexAnalyticSubset hB)
      (isAnalyticSubset_model_of_isComplexAnalyticSubset hD) hB'A hD'A hcover with h | h
    · exact Or.inl ((congrArg (fun S : Set C => Subtype.val '' S) h).trans hIB)
    · exact Or.inr ((congrArg (fun S : Set C => Subtype.val '' S) h).trans hID)
  · intro hA
    refine ⟨(isAnalyticSubset_model_iff A).mpr hA.1,?_,?_⟩
    · obtain ⟨a,⟨b,hb,_hab⟩⟩ := hA.2.1
      exact ⟨b,hb⟩
    · intro B D hB hD hBA hDA heq
      have hcover : (Subtype.val '' A : Set U) = Subtype.val '' B ∪ Subtype.val '' D := by
        rw [heq,image_union]
      rcases hA.2.2 _ _ ((isAnalyticSubset_model_iff B).mp hB)
        ((isAnalyticSubset_model_iff D).mp hD) (image_mono hBA) (image_mono hDA) hcover with h | h
      · exact Or.inl (Subtype.val_injective.image_injective h)
      · exact Or.inr (Subtype.val_injective.image_injective h)

/-- Every ORIGINAL irreducible component of the singular model contains
a genuine nonempty open window in that SAME source topology. -/
theorem exists_isOpen_subset_component_model {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset C}
    {Z : Set C} (hZ : (sourceReducedComplexSpaceModel U C hC).IsIrreducibleComponent Z) :
    ∃ O : Set C,IsOpen O ∧ O.Nonempty ∧ O ⊆ Z := by
  let A : Set U := Subtype.val '' Z
  have hA := (isIrreducibleAnalyticSubset_model_iff Z).mp hZ.1
  obtain ⟨a,ha⟩ := hA.2.1
  obtain ⟨p,_hp,k,hp⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen
    hA.1 isOpen_univ ha (mem_univ a)
  let V : ClosedIrreducibleAnalyticSubvariety n U := {
    carrier := A
    isClosed_carrier := hA.1.isClosed
    irreducible_carrier := hA
    dim := k
    dim_le := hp.1
    regularLocus_nonempty := ⟨p,hp⟩ }
  have hVA : SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus.IsIrreducibleComponent V C := by
    refine ⟨?_,?_⟩
    · rintro a ⟨z,_hz,rfl⟩
      exact z.property
    · intro W hVW hWC
      let Z' : Set C := Subtype.val ⁻¹' W.carrier
      have hWimage : (Subtype.val '' Z' : Set U) = W.carrier := by
        apply Subset.antisymm (image_preimage_subset _ _)
        intro w hw
        exact ⟨⟨w,hWC hw⟩,hw,rfl⟩
      have hZ' : (sourceReducedComplexSpaceModel U C hC).IsIrreducibleAnalyticSubset Z' := by
        apply (isIrreducibleAnalyticSubset_model_iff Z').mpr
        rw [hWimage]
        exact W.irreducible_carrier
      have hZZ' : Z ⊆ Z' := fun z hz => hVW ⟨z,hz,rfl⟩
      have heq := hZ.2 Z' hZ' hZZ'
      have hI := congrArg (fun S : Set C => (Subtype.val '' S : Set U)) heq
      rw [hWimage] at hI
      exact hI
  obtain ⟨B,hB,⟨a,haV,haB⟩,hCB⟩ := IrreducibleComponentFilling.exists_isOpen_inter_subset hC hVA
  refine ⟨Subtype.val ⁻¹' B,hB.preimage continuous_subtype_val,?_,?_⟩
  · obtain ⟨z,_hz,rfl⟩ := haV
    exact ⟨z,haB⟩
  · intro z hz
    obtain ⟨w,hw,hwz⟩ := hCB ⟨z.property,hz⟩
    exact Subtype.val_injective hwz ▸ hw

/-- A dense actual finite locus internally supplies the ORIGINAL component
qualification on every singular model. -/
theorem componentNondegenerate_model_of_dense_finite {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset C}
    {φ : C → EReal} (hd : Dense {c : C | φ c ≠ ⊥}) :
    ∀ Z,(sourceReducedComplexSpaceModel U C hC).IsIrreducibleComponent Z →
      ∃ z ∈ Z,φ z ≠ ⊥ := by
  intro Z hZ
  obtain ⟨O,hO,⟨c,hcO⟩,hOZ⟩ := exists_isOpen_subset_component_model hZ
  obtain ⟨z,hzO,hzfin⟩ := mem_closure_iff.mp (hd c) _ hO hcO
  exact ⟨z,hOZ hzO,hzfin⟩

end SGPT.Unibranch.SourceReducedComplexSpace
