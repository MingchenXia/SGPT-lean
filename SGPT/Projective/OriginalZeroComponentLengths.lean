import SGPT.Projective.SmoothSchemeClopenComponents
import SGPT.Projective.AlgebraicSectionZeroStalk

/-! Actual original zero scheme point partition and FULL local-ring length
sum over ALL genuine original smooth projective components.
Blueprint: original-zero-component-lengths.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open scoped BigOperators
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))

/-- The SAME original whole zero scheme's inverse-image component OPEN, without replacements. -/
def originalZeroComponentOpen (C : ↥(irreducibleComponents X)) :
    (sectionZeroSubscheme a s).Opens :=
  (sectionZeroι a s) ⁻¹ᵁ smoothProjectiveComponentOpen f n E C.val C.property

/-- The literal original dependent union of component-zero points maps bijectively
onto the ENTIRE same original zero scheme, no point or component discarded. -/
def originalZeroComponentPointEquiv :
    (Σ C : ↥(irreducibleComponents X), originalZeroComponentOpen f n E a s C) ≃
      sectionZeroSubscheme a s :=
  Equiv.ofBijective (fun p => p.2.val) (by
    constructor
    · rintro ⟨C, z⟩ ⟨D, w⟩ hzw
      change z.val = w.val at hzw
      have hC : sectionZeroι a s z.val ∈ C.val := z.property
      have hD : sectionZeroι a s z.val ∈ D.val := by
        have hw : sectionZeroι a s w.val ∈ D.val := w.property
        exact Eq.mp (congrArg (fun t : sectionZeroSubscheme a s => sectionZeroι a s t ∈ D.val) hzw.symm) hw
      have hCD : C = D := by
        apply Subtype.ext
        by_contra hne
        exact Set.disjoint_left.mp (smoothScheme_components_pairwiseDisjoint f n C.property D.property hne) hC hD
      cases hCD
      have hzw' : z = w := Subtype.ext hzw
      cases hzw'
      rfl
    · intro z
      obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f n E (sectionZeroι a s z)
      exact ⟨⟨C, ⟨z, hC⟩⟩, rfl⟩)

/-- FULL original local-ring length is preserved by ACTUAL SAME component-zero open inclusion. -/
theorem originalZeroComponentStalk_length (C : ↥(irreducibleComponents X))
    (z : originalZeroComponentOpen f n E a s C) :
    Module.length ((originalZeroComponentOpen f n E a s C).toScheme.presheaf.stalk z)
      ((originalZeroComponentOpen f n E a s C).toScheme.presheaf.stalk z) =
    Module.length ((sectionZeroSubscheme a s).presheaf.stalk z.val)
      ((sectionZeroSubscheme a s).presheaf.stalk z.val) := by
  let e := (asIso ((originalZeroComponentOpen f n E a s C).ι.stalkMap z)).commRingCatIsoToRingEquiv
  have h := SGPT.NAPotential.GraphDivisorOrderTransport.ord_ringEquiv e 0
  simpa only [map_zero, Ring.ord_zero, Scheme.Opens.ι_apply] using h

private theorem originalZeroComponentOpen_finite [Finite (sectionZeroSubscheme a s)]
    (C : ↥(irreducibleComponents X)) : Finite (originalZeroComponentOpen f n E a s C) := by
  exact Finite.of_injective (fun z : originalZeroComponentOpen f n E a s C => z.val) Subtype.val_injective

/-- ACTUAL entire full original zero-stalk length sum splits over ALL original components. -/
theorem originalZero_fullLength_sum_components
    [IsArtinianScheme (sectionZeroSubscheme a s)] :
    let : Finite ↥(irreducibleComponents X) := smoothProjective_componentIndex_finite f E
    let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
    let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
    letI (C : ↥(irreducibleComponents X)) : Finite (originalZeroComponentOpen f n E a s C) :=
      originalZeroComponentOpen_finite f n E a s C
    letI (C : ↥(irreducibleComponents X)) : Fintype (originalZeroComponentOpen f n E a s C) :=
      Fintype.ofFinite _
    (∑ z : sectionZeroSubscheme a s, Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
      ((sectionZeroSubscheme a s).presheaf.stalk z)) =
      ∑ C : ↥(irreducibleComponents X), ∑ z : originalZeroComponentOpen f n E a s C,
        Module.length ((originalZeroComponentOpen f n E a s C).toScheme.presheaf.stalk z)
          ((originalZeroComponentOpen f n E a s C).toScheme.presheaf.stalk z) := by
  classical
  let : Finite ↥(irreducibleComponents X) := smoothProjective_componentIndex_finite f E
  let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
  let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
  let (C : ↥(irreducibleComponents X)) : Finite (originalZeroComponentOpen f n E a s C) := originalZeroComponentOpen_finite f n E a s C
  let (C : ↥(irreducibleComponents X)) : Fintype (originalZeroComponentOpen f n E a s C) := Fintype.ofFinite _
  dsimp only
  let len (z : sectionZeroSubscheme a s) := Module.length
    ((sectionZeroSubscheme a s).presheaf.stalk z) ((sectionZeroSubscheme a s).presheaf.stalk z)
  calc
    _ = ∑ p : (Σ C : ↥(irreducibleComponents X), originalZeroComponentOpen f n E a s C),
        len (originalZeroComponentPointEquiv f n E a s p) :=
      ((originalZeroComponentPointEquiv f n E a s).sum_comp len).symm
    _ = ∑ C : ↥(irreducibleComponents X), ∑ z : originalZeroComponentOpen f n E a s C,
        len z.val := by rw [Fintype.sum_sigma]; rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro z _
      exact (originalZeroComponentStalk_length f n E a s C z).symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
