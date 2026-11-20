import SGPT.Projective.OriginalNormalizationAffineReadback
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! ACTUAL global original normalization is finite/surjective/proper,
from SAME original affine algebra and actual generic point; no smoothness.
Blueprint: original-normalization-finite-map.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

variable (X : Scheme.{0}) [IsIntegral X]

/-- Actual TRUE original generic point image is dense in SAME original scheme. -/
instance originalGenericPointMap_dominant : IsDominant (originalGenericPointMap X) := by
  constructor
  intro x
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (originalGenericPointMap X) := by
    apply Set.singleton_subset_iff.mpr
    exact ⟨closedPoint X.functionField, originalGenericPointMap_apply X _⟩
  apply closure_mono hsub
  rw [genericPoint_spec X]
  trivial

/-- Actual normalization map is dominant via the literal generic factorization. -/
instance originalNormalizationMap_dominant : IsDominant (originalNormalizationMap X) := by
  have hcomp : IsDominant ((originalGenericPointMap X).toNormalization ≫ originalNormalizationMap X) := by
    change IsDominant ((originalGenericPointMap X).toNormalization ≫ (originalGenericPointMap X).fromNormalization)
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact @IsDominant.of_comp _ _ _ (originalGenericPointMap X).toNormalization (originalNormalizationMap X) hcomp

/-- The TRUE integral original normalization map is actually surjective;
closed image +actual generic density, no surjectivity certificate. -/
instance originalNormalizationMap_surjective : Surjective (originalNormalizationMap X) := by
  infer_instance

variable (f : X ⟶ Spec (.of ℂ)) (E : SGPT.Foundations.Schemes.ClosedProjectiveEmbedding f)

include f E in
/-- The ACTUAL SAME original normalization map is FINITE, manufactured
on all original affine opens, including empty charts. No finite-map premise. -/
theorem originalNormalizationMap_finite : IsFinite (originalNormalizationMap X) := by
  refine { finite_app := ?_ }
  intro U hU
  classical
  by_cases h : Nonempty U
  · let : Nonempty U := h
    exact originalNormalizationMap_app_finite X U hU f E
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (h ⟨⟨x,hx⟩⟩)
      · exact bot_le
    let : Subsingleton Γ(X, U) := by rw [hbot]; infer_instance
    let : Subsingleton Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) :=
      ((originalNormalizationMap X).app U).hom.codomain_trivial
    exact RingHom.Finite.of_surjective _ (fun y => ⟨0, Subsingleton.elim _ y⟩)

include f E in
/-- The actual normalized ORIGINAL structural map is proper, from the
PRODUCED finite original normalization and SAME original projectivity. -/
theorem originalNormalizedStructureMap_isProper : IsProper (originalNormalizationMap X ≫ f) := by
  let := originalNormalizationMap_finite X f E
  let := E.isProper
  infer_instance

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
