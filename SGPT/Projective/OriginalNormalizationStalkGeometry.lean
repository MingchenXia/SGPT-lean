import SGPT.Projective.OriginalNormalizationFiniteMap

/-! ACTUAL ORIGINAL normalized affine/local rings are normal Noetherian
domains; no smoothness assumption on the original integral projective X.
Blueprint: original-normalization-stalk-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open scoped nonZeroDivisors

variable (X : Scheme.{0}) [IsIntegral X]

/-- The ACTUAL original normalization inverse-affine section ring is
integrally closed, from its PROVED SAME original integral-closure ring iso. -/
theorem originalNormalizationAffine_sections_isIntegrallyClosed
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) := by
  let : IsIntegrallyClosed (integralClosure Γ(X, U) X.functionField) :=
    originalAffineNormalization_isIntegrallyClosed hU
  exact IsIntegrallyClosed.of_equiv
    (originalNormalizationAffineRingIso X U hU).symm.commRingCatIsoToRingEquiv

/-- EVERY true original normalization stalk is integrally closed.
The actual same inverse-affine chart/localization supplies the geometry;
no normalized-source normality certificate is assumed. -/
theorem originalNormalization_stalk_isIntegrallyClosed (z : originalNormalizationScheme X) :
    IsIntegrallyClosed ((originalNormalizationScheme X).presheaf.stalk z) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (originalNormalizationMap X z)) isOpen_univ
  let : Nonempty U := ⟨⟨originalNormalizationMap X z,hxU⟩⟩
  let V := originalNormalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (originalNormalizationMap X)
  have hzV : z ∈ V := hxU
  let : Nonempty V := ⟨⟨z,hzV⟩⟩
  let : IsIntegrallyClosed Γ(originalNormalizationScheme X, V) :=
    originalNormalizationAffine_sections_isIntegrallyClosed X hU
  let := TopCat.Presheaf.algebra_section_stalk (originalNormalizationScheme X).presheaf ⟨z,hzV⟩
  have := hV.isLocalization_stalk ⟨z,hzV⟩
  exact isIntegrallyClosed_of_isLocalization
    (R := Γ(originalNormalizationScheme X, V))
    (S := (originalNormalizationScheme X).presheaf.stalk z)
    (hV.primeIdealOf ⟨z,hzV⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

variable (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

include f E in
/-- SAME actual normalized original structural geometry is locally
Noetherian, from PRODUCED finite normalization and original projectivity. -/
theorem originalNormalization_isLocallyNoetherian : IsLocallyNoetherian (originalNormalizationScheme X) := by
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let : LocallyOfFiniteType (originalNormalizationMap X ≫ f) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (originalNormalizationMap X ≫ f)

include f E in
/-- EVERY actual original normalization stalk is Noetherian, including at
singular ORIGINAL curve points and all branches above them. -/
theorem originalNormalization_stalk_isNoetherian (z : originalNormalizationScheme X) :
    IsNoetherianRing ((originalNormalizationScheme X).presheaf.stalk z) := by
  let := originalNormalization_isLocallyNoetherian X f E
  infer_instance

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
