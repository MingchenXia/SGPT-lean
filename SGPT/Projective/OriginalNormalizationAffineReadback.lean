import SGPT.Projective.OriginalGenericPointNormalization

/-! ACTUAL original normalization affine sections = SAME original
integral-closure algebra, with TRUE original map coefficient square.
Blueprint: original-normalization-affine-readback.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry Opposite

variable (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) [Nonempty U]

/-- The actual generic inverse-open reader is a TRUE algebra equivalence
for the SAME original chart scalar, by the PROVED generic coefficient square. -/
def originalGenericPointSectionsAlgEquiv :
    letI := ((originalGenericPointMap X).app U).hom.toAlgebra
    Γ(Spec X.functionField, originalGenericPointMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField := by
  letI := ((originalGenericPointMap X).app U).hom.toAlgebra
  refine { (originalGenericPointSectionsIso X U).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  exact congrArg (fun h : Γ(X, U) ⟶ X.functionField => h r)
    (originalGenericPointMap_app_sectionsIso X U)

variable (hU : IsAffineOpen U)

/-- TRUE normalization section ring iso with the SAME original affine
integral closure in the SAME original function field, no renamed fraction
field/normalization ring. -/
def originalNormalizationAffineRingIso :
    Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U) X.functionField) := by
  letI := ((originalGenericPointMap X).app U).hom.toAlgebra
  exact originalNormalizationAffineSectionsIso X hU ≪≫
    (originalGenericPointSectionsAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

/-- EXACT actual original normalization map / original algebra inclusion
square on EVERY genuine nonempty original affine chart. No scalar square
or normalization-comparison premise. -/
theorem originalNormalizationMap_app_affineRingIso :
    (originalNormalizationMap X).app U ≫ (originalNormalizationAffineRingIso X U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField)) := by
  let := ((originalGenericPointMap X).app U).hom.toAlgebra
  change (originalGenericPointMap X).fromNormalization.app U ≫
    ((originalGenericPointMap X).normalizationObjIso hU ≪≫
      (originalGenericPointSectionsAlgEquiv X U).mapIntegralClosure.toRingEquiv.toCommRingCatIso).hom = _
  rw [Scheme.Hom.fromNormalization_app _ hU]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (originalGenericPointSectionsAlgEquiv X U).mapIntegralClosure.commutes r

/-- Genuine normalization affine algebra equivalence, with the actual
original normalization-map scalar action retained literally. -/
def originalNormalizationAffineAlgEquiv :
    letI := ((originalNormalizationMap X).app U).hom.toAlgebra
    Γ(originalNormalizationScheme X, originalNormalizationMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) X.functionField := by
  letI := ((originalNormalizationMap X).app U).hom.toAlgebra
  refine { (originalNormalizationAffineRingIso X U hU).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  exact congrArg (fun h : Γ(X, U) ⟶ CommRingCat.of (integralClosure Γ(X, U) X.functionField) => h r)
    (originalNormalizationMap_app_affineRingIso X U hU)

variable (f : X ⟶ Spec (.of ℂ)) (E : SGPT.Foundations.Schemes.ClosedProjectiveEmbedding f)

include f E hU in
/-- Actual original map on a TRUE normalization inverse-open has finite
module, produced from SAME original projective data and actual affine
algebra isomorphism. No finite-map/local-output certificate. -/
theorem originalNormalizationMap_app_finite : ((originalNormalizationMap X).app U).hom.Finite := by
  let := ((originalNormalizationMap X).app U).hom.toAlgebra
  let := originalAffineNormalization_finite f E hU
  exact Module.Finite.equiv (originalNormalizationAffineAlgEquiv X U hU).symm.toLinearEquiv

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
