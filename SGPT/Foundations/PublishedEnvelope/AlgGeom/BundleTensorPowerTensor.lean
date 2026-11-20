import SGPT.Foundations.PublishedEnvelope.AlgGeom.BundleTensorPowerPullback

/-! # The SAME actual original tensor power of an original tensor product -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace SGPT.Foundations.PublishedEnvelope.BundleTensorPowerTensor
open CanonicalGeometry
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-- EVERY actual original tensor power splits into the SAME actual factor
powers, using only true tensor associativity, symmetry and structure units. -/
def powerTensorIso {X : Scheme.{u}} (A B : X.Modules) : (r : ℕ) →
    bundleTensorPower (A ⊗ B) r ≅ bundleTensorPower A r ⊗ bundleTensorPower B r
  | 0 => (SGPT.Support.PublishedModularCurves.unitObjTensorIso X).symm
  | r + 1 =>
    (SGPT.Support.PublishedModularCurves.monoidalTensorObjIso (bundleTensorPower (A ⊗ B) r) (A ⊗ B)).symm ≪≫
      (powerTensorIso A B r ⊗ᵢ Iso.refl (A ⊗ B)) ≪≫
      (α_ (bundleTensorPower A r) (bundleTensorPower B r) (A ⊗ B)) ≪≫
      whiskerLeftIso (bundleTensorPower A r) (α_ (bundleTensorPower B r) A B).symm ≪≫
      whiskerLeftIso (bundleTensorPower A r) ((β_ (bundleTensorPower B r) A) ⊗ᵢ Iso.refl B) ≪≫
      whiskerLeftIso (bundleTensorPower A r) (α_ A (bundleTensorPower B r) B) ≪≫
      (α_ (bundleTensorPower A r) A (bundleTensorPower B r ⊗ B)).symm ≪≫
      ((SGPT.Support.PublishedModularCurves.monoidalTensorObjIso (bundleTensorPower A r) A) ⊗ᵢ
        (SGPT.Support.PublishedModularCurves.monoidalTensorObjIso (bundleTensorPower B r) B))
end SGPT.Foundations.PublishedEnvelope.BundleTensorPowerTensor
