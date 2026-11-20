import SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTraceRawAffineCoordinateImage
import SGPT.Foundations.PublishedEnvelope.AlgGeom.Canonical.ModuleSpecGammaCarrier

/-! # An original affine canonical coordinate before target normalization

Only the original source field algebra is used. The arbitrary target keeps
its literal composite structure, as in the actual mixed extension.
-/
noncomputable section
namespace SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (source, short, original) in [
      (`SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTraceRawAffineCoordinateImage,
        `originalWholeRawAffineCoordinateImage,
        `SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTrace.originalRawAffineCoordinateImage),
      (`SGPT.Foundations.PublishedEnvelope.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalRawCoordinateWedge,
        `SGPT.Foundations.PublishedEnvelope.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge),
      (`SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalCanonicalSourceCoordinate,
        `SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTrace.nativeCanonicalCoordinateSection_eq)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing original source coordinate producer"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private theorem originalRawAffineCanonicalCoordinateImage
    {K : Type u} [Field K] (R T : CommRingCat.{u}) [Algebra K R]
    (φ : R ⟶ T) (d : ℕ) (z : Fin d → R) :
    ((exteriorCotangentSheafMorphism (affineStructuralMap K R) (Spec.map φ) d).val.app
      (op ⊤)).hom.toFun
        (ModuleSpecGammaCarrier.toRaw R
          (exteriorCotangentSheaf (affineStructuralMap K R) d)
          (affineCanonicalCoordinateSection K R d z)) =
      originalRawCoordinateWedge (Spec.map φ ≫ affineStructuralMap K R) d
        (fun j => affineCoordinateMap T (op ⊤) (φ.hom (z j))) := by
  have hSource := originalCanonicalSourceCoordinate K R d z
  have hMapped := congrArg
    (fun w : (moduleSpecΓFunctor (R := R)).obj
      (exteriorCotangentSheaf (affineStructuralMap K R) d) =>
      ((exteriorCotangentSheafMorphism (affineStructuralMap K R) (Spec.map φ) d).val.app
        (op ⊤)).hom.toFun
          (ModuleSpecGammaCarrier.toRaw R
            (exteriorCotangentSheaf (affineStructuralMap K R) d) w)) hSource
  have hRaw := originalWholeRawAffineCoordinateImage R T (affineStructuralMap K R) φ d z
  exact hMapped.trans hRaw

end SGPT.Foundations.PublishedEnvelope.Vanishing.NadelGlobalCanonicalTrace
