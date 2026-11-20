import SGPT.Projective.OriginalProjectiveTwistComparison
import SGPT.LineBundle.RiemannRochAmple
import SGPT.Foundations.Envelope.AlgGeom.OriginalAmpleSerreVanishing
import SGPT.Foundations.Envelope.AlgGeom.SchemeLineAmpleness

/-! Genuine Serre H1 vanishing for the SAME original geometrically ample line. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry SGPT.Foundations.Schemes
attribute [local instance] Scheme.Modules.monoidalCategory
variable {X : Scheme.{0}} {L : X.Modules}

/-- Both original constructions iterate the SAME actual tensor sheafification. -/
theorem originalTensorPower_eq_native (L : X.Modules) (m : ℕ) :
    SGPT.Foundations.Schemes.bundleTensorPower L m =
      SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change SGPT.Foundations.Schemes.bundleTensor (SGPT.Foundations.Schemes.bundleTensorPower L m) L =
      SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensor
        (SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L m) L
    rw [ih]
    rfl

/-- The original actual ample polarization manufactures every accepted geometric ample field. -/
theorem nativeIsAmple_of_originalPolarization {f : X ⟶ Spec (.of ℂ)}
    (a : LineBundleAtlas L) (P : SGPT.LineBundle.AmplePolarization f L) :
    SGPT.Foundations.Envelope.SchemeLineAmpleness.IsAmple f L := by
  refine ⟨originalAtlas_isInvertible a, P.power, P.power_pos, P.ambientDimension,
    P.map, P.isClosedImmersion, ?_, ⟨?_⟩⟩
  · change P.map ≫ polynomialProjStructureMap ℂ P.ambientDimension = f
    exact P.over_base
  · exact ((Scheme.Modules.pullback P.map).mapIso
        (originalProjectiveTwistNativeIso P.ambientDimension 0)).symm ≪≫
      P.iso.symm ≪≫ eqToIso (originalTensorPower_eq_native L P.power)

/-- One actual bound kills H1 of EVERY sufficiently large ORIGINAL power, with all nilpotents retained. -/
theorem exists_originalAmple_sheafH1_bound {f : X ⟶ Spec (.of ℂ)}
    (a : LineBundleAtlas L) (P : SGPT.LineBundle.AmplePolarization f L) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H (SGPT.Foundations.Schemes.bundleTensorPower L m).sheaf 1) := by
  let aUnit := (intrinsicLineBundleOfFrame (Scheme.Modules.unitObj X) (Iso.refl _)).atlas
  let : (Scheme.Modules.unitObj X).IsQuasicoherent := aUnit.isQuasicoherent
  let : (Scheme.Modules.unitObj X).IsFiniteType := aUnit.isFiniteType
  let η : SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L P.power ≅
      (Scheme.Modules.pullback P.map).obj
        (MvPolynomial.coordinateHyperplaneTwist (R := ℂ) (0 : Fin (P.ambientDimension + 1)) 1) :=
    eqToIso (originalTensorPower_eq_native L P.power).symm ≪≫ P.iso ≪≫
      (Scheme.Modules.pullback P.map).mapIso (originalProjectiveTwistNativeIso P.ambientDimension 0)
  obtain ⟨B, hB⟩ := @SGPT.Foundations.Envelope.OriginalAmpleSerreVanishing.exists_sheafCohomology_bound
    ℂ _ _ (Fin (P.ambientDimension + 1)) _ X P.map P.isClosedImmersion
    (Scheme.Modules.unitObj X) L _ _ (originalAtlas_isInvertible a)
    P.power P.power_pos (0 : Fin (P.ambientDimension + 1)) η
  refine ⟨B, fun m hm => ?_⟩
  let ξ : Scheme.Modules.unitObj X ⊗ SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L m ≅
      SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L m :=
    ((SGPT.Support.ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  let eH := (CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X) 1).mapIso ((Scheme.Modules.toSheaf X).mapIso ξ)
  have hresult : Subsingleton (CategoryTheory.Sheaf.H
      (SGPT.Foundations.Envelope.CanonicalGeometry.bundleTensorPower L m).sheaf 1) :=
    AddCommGrpCat.subsingleton_of_isZero
      (IsZero.of_iso (@AddCommGrpCat.isZero_of_subsingleton _ (hB m hm 0)) eH.symm)
  rw [originalTensorPower_eq_native]
  exact hresult

end SGPT.Projective.NumEq.AlgebraicCurveDegree
