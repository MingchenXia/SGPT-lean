import SGPT.Foundations.Schemes.TwistedModuleSectionAction
import SGPT.Foundations.Schemes.ProjectiveChartOverlap

/-! # The actual polynomial action on genuine projective twisted sections

The polynomial coordinates act by the actual global coordinate sections of
the genuine Proj twisting line.  This is a literal module construction on the
actual direct sum of tensor-twisted global sections.  Finiteness and the local
representation are not premises of this construction.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine degree-one twisting line on actual polynomial Proj. -/
def polynomialProjTwistingLine : IntrinsicLineBundle (polynomialProj K n) where
  sheaf := projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
  atlas := homogeneousPolynomialTwistingAtlas 1

/-- A literal global coordinate, included into the actual first tensor power
by the actual unit pure tensor. -/
def polynomialProjTwistedGlobalCoordinate (i : Fin (n + 1)) :
    bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf 1 :=
  tensorSection (SheafOfModules.unit (polynomialProj K n).ringCatSheaf)
    (polynomialProjTwistingLine K n).sheaf ⊤
    (show bundleSections (SheafOfModules.unit (polynomialProj K n).ringCatSheaf) ⊤
      from (1 : Γ(polynomialProj K n, ⊤)))
    (projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ ⊤)

/-- The genuine distinguished global coordinate has coefficient one in its own true frame. -/
theorem polynomialProjTwistedGlobalCoordinate_coefficient_self (i : Fin (n + 1)) :
    atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas 1 i
      (polynomialProjTwistedGlobalCoordinate K n i) = 1 := by
  unfold atlasPowerGlobalCoefficients polynomialProjTwistedGlobalCoordinate
  change (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower 1).coefficients (𝟙 _)
    ((bundleTensor (SheafOfModules.unit (polynomialProj K n).ringCatSheaf)
      (polynomialProjTwistingLine K n).sheaf).val.map
      (homOfLE (le_top : polynomialProjCoordinateOpen K n i ≤ ⊤)).op
      (tensorSection _ _ _ _ _)) = 1
  rw [tensorSection_restrict]
  change ((((polynomialProjTwistingLine K n).atlas.frame i).tensorPower 0).tensor
      ((polynomialProjTwistingLine K n).atlas.frame i)).coefficients (𝟙 _)
      (tensorSection _ _ _ _ _) = _
  rw [LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensorPower_zero_coefficients]
  change 1 * ((polynomialProjTwistingLine K n).atlas.frame i).coefficients (𝟙 _)
      (projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (polynomialProjCoordinateOpen K n i)) = 1
  rw [one_mul]
  change projectiveTwistingChartSectionsFrame
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (polynomialProjCoordinateOpen K n i) le_rfl
      (projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (polynomialProjCoordinateOpen K n i)) = 1
  have h := (projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    (polynomialProjCoordinateOpen K n i) le_rfl).apply_symm_apply 1
  simpa only [projectiveTwistingChartSectionsFrame, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply, projectiveTwistingCoordinateMul,
    LinearMap.toSpanSingleton_apply, one_smul] using h

/-- The literal polynomial-to-section-ring map uses true constants and true coordinate sections. -/
def polynomialProjTwistedSectionRingMap :
    MvPolynomial (Fin (n + 1)) K →+* (polynomialProjTwistingLine K n).sectionRing :=
  MvPolynomial.eval₂Hom
    ((polynomialProjTwistingLine K n).sectionRingBaseMap (polynomialProjStructureMap K n))
    (fun i => (polynomialProjTwistingLine K n).ofSection 1
      (polynomialProjTwistedGlobalCoordinate K n i))

/-- True polynomial constants act by their actual degree-zero regular sections. -/
theorem polynomialProjTwistedSectionRingMap_C (c : K) :
    polynomialProjTwistedSectionRingMap K n (MvPolynomial.C c) =
      (polynomialProjTwistingLine K n).ofSection 0
        (schemeConstantMap (polynomialProjStructureMap K n) c) := by
  simp [polynomialProjTwistedSectionRingMap, IntrinsicLineBundle.sectionRingBaseMap_apply]

/-- Every actual polynomial coordinate maps to its actual global degree-one section. -/
theorem polynomialProjTwistedSectionRingMap_X (i : Fin (n + 1)) :
    polynomialProjTwistedSectionRingMap K n (MvPolynomial.X i) =
      (polynomialProjTwistingLine K n).ofSection 1 (polynomialProjTwistedGlobalCoordinate K n i) := by
  simp [polynomialProjTwistedSectionRingMap]

/-- The actual direct sum of genuine projective twists of the actual module sheaf. -/
abbrev polynomialProjTwistedSectionModule (M : (polynomialProj K n).Modules) :=
  (polynomialProjTwistingLine K n).twistedSectionModule M

/-- Its polynomial action is induced by the actual polynomial coordinate-section map. -/
instance polynomialProjTwistedSectionModulePolynomialModule
    (M : (polynomialProj K n).Modules) :
    Module (MvPolynomial (Fin (n + 1)) K) (polynomialProjTwistedSectionModule K n M) :=
  Module.compHom (polynomialProjTwistedSectionModule K n M)
    (polynomialProjTwistedSectionRingMap K n)

/-- Multiplication by a polynomial coordinate is the actual homogeneous global twist action. -/
theorem polynomialProjTwistedSectionModule_X_smul
    (M : (polynomialProj K n).Modules) (i : Fin (n + 1)) (d : ℕ)
    (s : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) •
        (polynomialProjTwistingLine K n).ofTwistedSection M d s =
      (polynomialProjTwistingLine K n).ofTwistedSection M (1 + d)
        (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M 1 d
          (polynomialProjTwistedGlobalCoordinate K n i) s) := by
  change polynomialProjTwistedSectionRingMap K n (MvPolynomial.X i) •
      (polynomialProjTwistingLine K n).ofTwistedSection M d s = _
  rw [polynomialProjTwistedSectionRingMap_X]
  exact (polynomialProjTwistingLine K n).ofSection_smul_ofTwistedSection M 1 d
    (polynomialProjTwistedGlobalCoordinate K n i) s

/-- Polynomial constants have the native regular-section action on every genuine twist. -/
theorem polynomialProjTwistedSectionModule_C_smul
    (M : (polynomialProj K n).Modules) (c : K) (d : ℕ)
    (s : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    (MvPolynomial.C c : MvPolynomial (Fin (n + 1)) K) •
        (polynomialProjTwistingLine K n).ofTwistedSection M d s =
      (polynomialProjTwistingLine K n).ofTwistedSection M d
        ((schemeConstantMap (polynomialProjStructureMap K n) c) • s) := by
  change polynomialProjTwistedSectionRingMap K n (MvPolynomial.C c) •
      (polynomialProjTwistingLine K n).ofTwistedSection M d s = _
  rw [polynomialProjTwistedSectionRingMap_C]
  exact (polynomialProjTwistingLine K n).ofSection_constant_smul_ofTwistedSection M d
    (schemeConstantMap (polynomialProjStructureMap K n) c) s

end

end SGPT.Foundations.Schemes
