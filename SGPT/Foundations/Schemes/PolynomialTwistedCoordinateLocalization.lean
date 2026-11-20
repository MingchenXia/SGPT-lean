import SGPT.Foundations.Schemes.PolynomialTwistedSectionGrading
import SGPT.Foundations.Schemes.PolynomialTwistedSectionUniqueness
import SGPT.Foundations.Schemes.PolynomialTwistedGlobalExtension

/-! # Actual normalized coordinate localization of genuine twisted sections

The actual coefficient sum dehomogenizes the literal Γ-star module. Its
polynomial scalar action sends each variable to the true regular ratio.
The native localization universal property then produces the actual
degree-zero coordinate map, retaining genuine localization torsion.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine structural constants restricted to the actual coordinate open. -/
def polynomialTwistedCoordinateConstants (i : Fin (n + 1)) :
    K →+* Γ(polynomialProj K n, polynomialProjCoordinateOpen K n i) :=
  ((polynomialProj K n).presheaf.map (homOfLE le_top).op).hom.comp
    (schemeConstantMap (polynomialProjStructureMap K n))

/-- Actual polynomial dehomogenization takes values in actual regular coordinate sections. -/
def polynomialTwistedCoordinatePolynomialMap (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) K →+*
      Γ(polynomialProj K n, polynomialProjCoordinateOpen K n i) :=
  MvPolynomial.eval₂Hom (polynomialTwistedCoordinateConstants K n i)
    (fun j => homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j))

/-- The actual inverted coordinate has true normalized value one. -/
theorem polynomialTwistedCoordinatePolynomialMap_self (i : Fin (n + 1)) :
    polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.X i) = 1 := by
  simp [polynomialTwistedCoordinatePolynomialMap, polynomialProjCoordinateRatio_self]

variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))

/-- The coordinate-section field action is the true restricted structural action. -/
instance polynomialTwistedCoordinateSectionsBaseModule :
    Module K (bundleSections M (polynomialProjCoordinateOpen K n i)) :=
  Module.compHom _ (polynomialTwistedCoordinateConstants K n i)

/-- The actual polynomial action on coordinate sections is true dehomogenized multiplication. -/
instance polynomialTwistedCoordinateSectionsPolynomialModule :
    Module (MvPolynomial (Fin (n + 1)) K)
      (bundleSections M (polynomialProjCoordinateOpen K n i)) :=
  Module.compHom _ (polynomialTwistedCoordinatePolynomialMap K n i)

/-- Actual polynomial constants agree with the true restricted field action. -/
instance polynomialTwistedCoordinateSectionsScalarTower :
    IsScalarTower K (MvPolynomial (Fin (n + 1)) K)
      (bundleSections M (polynomialProjCoordinateOpen K n i)) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c s
  change polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.C c) • s =
    polynomialTwistedCoordinateConstants K n i c • s
  simp [polynomialTwistedCoordinatePolynomialMap]

/-- Each genuine global twist has its true additive coordinate coefficient map. -/
def polynomialTwistedCoordinateCoefficient (d : ℕ) :
    bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d →+
      bundleSections M (polynomialProjCoordinateOpen K n i) where
  toFun := atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i
  map_zero' := atlasTwistedGlobalCoefficients_zero _ _ _ _
  map_add' := atlasTwistedGlobalCoefficients_add _ _ _ _

/-- Actual coordinate coefficients are summed on the literal actual direct sum Γ-star. -/
def polynomialTwistedCoordinateCoefficientSum :
    polynomialProjTwistedSectionModule K n M →+ bundleSections M (polynomialProjCoordinateOpen K n i) :=
  DirectSum.toAddMonoid (polynomialTwistedCoordinateCoefficient K n M i)

/-- A true homogeneous singleton evaluates to its actual chart coefficient. -/
theorem polynomialTwistedCoordinateCoefficientSum_of (d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    polynomialTwistedCoordinateCoefficientSum K n M i
      ((polynomialProjTwistingLine K n).ofTwistedSection M d t) =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t :=
  DirectSum.toAddMonoid_of _ d t

/-- Every true coordinate acts on actual coefficients by its literal regular ratio. -/
theorem polynomialTwistedCoordinateCoefficientSum_X_smul
    (j : Fin (n + 1)) (x : polynomialProjTwistedSectionModule K n M) :
    polynomialTwistedCoordinateCoefficientSum K n M i
      ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K) • x) =
      polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.X j) •
        polynomialTwistedCoordinateCoefficientSum K n M i x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d t =>
    change polynomialTwistedCoordinateCoefficientSum K n M i
      ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K) •
        (polynomialProjTwistingLine K n).ofTwistedSection M d t) = _
    erw [← pow_one (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K),
      polynomialProjTwistedSectionModule_X_pow_smul K n M j 1 d t,
      polynomialTwistedCoordinateCoefficientSum_of K n M i,
      polynomialTwistedCoordinateCoefficientSum_of K n M i d t,
      polynomialProjTwistedCoordinatePowerAction_coefficients K n M j i 1 d t, pow_one]
    simp [polynomialTwistedCoordinatePolynomialMap]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]

/-- True structural polynomial constants act on actual coefficients by the actual restricted constants. -/
theorem polynomialTwistedCoordinateCoefficientSum_C_smul
    (c : K) (x : polynomialProjTwistedSectionModule K n M) :
    polynomialTwistedCoordinateCoefficientSum K n M i
      ((MvPolynomial.C c : MvPolynomial (Fin (n + 1)) K) • x) =
      polynomialTwistedCoordinatePolynomialMap K n i (MvPolynomial.C c) •
        polynomialTwistedCoordinateCoefficientSum K n M i x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d t =>
    change polynomialTwistedCoordinateCoefficientSum K n M i
      ((MvPolynomial.C c : MvPolynomial (Fin (n + 1)) K) •
        (polynomialProjTwistingLine K n).ofTwistedSection M d t) = _
    erw [polynomialProjTwistedSectionModule_C_smul K n M c d t,
      polynomialTwistedCoordinateCoefficientSum_of K n M i,
      polynomialTwistedCoordinateCoefficientSum_of K n M i d t]
    unfold atlasTwistedGlobalCoefficients
    rw [PresheafOfModules.map_smul, LinearEquiv.map_smul]
    simp [polynomialTwistedCoordinatePolynomialMap, polynomialTwistedCoordinateConstants]
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Genuine polynomial multiplication is genuine normalized coordinate multiplication. -/
theorem polynomialTwistedCoordinateCoefficientSum_smul
    (p : MvPolynomial (Fin (n + 1)) K) (x : polynomialProjTwistedSectionModule K n M) :
    polynomialTwistedCoordinateCoefficientSum K n M i (p • x) =
      polynomialTwistedCoordinatePolynomialMap K n i p •
        polynomialTwistedCoordinateCoefficientSum K n M i x := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C c => exact polynomialTwistedCoordinateCoefficientSum_C_smul K n M i c x
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]
  | mul_X p j hp =>
    rw [mul_smul, hp, polynomialTwistedCoordinateCoefficientSum_X_smul,
      map_mul, mul_smul]

/-- The true coefficient sum is a linear map for the actual dehomogenized polynomial action. -/
def polynomialTwistedCoordinateEvaluation :
    polynomialProjTwistedSectionModule K n M →ₗ[MvPolynomial (Fin (n + 1)) K]
      bundleSections M (polynomialProjCoordinateOpen K n i) where
  toAddHom := polynomialTwistedCoordinateCoefficientSum K n M i
  map_smul' := polynomialTwistedCoordinateCoefficientSum_smul K n M i

/-- Every actual denominator coordinate power acts by the actual identity on normalized chart sections. -/
theorem polynomialTwistedCoordinateLocalizationUnits :
    ∀ s : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K),
      IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Module.End (MvPolynomial (Fin (n + 1)) K)
          (bundleSections M (polynomialProjCoordinateOpen K n i))) s) := by
  intro s
  have he : algebraMap (MvPolynomial (Fin (n + 1)) K)
      (Module.End (MvPolynomial (Fin (n + 1)) K)
        (bundleSections M (polynomialProjCoordinateOpen K n i))) s = 1 := by
    apply LinearMap.ext
    intro t
    obtain ⟨N, hN⟩ := s.property
    change polynomialTwistedCoordinatePolynomialMap K n i s.val • t = t
    rw [← hN, map_pow, polynomialTwistedCoordinatePolynomialMap_self, one_pow, one_smul]
  rw [he]
  exact isUnit_one

/-- The genuine module localization descends actual normalized coordinate evaluation. -/
def polynomialTwistedLocalizedCoordinateEvaluation :
    LocalizedModule (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
      (polynomialProjTwistedSectionModule K n M) →ₗ[MvPolynomial (Fin (n + 1)) K]
      bundleSections M (polynomialProjCoordinateOpen K n i) :=
  LocalizedModule.lift _ (polynomialTwistedCoordinateEvaluation K n M i)
    (polynomialTwistedCoordinateLocalizationUnits K n M i)

/-- Every actual normalized coordinate fraction evaluates by its literal true numerator coefficient sum. -/
theorem polynomialTwistedLocalizedCoordinateEvaluation_mk
    (x : polynomialProjTwistedSectionModule K n M) (N : ℕ) :
    polynomialTwistedLocalizedCoordinateEvaluation K n M i
      (LocalizedModule.mk x (homogeneousPowerDenominator (MvPolynomial.X i) N)) =
    polynomialTwistedCoordinateCoefficientSum K n M i x := by
  rw [polynomialTwistedLocalizedCoordinateEvaluation, LocalizedModule.lift_mk,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff]
  change polynomialTwistedCoordinateCoefficientSum K n M i x =
    polynomialTwistedCoordinatePolynomialMap K n i ((MvPolynomial.X i) ^ N) •
      polynomialTwistedCoordinateCoefficientSum K n M i x
  rw [map_pow, polynomialTwistedCoordinatePolynomialMap_self, one_pow, one_smul]

/-- The literal degree-zero localized Γ-star piece in the genuine integral polynomial grading. -/
abbrev polynomialTwistedCoordinateDegreeZero :=
  localizedHomogeneousModulePiece
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedSectionPiece K n M) (MvPolynomial.X i) 1
    (polynomialCoordinate_X_degree i) 0

/-- Actual normalized homogeneous degree-zero fractions map linearly to actual structural chart sections. -/
def polynomialTwistedCoordinateDegreeZeroMap :
    polynomialTwistedCoordinateDegreeZero K n M i →ₗ[K]
      bundleSections M (polynomialProjCoordinateOpen K n i) :=
  ((polynomialTwistedLocalizedCoordinateEvaluation K n M i).restrictScalars K).comp
    (polynomialTwistedCoordinateDegreeZero K n M i).subtype

/-- A genuine degree-d numerator divided by Xi to its actual degree has its literal actual frame coefficient. -/
theorem polynomialTwistedCoordinateDegreeZeroMap_fraction
    (d : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    polynomialTwistedCoordinateDegreeZeroMap K n M i
      ⟨LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M d t)
        (homogeneousPowerDenominator (MvPolynomial.X i) d),
        d, (polynomialProjTwistingLine K n).ofTwistedSection M d t,
        (by simpa using polynomialProjTwistedSectionPiece_ofTwistedSection K n M d t), rfl⟩ =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t := by
  exact (polynomialTwistedLocalizedCoordinateEvaluation_mk K n M i
    ((polynomialProjTwistingLine K n).ofTwistedSection M d t) d).trans
    (polynomialTwistedCoordinateCoefficientSum_of K n M i d t)

/-- Every actual degree-zero localized element has a genuine homogeneous twisted-section fraction. -/
theorem polynomialTwistedCoordinateDegreeZero_fraction_exists
    (z : polynomialTwistedCoordinateDegreeZero K n M i) :
    ∃ (d : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d),
      LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M d t)
        (homogeneousPowerDenominator (MvPolynomial.X i) d) = z.val := by
  obtain ⟨d, x, hx, he⟩ := z.property
  have hx' : x ∈ polynomialProjTwistedSectionPiece K n M (d : ℤ) := by simpa using hx
  let y : ⨁ e : ℕ, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M e := x
  have hsingle : x = (polynomialProjTwistingLine K n).ofTwistedSection M d (y d) :=
    nonnegativeDirectSumPiece_eq_single K
      (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) d ⟨y, hx'⟩
  exact ⟨d, y d, hsingle ▸ he⟩

/-- True coordinate-power uniqueness makes actual normalized homogeneous localization faithful. -/
theorem polynomialTwistedCoordinateDegreeZeroMap_injective
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent] :
    Function.Injective (polynomialTwistedCoordinateDegreeZeroMap K n M i) := by
  apply (polynomialTwistedCoordinateDegreeZeroMap K n M i).ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    obtain ⟨d, t, ht⟩ := polynomialTwistedCoordinateDegreeZero_fraction_exists K n M i z
    have hc : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0 := by
      change polynomialTwistedLocalizedCoordinateEvaluation K n M i z.val = 0 at hz
      rw [← ht, polynomialTwistedLocalizedCoordinateEvaluation_mk,
        polynomialTwistedCoordinateCoefficientSum_of] at hz
      exact hz
    obtain ⟨N, hN⟩ := polynomialTwistedSection_X_pow_zero K n M i d t hc
    change z = 0
    apply Subtype.ext
    rw [← ht]
    change LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M d t)
      (homogeneousPowerDenominator (MvPolynomial.X i) d) = 0
    rw [← LocalizedModule.zero_mk
      (1 : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨homogeneousPowerDenominator (MvPolynomial.X i) N, ?_⟩
    simpa only [Submonoid.smul_def, homogeneousPowerDenominator, one_smul, smul_zero] using hN
  · exact bot_le

/-- Genuine extension of actual chart sections supplies honest normalized localization surjectivity. -/
theorem polynomialTwistedCoordinateDegreeZeroMap_surjective
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent] :
    Function.Surjective (polynomialTwistedCoordinateDegreeZeroMap K n M i) := by
  intro s
  obtain ⟨d, t, ht⟩ := polynomialProjCoordinateSection_twistedGlobalExtension K n M i s
  refine ⟨⟨LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M d t)
    (homogeneousPowerDenominator (MvPolynomial.X i) d),
    d, (polynomialProjTwistingLine K n).ofTwistedSection M d t,
    (by simpa using polynomialProjTwistedSectionPiece_ofTwistedSection K n M d t), rfl⟩, ?_⟩
  exact (polynomialTwistedCoordinateDegreeZeroMap_fraction K n M i d t).trans ht

/-- The actual degree-zero localized Γ-star module is equivalent to actual structurally scalar chart sections. -/
def polynomialTwistedCoordinateDegreeZeroEquiv
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent] :
    polynomialTwistedCoordinateDegreeZero K n M i ≃ₗ[K]
      bundleSections M (polynomialProjCoordinateOpen K n i) :=
  LinearEquiv.ofBijective (polynomialTwistedCoordinateDegreeZeroMap K n M i)
    ⟨polynomialTwistedCoordinateDegreeZeroMap_injective K n M i,
      polynomialTwistedCoordinateDegreeZeroMap_surjective K n M i⟩

end
end SGPT.Foundations.Schemes
