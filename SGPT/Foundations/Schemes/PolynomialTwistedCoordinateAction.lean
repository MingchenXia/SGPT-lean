import SGPT.Foundations.Schemes.PolynomialTwistedSectionModule

/-! # Actual coordinate powers on genuine twisted sections

The coordinate coefficient is the literal ratio in the native Proj chart.
The resulting polynomial power action is the true global sheaf action, with
its coefficients computed in every genuine coordinate frame.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal cancellation of a native coordinate ratio in the actual localization. -/
theorem polynomialProjCoordinateRatio_mul_coordinate_val (i j : Fin (n + 1)) :
    (polynomialProjCoordinateRatio K n i j).val *
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
        (MvPolynomial.X i) =
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
        (MvPolynomial.X j) := by
  rw [polynomialProjCoordinateRatio_val, mul_assoc, mul_comm
    (IsLocalization.Away.invSelf
      (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- Multiplication by the actual ratio reconstructs the actual coordinate section. -/
theorem polynomialProjTwistingCoordinateMul_ratio (i j : Fin (n + 1)) :
    projectiveTwistingCoordinateMul (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
      (polynomialProjCoordinateOpen K n j)
      (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i)) =
    projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (polynomialProjCoordinateOpen K n j) := by
  apply Subtype.ext
  funext x
  change ((homogeneousPolynomialBasicOpenAwayEquiv j
      (polynomialProjCoordinateRatio K n j i)).val x).val *
    algebraMap (MvPolynomial (Fin (n + 1)) K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) x.val)
      ((MvPolynomial.X j) ^ 1) =
    algebraMap (MvPolynomial (Fin (n + 1)) K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) x.val)
      ((MvPolynomial.X i) ^ 1)
  rw [pow_one, pow_one]
  have he : ((homogeneousPolynomialBasicOpenAwayEquiv j
      (polynomialProjCoordinateRatio K n j i)).val x).val =
      homogeneousPolynomialCoordinateAtPoint j x.val x.property
        (polynomialProjCoordinateRatio K n j i).val :=
    homogeneousPolynomialBasicOpenAwayEquiv_eval j
      (polynomialProjCoordinateRatio K n j i) x.val x.property
  rw [he]
  have h := congrArg (homogeneousPolynomialCoordinateAtPoint j x.val x.property)
    (polynomialProjCoordinateRatio_mul_coordinate_val K n j i)
  simpa only [map_mul, homogeneousPolynomialCoordinateAtPoint_algebraMap] using h

/-- A genuine global coordinate has its literal ratio coefficient in every true chart. -/
theorem polynomialProjTwistedGlobalCoordinate_coefficient (i j : Fin (n + 1)) :
    atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas 1 j
      (polynomialProjTwistedGlobalCoordinate K n i) =
    homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i) := by
  unfold atlasPowerGlobalCoefficients polynomialProjTwistedGlobalCoordinate
  change (((polynomialProjTwistingLine K n).atlas.frame j).tensorPower 1).coefficients (𝟙 _)
    ((bundleTensor (SheafOfModules.unit (polynomialProj K n).ringCatSheaf)
      (polynomialProjTwistingLine K n).sheaf).val.map
      (homOfLE (le_top : polynomialProjCoordinateOpen K n j ≤ ⊤)).op
      (tensorSection _ _ _ _ _)) = _
  rw [tensorSection_restrict]
  change ((((polynomialProjTwistingLine K n).atlas.frame j).tensorPower 0).tensor
      ((polynomialProjTwistingLine K n).atlas.frame j)).coefficients (𝟙 _)
      (tensorSection _ _ _ _ _) = _
  rw [LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensorPower_zero_coefficients]
  change 1 * ((polynomialProjTwistingLine K n).atlas.frame j).coefficients (𝟙 _)
      (projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (polynomialProjCoordinateOpen K n j)) = _
  rw [one_mul]
  change projectiveTwistingChartSectionsFrame
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
      (polynomialProjCoordinateOpen K n j) le_rfl
      (projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (polynomialProjCoordinateOpen K n j)) = _
  rw [← polynomialProjTwistingCoordinateMul_ratio K n i j]
  exact (projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
    (polynomialProjCoordinateOpen K n j) le_rfl).apply_symm_apply _

/-- Genuine repeated coordinate multiplication in the actual tensor powers. -/
def polynomialProjTwistedGlobalCoordinatePower (i : Fin (n + 1)) :
    (N : ℕ) → bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf N
  | 0 => bundlePowerGlobalOne (polynomialProjTwistingLine K n).sheaf
  | N + 1 => atlasPowerGlobalMul (polynomialProjTwistingLine K n).atlas N 1
      (polynomialProjTwistedGlobalCoordinatePower i N)
      (polynomialProjTwistedGlobalCoordinate K n i)

/-- The actual polynomial power maps to the actual homogeneous coordinate-power section. -/
theorem polynomialProjTwistedSectionRingMap_X_pow (i : Fin (n + 1)) (N : ℕ) :
    polynomialProjTwistedSectionRingMap K n ((MvPolynomial.X i) ^ N) =
      (polynomialProjTwistingLine K n).ofSection N
        (polynomialProjTwistedGlobalCoordinatePower K n i N) := by
  induction N with
  | zero =>
      simp only [pow_zero, map_one, polynomialProjTwistedGlobalCoordinatePower,
        IntrinsicLineBundle.ofSection_one]
  | succ N h =>
      rw [pow_succ, map_mul, h, polynomialProjTwistedSectionRingMap_X,
        IntrinsicLineBundle.ofSection_mul]
      rfl

/-- Every actual coordinate power has its literal ratio power as true chart coefficient. -/
theorem polynomialProjTwistedGlobalCoordinatePower_coefficient
    (i j : Fin (n + 1)) (N : ℕ) :
    atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas N j
      (polynomialProjTwistedGlobalCoordinatePower K n i N) =
      (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i)) ^ N := by
  induction N with
  | zero =>
      exact (atlasPowerGlobalCoefficients_one (polynomialProjTwistingLine K n).atlas j).trans
        (pow_zero _).symm
  | succ N h =>
      change atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas (N + 1) j
        (atlasPowerGlobalMul (polynomialProjTwistingLine K n).atlas N 1
          (polynomialProjTwistedGlobalCoordinatePower K n i N)
          (polynomialProjTwistedGlobalCoordinate K n i)) = _
      rw [atlasPowerGlobalMul_coefficients, h,
        polynomialProjTwistedGlobalCoordinate_coefficient, pow_succ]

/-- Actual polynomial powers act by the actual homogeneous global tensor action. -/
theorem polynomialProjTwistedSectionModule_X_pow_smul
    (M : (polynomialProj K n).Modules) (i : Fin (n + 1)) (N d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N •
        (polynomialProjTwistingLine K n).ofTwistedSection M d t =
      (polynomialProjTwistingLine K n).ofTwistedSection M (N + d)
        (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M N d
          (polynomialProjTwistedGlobalCoordinatePower K n i N) t) := by
  change polynomialProjTwistedSectionRingMap K n ((MvPolynomial.X i) ^ N) •
      (polynomialProjTwistingLine K n).ofTwistedSection M d t = _
  rw [polynomialProjTwistedSectionRingMap_X_pow]
  exact (polynomialProjTwistingLine K n).ofSection_smul_ofTwistedSection M N d
    (polynomialProjTwistedGlobalCoordinatePower K n i N) t

/-- The true polynomial power action has exactly the ratio-power action on all native coefficients. -/
theorem polynomialProjTwistedCoordinatePowerAction_coefficients
    (M : (polynomialProj K n).Modules) (i j : Fin (n + 1)) (N d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (N + d) j
      (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M N d
        (polynomialProjTwistedGlobalCoordinatePower K n i N) t) =
      (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i)) ^ N •
        atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t := by
  rw [atlasTwistedGlobalAction_coefficients, polynomialProjTwistedGlobalCoordinatePower_coefficient]

end

end SGPT.Foundations.Schemes
