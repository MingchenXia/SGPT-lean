import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateAction
import SGPT.Foundations.Schemes.PolynomialProjectiveAnticanonical

/-! Literal coordinate-power transitions of the genuine projective twisting sheaf. -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The true regular-coordinate equivalence is the native homogeneous section map. -/
theorem polynomialProjCoordinateSectionMap_equiv (i : Fin (n + 1))
    (a : polynomialProjCoordinateRing K n i) :
    homogeneousPolynomialBasicOpenAwayEquiv i a = polynomialProjCoordinateSectionMap K n i a := rfl

/-- Multiplication by the literal ratio power reconstructs the literal coordinate-power section. -/
theorem polynomialProjTwistingCoordinateMul_ratio_pow (i j : Fin (n + 1)) (k : ℕ) :
    projectiveTwistingCoordinateMul (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
      (polynomialProjCoordinateOpen K n j)
      ((homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i)) ^ k) =
    projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (polynomialProjCoordinateOpen K n j) := by
  apply Subtype.ext
  funext x
  change (((homogeneousPolynomialBasicOpenAwayEquiv j
      (polynomialProjCoordinateRatio K n j i)).val x) ^ k).val *
    algebraMap (MvPolynomial (Fin (n + 1)) K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) x.val)
      ((MvPolynomial.X j) ^ k) =
    algebraMap (MvPolynomial (Fin (n + 1)) K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) x.val)
      ((MvPolynomial.X i) ^ k)
  have he : ((homogeneousPolynomialBasicOpenAwayEquiv j
      (polynomialProjCoordinateRatio K n j i)).val x).val =
      homogeneousPolynomialCoordinateAtPoint j x.val x.property
        (polynomialProjCoordinateRatio K n j i).val :=
    homogeneousPolynomialBasicOpenAwayEquiv_eval j
      (polynomialProjCoordinateRatio K n j i) x.val x.property
  rw [HomogeneousLocalization.val_pow, he, map_pow, map_pow, ← mul_pow]
  have h := congrArg (homogeneousPolynomialCoordinateAtPoint j x.val x.property)
    (polynomialProjCoordinateRatio_mul_coordinate_val K n j i)
  exact congrArg (fun a ↦ a ^ k)
    (by simpa only [map_mul, homogeneousPolynomialCoordinateAtPoint_algebraMap] using h)

/-- The actual normalized generator of the twisting frame is the literal coordinate power. -/
theorem polynomialProjTwistingFrame_generator (i : Fin (n + 1)) (k : ℕ)
    {W : (polynomialProj K n).Opens} (l : W ⟶ polynomialProjCoordinateOpen K n i) :
    ((projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩).coefficients l).symm 1 =
      projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W := by
  change projectiveTwistingCoordinateMul
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W 1 = _
  exact one_smul _ _

/-- The literal coordinate-power section has its literal ratio-power chart coefficient. -/
theorem polynomialProjTwistingCoordinateSection_coefficient (i j : Fin (n + 1)) (k : ℕ) :
    (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩).coefficients (𝟙 _)
      (projectiveTwistingCoordinateSection
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (polynomialProjCoordinateOpen K n j)) =
      polynomialProjCoordinateRegularRatio K n j i ^ k := by
  rw [← polynomialProjTwistingCoordinateMul_ratio_pow K n i j k]
  change projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
    (polynomialProjCoordinateOpen K n j) le_rfl _ = _
  exact (projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
    (polynomialProjCoordinateOpen K n j) le_rfl).apply_symm_apply _

/-- Genuine degree-k frame transitions on any true overlap are the restricted ratio powers. -/
theorem polynomialProjTwistingFrame_transition_ratio (i j : Fin (n + 1)) (k : ℕ)
    {W : (polynomialProj K n).Opens}
    (l : W ⟶ polynomialProjCoordinateOpen K n i)
    (r : W ⟶ polynomialProjCoordinateOpen K n j) :
    (↑(localBundleFrameTransition
      (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)
      (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩) l r) : (polynomialProj K n).sheaf.obj.obj (op W)) =
      (polynomialProj K n).presheaf.map r.op (polynomialProjCoordinateRegularRatio K n j i) ^ k := by
  let e := projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
  let f := projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
  have ht := localBundleFrameTransition_coefficients e f l r ((e.coefficients l).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at ht
  rw [polynomialProjTwistingFrame_generator] at ht
  apply ht.symm.trans
  have h := LocalBundleFrame.coefficients_restrict
    (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩)
    (𝟙 _) r (projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (polynomialProjCoordinateOpen K n j))
  rw [Category.comp_id] at h
  have hh := polynomialProjTwistingCoordinateSection_coefficient K n i j k
  rw [hh] at h
  change (f.coefficients r)
    (projectiveTwistingCoordinateSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W) = _ at h
  exact h.trans (map_pow _ _ k)

/-- On the actual homogeneous product overlap, the genuine degree-k transition is the inverse unit power. -/
theorem polynomialProjTwistingFrame_transition_unit (i j : Fin (n + 1)) (k : ℕ) :
    (↑(localBundleFrameTransition
      (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)
      (projectiveTwistingCoordinateFrame (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) k
        ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩)
      (polynomialProjOverlapLeftInclusion K n i j)
      (polynomialProjOverlapRightInclusion K n i j)) :
        (polynomialProj K n).sheaf.obj.obj (op (Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j)))) =
      (↑((polynomialProjOverlapRegularUnit K n i j)⁻¹) : Γ(polynomialProj K n, Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i * MvPolynomial.X j))) ^ k := by
  rw [polynomialProjTwistingFrame_transition_ratio K n i j k
      (polynomialProjOverlapLeftInclusion K n i j) (polynomialProjOverlapRightInclusion K n i j),
    polynomialProjCoordinateRegularRatio_restrict_right,
    polynomialProjOverlapRegularRatio_quotient, polynomialProjOverlapRegularRatio_self, one_mul]
end
end SGPT.Foundations.Schemes
