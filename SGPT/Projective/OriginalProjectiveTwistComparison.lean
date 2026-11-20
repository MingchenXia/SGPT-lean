import SGPT.Projective.OriginalProjectiveCoordinateFrames
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveHomogeneousSections

/-! Genuine original projective twisting line versus the accepted native Serre model. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open SGPT.Foundations.Envelope.ProjectiveHomogeneousSections

private theorem frameCoefficient_subopen {X : Scheme.{0}} {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (s : Γ(L, ⊤)) (c : Γ(X, U))
    (hc : e.coefficients (𝟙 U) (L.val.map U.leTop.op s) = c) (l : W ⟶ U) :
    e.coefficients l (L.val.map W.leTop.op s) = X.sheaf.obj.map l.op c := by
  have hm : L.val.map l.op (L.val.map U.leTop.op s) = L.val.map W.leTop.op s := by
    rw [← L.val.map_comp_apply]
    rfl
  calc
    _ = e.coefficients l (L.val.map l.op (L.val.map U.leTop.op s)) := congrArg _ hm.symm
    _ = X.sheaf.obj.map l.op (e.coefficients (𝟙 U) (L.val.map U.leTop.op s)) := by
      simpa only [Category.comp_id] using e.coefficients_restrict (𝟙 U) l _
    _ = _ := congrArg _ hc

/-- Both actual original coefficient maps apply to the SAME literal degree-one fraction. -/
theorem originalCoordinateRatio_eq_nativeCoefficient (N : ℕ) (i j : Fin (N + 1)) :
    polynomialProjCoordinateRegularRatio ℂ N i j =
      coefficient i 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) := rfl

/-- Actual accepted Serre-model coordinate frames on the original coordinate opens. -/
def originalNativeTwistFrame (N : ℕ) (k i : Fin (N + 1)) :
    LocalBundleFrame (MvPolynomial.coordinateHyperplaneTwist (R := ℂ) k 1)
      (polynomialProjCoordinateOpen ℂ N i) :=
  Scheme.Modules.overTrivializationOfRestrictIso _ _
    (MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i k 1)

private theorem nativeFrameCoordinate (N : ℕ) (k i j : Fin (N + 1))
    {W : (polynomialProj ℂ N).Opens} (l : W ⟶ polynomialProjCoordinateOpen ℂ N i) :
    (originalNativeTwistFrame N k i).coefficients l
      ((MvPolynomial.coordinateHyperplaneTwist (R := ℂ) k 1).val.map W.leTop.op
        (homogeneousSection k 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j))) =
      (polynomialProj ℂ N).sheaf.obj.map l.op (polynomialProjCoordinateRegularRatio ℂ N i j) := by
  apply frameCoefficient_subopen
  change SGPT.Support.ModularCurves.overTrivializationCoefficient
    (MvPolynomial.coordinateHyperplanePoleSheafPower (R := ℂ) k 1)
    (MvPolynomial.coordinateOpen (R := ℂ) i)
    (Scheme.Modules.overTrivializationOfRestrictIso _ _
      (MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := ℂ) i k 1))
    (homogeneousSection k 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)) =
      coefficient i 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)
  exact section_coefficient i k 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)

/-- Every actual native-model transition has the literal original restricted ratio. -/
theorem originalNativeTwistFrame_transition_ratio (N : ℕ) (k i j : Fin (N + 1))
    {W : (polynomialProj ℂ N).Opens}
    (l : W ⟶ polynomialProjCoordinateOpen ℂ N i)
    (r : W ⟶ polynomialProjCoordinateOpen ℂ N j) :
    (localBundleFrameTransition (originalNativeTwistFrame N k i)
      (originalNativeTwistFrame N k j) l r :
        (polynomialProj ℂ N).sheaf.obj.obj (op W)) =
      (polynomialProj ℂ N).sheaf.obj.map r.op (polynomialProjCoordinateRegularRatio ℂ N j i) := by
  let s := homogeneousSection k 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)
  have hi := nativeFrameCoordinate N k i i l
  rw [polynomialProjCoordinateRegularRatio_self, map_one] at hi
  have ht := localBundleFrameTransition_coefficients (originalNativeTwistFrame N k i)
    (originalNativeTwistFrame N k j) l r
    ((MvPolynomial.coordinateHyperplaneTwist (R := ℂ) k 1).val.map W.leTop.op s)
  rw [hi, mul_one] at ht
  exact ht.symm.trans (nativeFrameCoordinate N k j i r)

/-- Genuine whole original O(1) comparison, derived by matching the actual coordinate transitions. -/
def originalProjectiveTwistNativeIso (N : ℕ) (k : Fin (N + 1)) :
    (polynomialProjTwistingLine ℂ N).sheaf ≅
      MvPolynomial.coordinateHyperplaneTwist (R := ℂ) k 1 :=
  nativeMatchingBundleFrameIso _ _ (polynomialProjCoordinateOpen ℂ N)
    (polynomialProjTwistingLine ℂ N).atlas.covers
    (polynomialProjTwistingLine ℂ N).atlas.frame (originalNativeTwistFrame N k)
    (fun i j W l r => by
      apply Units.ext
      exact (polynomialProjTwistingFrame_transition_ratio ℂ N i j 1 l r).trans
        (by rw [pow_one]; exact (originalNativeTwistFrame_transition_ratio N k i j l r).symm))

end SGPT.Projective.NumEq.AlgebraicCurveDegree
