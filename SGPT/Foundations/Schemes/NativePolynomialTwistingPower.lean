import SGPT.Foundations.Schemes.NativeGeneratedProjectionFormula
import SGPT.Foundations.Schemes.PolynomialProjectiveTwistingTransition
/-!
# NativePolynomialTwistingPower

Literal native tensor powers of polynomial-Proj O(1) and actual twisting sheaves O(m) have matching true coordinate transitions. Genuine frame descent gives their actual sheaf isomorphism and all smaller-open coefficient readbacks. Real projective coordinate generators give the canonical native projection formula for every such tensor power.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativePolynomialTwistingPowerMatching (m : ℕ)
    (i j : Fin (n + 1)) (W : (polynomialProj K n).Opens)
    (h : W ⟶ polynomialProjCoordinateOpen K n i)
    (k : W ⟶ polynomialProjCoordinateOpen K n j) :
    localBundleFrameTransition
      (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m)
      (((polynomialProjTwistingLine K n).atlas.frame j).tensorPower m) h k =
    localBundleFrameTransition
      ((homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame i)
      ((homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame j) h k := by
  rw [localBundleFrameTransition_tensorPower]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (↑(localBundleFrameTransition
    (projectiveTwistingCoordinateFrame _ 1 ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)
    (projectiveTwistingCoordinateFrame _ 1 ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩) h k) : (polynomialProj K n).sheaf.obj.obj (.op W)) ^ m =
    (↑(localBundleFrameTransition
    (projectiveTwistingCoordinateFrame _ m ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)
    (projectiveTwistingCoordinateFrame _ m ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩) h k) : (polynomialProj K n).sheaf.obj.obj (.op W))
  rw [polynomialProjTwistingFrame_transition_ratio K n i j 1,
    polynomialProjTwistingFrame_transition_ratio K n i j m, pow_one]

/-- Actual tensor powers of native polynomial-Proj O(1) are genuinely isomorphic to the actual twisting sheaf O(m). -/
def nativePolynomialTwistingPowerIso (m : ℕ) :
    bundleTensorPower (polynomialProjTwistingLine K n).sheaf m ≅
      projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m :=
  nativeMatchingBundleFrameIso _ _ (polynomialProjCoordinateOpen K n)
    (polynomialProjTwistingLine K n).atlas.covers
    (fun i ↦ ((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m)
    (fun i ↦ (homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame i)
    (nativePolynomialTwistingPowerMatching K n m)

/-- The genuine twisting comparison retains every literal smaller-open frame coefficient. -/
theorem nativePolynomialTwistingPowerIso_coefficients (m : ℕ) (i : Fin (n + 1))
    {W : (polynomialProj K n).Opens} (h : W ⟶ polynomialProjCoordinateOpen K n i)
    (s : bundleSections (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) W) :
    ((homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame i).coefficients h
      ((nativePolynomialTwistingPowerIso K n m).hom.val.app (.op W) s) =
    (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients _ _ (polynomialProjCoordinateOpen K n)
    (polynomialProjTwistingLine K n).atlas.covers
    (fun i ↦ ((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m)
    (fun i ↦ (homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame i)
    (nativePolynomialTwistingPowerMatching K n m) i h s

/-- The actual canonical projection formula holds for all genuine tensor powers of native polynomial-Proj O(1). -/
theorem nativePolynomialTwistingTensorPowerProjectionMap_isIso {X : Scheme}
    (f : X ⟶ polynomialProj K n) (m : ℕ) (M : X.Modules) :
    IsIso (nativeSchemeProjectionMap f
      (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M) := by
  let E := nativePolynomialTwistingPowerIso K n m
  let α (i : Fin (n + 1)) :=
    projectiveTwistingCoordinateGlobalHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      m ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ ≫ E.inv
  apply nativeGeneratedLineProjectionMap_isIso f α (polynomialProjCoordinateOpen K n)
    (polynomialProjTwistingLine K n).atlas.covers
  intro i
  have hg : IsIso ((SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
      (polynomialProjCoordinateOpen K n i)).map
      (projectiveTwistingCoordinateGlobalHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        m ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)) := by
    exact (nativeModuleHom_over_isIso_iff_restrict _ _).mpr
      (projectiveTwistingCoordinateGlobalHom_restrict_isIso
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩)
  dsimp [α]
  rw [Functor.map_comp]
  infer_instance

end
end SGPT.Foundations.Schemes
