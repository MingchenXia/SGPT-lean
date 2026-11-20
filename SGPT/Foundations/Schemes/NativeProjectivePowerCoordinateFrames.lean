import SGPT.Foundations.Schemes.NativePolynomialTwistingPower
import SGPT.Foundations.Schemes.PolynomialTwistedGlobalExtension
/-!
# NativeProjectivePowerCoordinateFrames

Actual projective power coordinates transported to genuine O(1) tensor powers are exactly inverse original tensor-power frames. Actual pullback generators give genuine frames on inverse-image coordinate opens.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual degree-m projective coordinate is transported to the literal recursively formed tensor power. -/
def nativePolynomialPowerCoordinateHom (m : ℕ) (i : Fin (n + 1)) :
    SheafOfModules.unit (polynomialProj K n).ringCatSheaf ⟶
      bundleTensorPower (polynomialProjTwistingLine K n).sheaf m :=
  projectiveTwistingCoordinateGlobalHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    m ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ ≫
      (nativePolynomialTwistingPowerIso K n m).inv

/-- The genuine coordinate scalar map is exactly the inverse actual tensor-power frame on its true chart. -/
theorem nativePolynomialPowerCoordinateHom_over (m : ℕ) (i : Fin (n + 1)) :
    (SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
      (polynomialProjCoordinateOpen K n i)).map (nativePolynomialPowerCoordinateHom K n m i) =
      (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).inv := by
  let E := nativePolynomialTwistingPowerIso K n m
  let e := ((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m
  let d := (homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) m).frame i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply (e.coefficients W.unop.hom).injective
  let t := (projectiveTwistingCoordinateGlobalHom
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩).val.app (.op W.unop.left) r
  have he := nativePolynomialTwistingPowerIso_coefficients K n m i W.unop.hom
    (E.inv.val.app (.op W.unop.left) t)
  have hid := congrArg (fun a ↦ a.val.app (.op W.unop.left) t) E.inv_hom_id
  change E.hom.val.app (.op W.unop.left) (E.inv.val.app (.op W.unop.left) t) = t at hid
  change d.coefficients W.unop.hom
    (E.hom.val.app (.op W.unop.left) (E.inv.val.app (.op W.unop.left) t)) =
      e.coefficients W.unop.hom (E.inv.val.app (.op W.unop.left) t) at he
  rw [hid] at he
  have ht : d.coefficients W.unop.hom t = r := by
    change (projectiveTwistingChartSectionsFrame
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W.unop.left W.unop.hom.le)
        (projectiveTwistingCoordinateMul
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m
          ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W.unop.left r) = r
    exact (projectiveTwistingChartSectionsFrame
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ W.unop.left W.unop.hom.le).apply_symm_apply r
  change e.coefficients W.unop.hom (E.inv.val.app (.op W.unop.left) t) =
    e.coefficients W.unop.hom ((e.coefficients W.unop.hom).symm r)
  rw [LinearEquiv.apply_symm_apply]
  exact he.symm.trans ht

instance nativePolynomialPowerCoordinateHom_over_isIso (m : ℕ) (i : Fin (n + 1)) :
    IsIso ((SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
      (polynomialProjCoordinateOpen K n i)).map (nativePolynomialPowerCoordinateHom K n m i)) := by
  rw [nativePolynomialPowerCoordinateHom_over]
  infer_instance

/-- The generator frame of the actual power coordinate is the original genuine tensor-power frame. -/
theorem nativePolynomialPowerCoordinateHom_generatorFrame (m : ℕ) (i : Fin (n + 1)) :
    nativeGlobalGeneratorFrame (nativePolynomialPowerCoordinateHom K n m i)
      (polynomialProjCoordinateOpen K n i) =
        ((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m := by
  apply Iso.ext
  change inv ((SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
    (polynomialProjCoordinateOpen K n i)).map (nativePolynomialPowerCoordinateHom K n m i)) = _
  apply IsIso.inv_eq_of_hom_inv_id
  rw [nativePolynomialPowerCoordinateHom_over]
  exact (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).inv_hom_id

variable {X : Scheme} (f : X ⟶ polynomialProj K n)

/-- The actual pullback of a true tensor-power coordinate gives a genuine frame on the inverse-image chart. -/
def nativePolynomialPowerPullbackFrame (m : ℕ) (i : Fin (n + 1)) :
    LocalBundleFrame ((Scheme.Modules.pullback f).obj
      (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m))
      (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) :=
  nativePullbackGeneratorFrame f (nativePolynomialPowerCoordinateHom K n m i)
    (polynomialProjCoordinateOpen K n i)

end
end SGPT.Foundations.Schemes
