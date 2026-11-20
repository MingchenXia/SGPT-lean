import SGPT.Foundations.Schemes.NativePolynomialPullbackPower
import SGPT.Foundations.Schemes.NativeTensorTwistTransport

/-!
# Actual projective tensor-twist comparison and its section action

The canonical projection map and the literal projective pullback-power
comparison give an actual sheaf isomorphism. Its genuine coordinate-frame
readback intertwines the actual global twisted section actions.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (M : X.Modules)

/-- The actual projection isomorphism followed by the literal pullback-power
comparison, without a supplied projection or representation certificate. -/
def nativePolynomialPullbackTwistIso (m : ℕ) :
    bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
      ((Scheme.Modules.pushforward f).obj M) ≅
    (Scheme.Modules.pushforward f).obj
      (bundleTensor (bundleTensorPower
        ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) m) M) := by
  have := nativePolynomialTwistingTensorPowerProjectionMap_isIso K n f m M
  exact asIso (nativeSchemeProjectionMap f
    (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M) ≪≫
      (Scheme.Modules.pushforward f).mapIso
        (bundleTensorIso (nativePolynomialPullbackPowerIso K n f m) (Iso.refl M))

/-- The genuine projection/pullback composite retains module-valued
coefficients on every subordinate projective coordinate open. -/
theorem nativePolynomialPullbackTwistIso_coefficients (m : ℕ) (i : Fin (n + 1))
    (W : (polynomialProj K n).Opens) (h : W ⟶ polynomialProjCoordinateOpen K n i)
    (t : bundleSections
      (bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
        ((Scheme.Modules.pushforward f).obj M)) W) :
    (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m).tensorModuleCoefficients M
      ((Opens.map f.base).map h)
      ((nativePolynomialPullbackTwistIso K n f M m).hom.val.app (.op W) t) =
    (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients
      ((Scheme.Modules.pushforward f).obj M) h t := by
  change (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m).tensorModuleCoefficients M
    ((Opens.map f.base).map h)
    ((bundleTensorIso (nativePolynomialPullbackPowerIso K n f m) (Iso.refl M)).hom.val.app
      (.op (f ⁻¹ᵁ W)) ((nativeSchemeProjectionMap f
        (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M).val.app (.op W) t)) = _
  refine (nativeTensorTwistIso_coefficients (nativePolynomialPullbackPowerIso K n f m)
    (nativePolynomialPowerPullbackFrame K n f m i)
    (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m)
    (fun W h s ↦ nativePolynomialPullbackPowerIso_coefficients K n f m i h s)
    M ((Opens.map f.base).map h) _).trans ?_
  have hc := nativeGeneratedLineProjectionMap_coefficients f
    (nativePolynomialPowerCoordinateHom K n m i) (polynomialProjCoordinateOpen K n i)
    M W h t
  rw [nativePolynomialPowerCoordinateHom_generatorFrame] at hc
  exact hc

/-- On genuine global sections the same composite retains exactly the
original module-valued coordinate coefficients. -/
theorem nativePolynomialPullbackTwistIso_globalCoefficients (m : ℕ) (i : Fin (n + 1))
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj M) m) :
    atlasTwistedGlobalCoefficients (nativePolynomialPullbackAtlas K n f) M m i
      ((nativePolynomialPullbackTwistIso K n f M m).hom.val.app (.op ⊤) t) =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj M) m i t := by
  let U := polynomialProjCoordinateOpen K n i
  let P := bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
    ((Scheme.Modules.pushforward f).obj M)
  let Q := bundleTensor (bundleTensorPower
    ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) m) M
  let E := nativePolynomialPullbackTwistIso K n f M m
  have hn := PresheafOfModules.naturality_apply E.hom.val U.leTop.op t
  change E.hom.val.app (.op U) (P.val.map U.leTop.op t) =
    Q.val.map (f ⁻¹ᵁ U).leTop.op (E.hom.val.app (.op ⊤) t) at hn
  have hc := nativePolynomialPullbackTwistIso_coefficients K n f M m i U (𝟙 _)
    (P.val.map U.leTop.op t)
  exact (congrArg
    ((((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m).tensorModuleCoefficients
      M (𝟙 _)) hn).symm.trans hc

/-- The literal additive pullback of actual projective power sections,
formed from the genuine adjunction unit and actual pullback-power comparison. -/
def nativePolynomialPullbackPowerSection (d : ℕ) :
    bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf d →+
      bundlePowerGlobalSections
        ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) d :=
  ((nativePolynomialPullbackPowerIso K n f d).hom.val.app (.op ⊤)).hom.toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d)).val.app
        (.op ⊤)).hom.toAddMonoidHom

/-- The actual power-section pullback has the literal structural-ring
pullback of each genuine projective coordinate coefficient. -/
theorem nativePolynomialPullbackPowerSection_coefficients (d : ℕ) (i : Fin (n + 1))
    (s : bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf d) :
    atlasPowerGlobalCoefficients (nativePolynomialPullbackAtlas K n f) d i
      (nativePolynomialPullbackPowerSection K n f d s) =
    f.app (polynomialProjCoordinateOpen K n i)
      (atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas d i s) := by
  let U := polynomialProjCoordinateOpen K n i
  let P := bundleTensorPower (polynomialProjTwistingLine K n).sheaf d
  let Q := (Scheme.Modules.pullback f).obj P
  let R := bundleTensorPower
    ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) d
  let C := nativePolynomialPullbackPowerIso K n f d
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P
  let z : bundleSections Q ⊤ := η.val.app (.op ⊤) s
  have hC := PresheafOfModules.naturality_apply C.hom.val (f ⁻¹ᵁ U).leTop.op z
  change C.hom.val.app (.op (f ⁻¹ᵁ U)) (Q.val.map (f ⁻¹ᵁ U).leTop.op z) =
    R.val.map (f ⁻¹ᵁ U).leTop.op (nativePolynomialPullbackPowerSection K n f d s) at hC
  have hη := PresheafOfModules.naturality_apply η.val U.leTop.op s
  change η.val.app (.op U) (P.val.map U.leTop.op s) =
    Q.val.map (f ⁻¹ᵁ U).leTop.op z at hη
  have hp := nativePolynomialPullbackPowerIso_coefficients K n f d i (𝟙 _)
    (η.val.app (.op U) (P.val.map U.leTop.op s))
  have hg := nativeGeneratorPullback_coefficient_square f
    (nativePolynomialPowerCoordinateHom K n d i) U U (𝟙 _)
    (P.val.map U.leTop.op s)
  rw [nativePolynomialPowerCoordinateHom_generatorFrame] at hg
  let c := (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower d).coefficients (𝟙 _)
  exact (congrArg c hC).symm.trans
    ((congrArg (fun v ↦ c (C.hom.val.app (.op (f ⁻¹ᵁ U)) v)) hη.symm).trans (hp.trans hg))

/-- The actual projection/pullback-power comparison intertwines the genuine
global twisted action with the literal pullback of its acting power section. -/
theorem nativePolynomialPullbackTwistIso_globalAction (d m : ℕ)
    (s : bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf d)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj M) m) :
    (nativePolynomialPullbackTwistIso K n f M (d + m)).hom.val.app (.op ⊤)
      (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas
        ((Scheme.Modules.pushforward f).obj M) d m s t) =
    atlasTwistedGlobalAction (nativePolynomialPullbackAtlas K n f) M d m
      (nativePolynomialPullbackPowerSection K n f d s)
      ((nativePolynomialPullbackTwistIso K n f M m).hom.val.app (.op ⊤) t) := by
  apply atlasTwistedGlobalCoefficients_ext (nativePolynomialPullbackAtlas K n f) M (d + m)
  intro i
  rw [nativePolynomialPullbackTwistIso_globalCoefficients,
    atlasTwistedGlobalAction_coefficients, atlasTwistedGlobalAction_coefficients,
    nativePolynomialPullbackPowerSection_coefficients,
    nativePolynomialPullbackTwistIso_globalCoefficients]
  rfl

end
end SGPT.Foundations.Schemes
