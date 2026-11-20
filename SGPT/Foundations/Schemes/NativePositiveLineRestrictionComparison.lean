import SGPT.Foundations.Schemes.BundleTensorRightUnit
import SGPT.Foundations.Schemes.PositiveProjectiveCechInputs
import SGPT.Foundations.Schemes.NativeGeneratedProjectionFormula
import SGPT.Foundations.Schemes.NativeProjectivePowerCoordinateFrames

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (K : Type) [Field K] (N : ℕ) {Y : Scheme}
    (f : Y ⟶ polynomialProj K N) (L : IntrinsicLineBundle Y) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual positivity powers and the genuine pullback-power comparison retain
literal B_m=(L^q)^m, without replacing it by a different degree object. -/
def nativePositiveProjectiveIteratedPowerPullbackIso (m : ℕ) :
    bundleTensorPower (bundleTensorPower L.sheaf q) m ≅
      (Scheme.Modules.pullback f).obj
        (bundleTensorPower (polynomialProjTwistingLine K N).sheaf m) :=
  nativeLineTensorPowerIso e m ≪≫ (nativePolynomialPullbackPowerIso K N f m).symm

/-- Actual global positive power coordinates, transported to the literal original power. -/
def nativePositiveProjectiveIteratedPowerCoordinateHom (m : ℕ) (i : Fin (N + 1)) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ bundleTensorPower (bundleTensorPower L.sheaf q) m :=
  nativePullbackGlobalHom f (nativePolynomialPowerCoordinateHom K N m i) ≫
    (nativePositiveProjectiveIteratedPowerPullbackIso K N f L q e m).inv

/-- These produced global coordinates are actual generators on their genuine covering opens. -/
theorem nativePositiveProjectiveIteratedPowerCoordinateHom_over_isIso
    (m : ℕ) (i : Fin (N + 1)) :
    IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf
      (actualPolynomialProjectivePullbackCoordinateOpens f i)).map
        (nativePositiveProjectiveIteratedPowerCoordinateHom K N f L q e m i)) := by
  change IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf
    (f ⁻¹ᵁ polynomialProjCoordinateOpen K N i)).map
      (nativePositiveProjectiveIteratedPowerCoordinateHom K N f L q e m i))
  have hcoord : IsIso ((Scheme.Modules.restrictFunctor
      (polynomialProjCoordinateOpen K N i).ι).map (nativePolynomialPowerCoordinateHom K N m i)) :=
    (nativeModuleHom_over_isIso_iff_restrict _ _).mp inferInstance
  have hpull := nativePullbackGlobalHom_restrict_isIso f
    (nativePolynomialPowerCoordinateHom K N m i) (polynomialProjCoordinateOpen K N i)
  have hglobal : IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf
      (f ⁻¹ᵁ polynomialProjCoordinateOpen K N i)).map
        (nativePullbackGlobalHom f (nativePolynomialPowerCoordinateHom K N m i))) :=
    (nativeModuleHom_over_isIso_iff_restrict _ _).mpr hpull
  dsimp [nativePositiveProjectiveIteratedPowerCoordinateHom]
  rw [Functor.map_comp]
  infer_instance

include e in
/-- Actual positive coordinate generators PRODUCE invertibility of the
CANONICAL projection map for literal iterated powers, including m=0. -/
theorem nativePositiveProjectiveIteratedPowerProjectionMap_isIso
    {Z : Scheme} (g : Z ⟶ Y) (m : ℕ) (M : Z.Modules) :
    IsIso (nativeSchemeProjectionMap g (bundleTensorPower (bundleTensorPower L.sheaf q) m) M) :=
  nativeGeneratedLineProjectionMap_isIso g
    (nativePositiveProjectiveIteratedPowerCoordinateHom K N f L q e m)
    (actualPolynomialProjectivePullbackCoordinateOpens f)
    (nativePolynomialPullbackAtlas K N f).covers
    (nativePositiveProjectiveIteratedPowerCoordinateHom_over_isIso K N f L q e m) M

/-- Canonical projection followed by the genuine right unit is the actual
geometric restriction isomorphism, for every true scheme morphism g. -/
def nativePositiveProjectiveIteratedPowerRestrictionIso
    {Z : Scheme} (g : Z ⟶ Y) (m : ℕ) :
    bundleTensor (bundleTensorPower (bundleTensorPower L.sheaf q) m)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj (bundleTensorPower (bundleTensorPower L.sheaf q) m)) := by
  let B := bundleTensorPower (bundleTensorPower L.sheaf q) m
  let : IsIso (nativeSchemeProjectionMap g B (SheafOfModules.unit Z.ringCatSheaf)) :=
    nativePositiveProjectiveIteratedPowerProjectionMap_isIso K N f L q e g m _
  exact asIso (nativeSchemeProjectionMap g B (SheafOfModules.unit Z.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward g).mapIso
      (bundleTensorRightUnitIso ((Scheme.Modules.pullback g).obj B))

/-- The actual restriction isomorphism sends t tensor1 to the ACTUAL
pullback-adjunction unit section, with the literal original native maps. -/
theorem nativePositiveProjectiveIteratedPowerRestrictionIso_tensorUnit
    {Z : Scheme} (g : Z ⟶ Y) (m : ℕ) (U : Y.Opens)
    (t : bundleSections (bundleTensorPower (bundleTensorPower L.sheaf q) m) U) :
    (nativePositiveProjectiveIteratedPowerRestrictionIso K N f L q e g m).hom.val.app (op U)
      (tensorSection (bundleTensorPower (bundleTensorPower L.sheaf q) m)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) U t
          (show bundleSections ((Scheme.Modules.pushforward g).obj
            (SheafOfModules.unit Z.ringCatSheaf)) U from (1 : Γ(Z, g ⁻¹ᵁ U)))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (bundleTensorPower (bundleTensorPower L.sheaf q) m)).val.app (op U) t) := by
  let B := bundleTensorPower (bundleTensorPower L.sheaf q) m
  change (bundleTensorRightUnitIso ((Scheme.Modules.pullback g).obj B)).hom.val.app
    (op (g ⁻¹ᵁ U))
      ((nativeSchemeProjectionMap g B (SheafOfModules.unit Z.ringCatSheaf)).val.app (op U)
        (tensorSection B ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf))
          U t (show bundleSections ((Scheme.Modules.pushforward g).obj
            (SheafOfModules.unit Z.ringCatSheaf)) U from (1 : Γ(Z, g ⁻¹ᵁ U))))) = _
  rw [nativeSchemeProjectionMap_tensorSection, nativeBundleTensorRightUnitIso_tensorSection, one_smul]

/-- The ORIGINAL zero-section tensor quotient morphism is identified with
actual geometric adjunction-unit restriction as a full sheaf map. -/
theorem nativePositiveProjectiveSectionZeroTensorRestriction_comp
    (s : bundlePowerGlobalSections L.sheaf q) (m : ℕ) :
    sectionZeroTensorRestriction (L.atlas.tensorPower q) s
        (bundleTensorPower (bundleTensorPower L.sheaf q) m) ≫
      (nativePositiveProjectiveIteratedPowerRestrictionIso K N f L q e
        (sectionZeroι (L.atlas.tensorPower q) s) m).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction
      (sectionZeroι (L.atlas.tensorPower q) s)).unit.app
        (bundleTensorPower (bundleTensorPower L.sheaf q) m) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (nativePositiveProjectiveIteratedPowerRestrictionIso K N f L q e
      (sectionZeroι (L.atlas.tensorPower q) s) m).hom.val.app U
    ((sectionZeroTensorRestriction (L.atlas.tensorPower q) s
      (bundleTensorPower (bundleTensorPower L.sheaf q) m)).app U.unop t) = _
  rw [sectionZeroTensorRestriction_app]
  exact nativePositiveProjectiveIteratedPowerRestrictionIso_tensorUnit K N f L q e _ m U.unop t

end
end SGPT.Foundations.Schemes
