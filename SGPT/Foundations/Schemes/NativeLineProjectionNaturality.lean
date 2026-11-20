import SGPT.Foundations.Schemes.NativeGeneratedProjectionFormula
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison

/-!
# Naturality of the literal projection map

The canonical tensor projection map commutes with an actual isomorphism of
its target-scheme module sheaf. The equality is proved before invertibility
of the projection maps is used.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{u}}

/-- The literal projection morphism commutes with any actual isomorphism
of target-scheme module sheaves, before either projection map is inverted. -/
theorem nativeSchemeProjectionMap_naturality (f : X ⟶ Y) {P Q : Y.Modules}
    (E : P ≅ Q) (M : X.Modules) :
    (bundleTensorIso E (Iso.refl ((Scheme.Modules.pushforward f).obj M))).hom ≫
        nativeSchemeProjectionMap f Q M =
      nativeSchemeProjectionMap f P M ≫ (Scheme.Modules.pushforward f).map
        (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  apply (adj.homEquiv (bundleTensorPresheaf P ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pushforward f).obj (bundleTensor ((Scheme.Modules.pullback f).obj Q) M))).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change (nativeSchemeProjectionMap f Q M).val.app U
      ((bundleTensorIso E (Iso.refl ((Scheme.Modules.pushforward f).obj M))).hom.val.app U
        (tensorSection P ((Scheme.Modules.pushforward f).obj M) U.unop s t)) =
    (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)).hom.val.app
      (.op (f ⁻¹ᵁ U.unop))
      ((nativeSchemeProjectionMap f P M).val.app U
        (tensorSection P ((Scheme.Modules.pushforward f).obj M) U.unop s t))
  rw [nativeBundleTensorIso_tensorSection, nativeSchemeProjectionMap_tensorSection,
    nativeSchemeProjectionMap_tensorSection, nativeBundleTensorIso_tensorSection]
  have hu := congrArg (fun a ↦ a.val.app U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality E.hom)
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Q).val.app U
      (E.hom.val.app U s) =
    ((Scheme.Modules.pullback f).map E.hom).val.app (.op (f ⁻¹ᵁ U.unop))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app U s) at hu
  exact congrArg (fun z ↦ tensorSection ((Scheme.Modules.pullback f).obj Q) M
    (f ⁻¹ᵁ U.unop) z t) hu

/-- If the genuine projection maps are invertible, their actual
isomorphisms satisfy the same naturality square. -/
theorem nativeSchemeProjectionIso_naturality (f : X ⟶ Y) {P Q : Y.Modules}
    (E : P ≅ Q) (M : X.Modules)
    [IsIso (nativeSchemeProjectionMap f P M)] [IsIso (nativeSchemeProjectionMap f Q M)] :
    bundleTensorIso E (Iso.refl ((Scheme.Modules.pushforward f).obj M)) ≪≫
        asIso (nativeSchemeProjectionMap f Q M) =
      asIso (nativeSchemeProjectionMap f P M) ≪≫
        (Scheme.Modules.pushforward f).mapIso
          (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)) := by
  apply Iso.ext
  exact nativeSchemeProjectionMap_naturality f E M

/-- The inverse projection comparison commutes with the same given
isomorphism, retaining the literal pullback and pushforward maps. -/
theorem nativeSchemeProjectionIso_inv_naturality (f : X ⟶ Y) {P Q : Y.Modules}
    (E : P ≅ Q) (M : X.Modules)
    [IsIso (nativeSchemeProjectionMap f P M)] [IsIso (nativeSchemeProjectionMap f Q M)] :
    (Scheme.Modules.pushforward f).mapIso
        (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)) ≪≫
        (asIso (nativeSchemeProjectionMap f Q M)).symm =
      (asIso (nativeSchemeProjectionMap f P M)).symm ≪≫
        bundleTensorIso E (Iso.refl ((Scheme.Modules.pushforward f).obj M)) := by
  apply Iso.ext
  apply (cancel_mono (nativeSchemeProjectionMap f Q M)).mp
  change ((Scheme.Modules.pushforward f).map
      (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)).hom ≫
      (asIso (nativeSchemeProjectionMap f Q M)).inv) ≫ nativeSchemeProjectionMap f Q M =
    ((asIso (nativeSchemeProjectionMap f P M)).inv ≫
      (bundleTensorIso E (Iso.refl ((Scheme.Modules.pushforward f).obj M))).hom) ≫
      nativeSchemeProjectionMap f Q M
  have hQ : (asIso (nativeSchemeProjectionMap f Q M)).inv ≫
      nativeSchemeProjectionMap f Q M = 𝟙 _ := (asIso (nativeSchemeProjectionMap f Q M)).inv_hom_id
  have hP : (asIso (nativeSchemeProjectionMap f P M)).inv ≫
      nativeSchemeProjectionMap f P M = 𝟙 _ := (asIso (nativeSchemeProjectionMap f P M)).inv_hom_id
  rw [Category.assoc, hQ, Category.comp_id,
    Category.assoc, nativeSchemeProjectionMap_naturality, ← Category.assoc,
    hP, Category.id_comp]

end
end SGPT.Foundations.Schemes
