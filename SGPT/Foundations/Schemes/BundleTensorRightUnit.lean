import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

local instance bundleTensorRightUnitPresheafMonoidalCategory {X : Scheme.{u}} : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)

/-- Sheafification of the true presheaf right unitor gives the actual tensor unit iso. -/
def bundleTensorRightUnitIso {X : Scheme.{u}} (P : X.Modules) :
    bundleTensor P (SheafOfModules.unit X.ringCatSheaf) ≅ P :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.rightUnitor P.val) ≪≫ bundleSheafificationIso P

/-- The genuine right unit sends literal pure sections to the original scalar product. -/
theorem nativeBundleTensorRightUnitIso_tensorSection {X : Scheme.{u}}
    (P : X.Modules) (U : X.Opens) (s : bundleSections P U) (r : Γ(X, U)) :
    (bundleTensorRightUnitIso P).hom.val.app (op U)
      (tensorSection P (SheafOfModules.unit X.ringCatSheaf) U s r) = r • s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he := (adj.homEquiv (bundleTensorPresheaf P (SheafOfModules.unit X.ringCatSheaf))
    P).apply_symm_apply (MonoidalCategory.rightUnitor P.val).hom
  have hs := congrArg (fun α ↦ (α.app (op U)).hom (s ⊗ₜ[Γ(X, U)] r)) he
  change (bundleTensorRightUnitIso P).hom.val.app (op U)
    (tensorSection P (SheafOfModules.unit X.ringCatSheaf) U s r) =
      (MonoidalCategory.rightUnitor (ModuleCat.of Γ(X, U) (bundleSections P U))).hom
        (s ⊗ₜ[Γ(X, U)] r) at hs
  exact hs.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply (R := Γ(X, U)) s r)


end
end SGPT.Foundations.Schemes
