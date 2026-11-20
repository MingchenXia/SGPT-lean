import SGPT.Foundations.Schemes.TwistedModuleFrames
import SGPT.Foundations.Schemes.ModulePushforwardRestriction

/-! # The canonical native sheaf projection map

The literal pullback-adjunction unit and the actual tensor-section map
produce the native projection morphism after genuine sheafification.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{u}}

/-- An actual sheaf map to a native pushforward supplies the literal
balanced tensor map, with all structural scalar actions retained. -/
def nativeSchemeTensorPushforwardBilinear (f : X ⟶ Y) (L : Y.Modules) (P M : X.Modules)
    (η : L ⟶ (Scheme.Modules.pushforward f).obj P)
    (U : Y.Opens) :
    bundleSections L U →ₗ[Γ(Y, U)]
      bundleSections ((Scheme.Modules.pushforward f).obj M) U →ₗ[Γ(Y, U)]
        bundleSections ((Scheme.Modules.pushforward f).obj
          (bundleTensor P M)) U where
  toFun s :=
    { toFun t := tensorSection P M (f ⁻¹ᵁ U) (η.val.app (op U) s) t
      map_add' t t' := tensorSection_add_right P M (f ⁻¹ᵁ U) (η.val.app (op U) s) t t'
      map_smul' r t := by
        change tensorSection P M (f ⁻¹ᵁ U) (η.val.app (op U) s)
            ((f.app U).hom r • (show bundleSections M (f ⁻¹ᵁ U) from t)) =
          (f.app U).hom r • tensorSection P M (f ⁻¹ᵁ U) (η.val.app (op U) s)
            (show bundleSections M (f ⁻¹ᵁ U) from t)
        exact tensorSection_smul_right P M (f ⁻¹ᵁ U) ((f.app U).hom r) (η.val.app (op U) s) t }
  map_add' s s' := by
    ext t
    dsimp only
    rw [map_add]
    exact tensorSection_add_left P M (f ⁻¹ᵁ U) (η.val.app (op U) s) (η.val.app (op U) s') t
  map_smul' r s := by
    ext t
    change tensorSection P M (f ⁻¹ᵁ U)
        ((η.val.app (op U)).hom (r • s)) t =
      (f.app U).hom r • tensorSection P M (f ⁻¹ᵁ U) (η.val.app (op U) s) t
    have hη := (η.val.app (op U)).hom.map_smul r s
    change (η.val.app (op U)).hom (r • s) =
      (f.app U).hom r • (show bundleSections P (f ⁻¹ᵁ U) from η.val.app (op U) s) at hη
    rw [hη]
    exact tensorSection_smul_left P M (f ⁻¹ᵁ U) ((f.app U).hom r) (η.val.app (op U) s) t

/-- The actual objectwise tensor presheaf maps to the native pushforward
of the actual pulled-back tensor sheaf. -/
def nativeSchemeTensorPushforwardPresheafMap (f : X ⟶ Y) (L : Y.Modules) (P M : X.Modules)
    (η : L ⟶ (Scheme.Modules.pushforward f).obj P) :
    bundleTensorPresheaf L ((Scheme.Modules.pushforward f).obj M) ⟶
      ((Scheme.Modules.pushforward f).obj (bundleTensor P M)).val where
  app U := ModuleCat.ofHom (Y := bundleSections ((Scheme.Modules.pushforward f).obj (bundleTensor P M)) U.unop)
    (TensorProduct.lift (nativeSchemeTensorPushforwardBilinear f L P M η U.unop))
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    change tensorSection P M (f ⁻¹ᵁ V.unop)
        (η.val.app V (L.val.map i s)) (M.val.map ((Opens.map f.base).map i.unop).op t) =
      (bundleTensor P M).val.map
        ((Opens.map f.base).map i.unop).op
          (tensorSection P M (f ⁻¹ᵁ U.unop)
            (η.val.app U s) t)
    rw [tensorSection_restrict]
    exact congrArg (fun z ↦ tensorSection P M (f ⁻¹ᵁ V.unop) z
      (M.val.map ((Opens.map f.base).map i.unop).op t))
        (PresheafOfModules.naturality_apply
          η.val i s)

/-- The actual tensor map induced by a genuine sheaf morphism, after the
literal tensor sheafification adjunction. -/
def nativeSchemeTensorPushforwardMap (f : X ⟶ Y) (L : Y.Modules) (P M : X.Modules)
    (η : L ⟶ (Scheme.Modules.pushforward f).obj P) :
    bundleTensor L ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f).obj (bundleTensor P M) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (nativeSchemeTensorPushforwardPresheafMap f L P M η)

/-- The canonical actual projection map, as the true sheafification adjoint. -/
def nativeSchemeProjectionMap (f : X ⟶ Y) (L : Y.Modules) (M : X.Modules) :
    bundleTensor L ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f).obj (bundleTensor ((Scheme.Modules.pullback f).obj L) M) :=
  nativeSchemeTensorPushforwardMap f L ((Scheme.Modules.pullback f).obj L) M
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)

/-- Composing with the literal tensor sheafification unit recovers the
actual objectwise balanced projection map. -/
theorem nativeSchemeProjectionMap_unit (f : X ⟶ Y) (L : Y.Modules) (M : X.Modules) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (bundleTensorPresheaf L ((Scheme.Modules.pushforward f).obj M)) ≫
      (nativeSchemeProjectionMap f L M).val =
      nativeSchemeTensorPushforwardPresheafMap f L ((Scheme.Modules.pullback f).obj L) M
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).apply_symm_apply _

/-- The genuine sheaf projection map has its literal pure-tensor formula. -/
theorem nativeSchemeProjectionMap_tensorSection (f : X ⟶ Y) (L : Y.Modules) (M : X.Modules)
    (U : Y.Opens) (s : bundleSections L U)
    (t : bundleSections ((Scheme.Modules.pushforward f).obj M) U) :
    (nativeSchemeProjectionMap f L M).val.app (op U)
        (tensorSection L ((Scheme.Modules.pushforward f).obj M) U s t) =
      tensorSection ((Scheme.Modules.pullback f).obj L) M (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) s) t := by
  have h := congrArg (fun α ↦ (α.app (op U)).hom (s ⊗ₜ[Γ(Y, U)] t))
    (nativeSchemeProjectionMap_unit f L M)
  exact h

end

end SGPT.Foundations.Schemes
