import SGPT.Foundations.Schemes.NativeLineProjectionFormula
import SGPT.Foundations.Schemes.NativeLinePullbackFrames
import SGPT.Foundations.Schemes.BundleMorphismGluing

/-! # Actual local tensor coefficients for native pushforward

A genuine source line frame on the literal inverse-image open gives a
native target coefficient isomorphism. The scalar action uses the actual
scheme structure map; the restrictions use the actual inverse-image functor.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{u}}

/-- True inverse-image tensor coefficients, with the literal ambient
regular-ring action through the actual scheme map. -/
def nativeSchemePushforwardTensorFrameSectionEquiv (f : X ⟶ Y) (P M : X.Modules)
    {U W : Y.Opens} (e : LocalBundleFrame P (f ⁻¹ᵁ U)) (h : W ⟶ U) :
    bundleSections ((Scheme.Modules.pushforward f).obj (bundleTensor P M)) W ≃ₗ[Γ(Y, W)]
      bundleSections ((Scheme.Modules.pushforward f).obj M) W where
  toFun s := e.tensorModuleCoefficients M ((Opens.map f.base).map h) s
  invFun s := (e.tensorModuleCoefficients M ((Opens.map f.base).map h)).symm s
  left_inv s := (e.tensorModuleCoefficients M ((Opens.map f.base).map h)).symm_apply_apply s
  right_inv s := (e.tensorModuleCoefficients M ((Opens.map f.base).map h)).apply_symm_apply s
  map_add' s t := (e.tensorModuleCoefficients M ((Opens.map f.base).map h)).map_add s t
  map_smul' r s := by
    change e.tensorModuleCoefficients M ((Opens.map f.base).map h)
        ((f.app W).hom r • (show bundleSections (bundleTensor P M) (f ⁻¹ᵁ W) from s)) =
      (f.app W).hom r • (show bundleSections M (f ⁻¹ᵁ W) from
        e.tensorModuleCoefficients M ((Opens.map f.base).map h) s)
    exact (e.tensorModuleCoefficients M ((Opens.map f.base).map h)).map_smul ((f.app W).hom r) s

/-- These actual ambient-linear coefficient maps commute with every
genuine subordinate restriction. -/
theorem nativeSchemePushforwardTensorFrameSectionEquiv_restrict (f : X ⟶ Y) (P M : X.Modules)
    {U W V : Y.Opens} (e : LocalBundleFrame P (f ⁻¹ᵁ U)) (h : W ⟶ U) (j : V ⟶ W)
    (s : bundleSections ((Scheme.Modules.pushforward f).obj (bundleTensor P M)) W) :
    nativeSchemePushforwardTensorFrameSectionEquiv f P M e (j ≫ h)
        (((Scheme.Modules.pushforward f).obj (bundleTensor P M)).val.map j.op s) =
      ((Scheme.Modules.pushforward f).obj M).val.map j.op
        (nativeSchemePushforwardTensorFrameSectionEquiv f P M e h s) := by
  change e.tensorModuleCoefficients M ((Opens.map f.base).map (j ≫ h))
      ((bundleTensor P M).val.map ((Opens.map f.base).map j).op s) =
    M.val.map ((Opens.map f.base).map j).op
      (e.tensorModuleCoefficients M ((Opens.map f.base).map h) s)
  rw [Functor.map_comp]
  exact e.tensorModuleCoefficients_restrict M _ _ s

/-- A genuine source tensor frame descends to the actual native
pushforward over-site, retaining the literal ambient scalar action. -/
def nativeSchemePushforwardTensorFrameIso (f : X ⟶ Y) (P M : X.Modules)
    {U : Y.Opens} (e : LocalBundleFrame P (f ⁻¹ᵁ U)) :
    ((Scheme.Modules.pushforward f).obj (bundleTensor P M)).over U ≅
      ((Scheme.Modules.pushforward f).obj M).over U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun W ↦ (nativeSchemePushforwardTensorFrameSectionEquiv f P M e W.unop.hom).toModuleIso)
      (fun {V W} j ↦ by
        apply ModuleCat.hom_ext
        ext s
        change nativeSchemePushforwardTensorFrameSectionEquiv f P M e W.unop.hom
            (((Scheme.Modules.pushforward f).obj (bundleTensor P M)).val.map j.unop.left.op s) =
          ((Scheme.Modules.pushforward f).obj M).val.map j.unop.left.op
            (nativeSchemePushforwardTensorFrameSectionEquiv f P M e V.unop.hom s)
        have hh : W.unop.hom = j.unop.left ≫ V.unop.hom := Subsingleton.elim _ _
        rw [hh]
        exact nativeSchemePushforwardTensorFrameSectionEquiv_restrict f P M e _ _ s))

/-- The actual local comparison obtained from the two genuine tensor frames. -/
def nativeSchemeLineProjectionLocalIso (f : X ⟶ Y) {L : Y.Modules} (P M : X.Modules)
    {U : Y.Opens} (e : LocalBundleFrame L U) (eP : LocalBundleFrame P (f ⁻¹ᵁ U)) :
    (bundleTensor L ((Scheme.Modules.pushforward f).obj M)).over U ≅
      ((Scheme.Modules.pushforward f).obj (bundleTensor P M)).over U :=
  e.tensorModule ((Scheme.Modules.pushforward f).obj M) ≪≫
    (nativeSchemePushforwardTensorFrameIso f P M eP).symm

/-- The true sheafification adjoint of a genuine pushforward sheaf map
has its literal actual pure-tensor formula. -/
theorem nativeSchemeTensorPushforwardMap_tensorSection (f : X ⟶ Y) (L : Y.Modules) (P M : X.Modules)
    (η : L ⟶ (Scheme.Modules.pushforward f).obj P) (W : Y.Opens)
    (s : bundleSections L W) (t : bundleSections ((Scheme.Modules.pushforward f).obj M) W) :
    (nativeSchemeTensorPushforwardMap f L P M η).val.app (op W)
        (tensorSection L ((Scheme.Modules.pushforward f).obj M) W s t) =
      tensorSection P M (f ⁻¹ᵁ W) (η.val.app (op W) s) t := by
  have hu : (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (bundleTensorPresheaf L ((Scheme.Modules.pushforward f).obj M)) ≫
      (nativeSchemeTensorPushforwardMap f L P M η).val =
      nativeSchemeTensorPushforwardPresheafMap f L P M η :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).apply_symm_apply _
  exact congrArg (fun α ↦ (α.app (op W)).hom (s ⊗ₜ[Γ(Y, W)] t)) hu

/-- A genuine coefficient square identifies the actual local tensor
isomorphism with the actual sheafified tensor map. -/
theorem nativeSchemeLineProjectionLocalIso_hom (f : X ⟶ Y) {L : Y.Modules} (P M : X.Modules)
    (η : L ⟶ (Scheme.Modules.pushforward f).obj P) {U : Y.Opens}
    (e : LocalBundleFrame L U) (eP : LocalBundleFrame P (f ⁻¹ᵁ U))
    (hu : ∀ (W : Y.Opens) (h : W ⟶ U) (s : bundleSections L W),
      eP.coefficients ((Opens.map f.base).map h) (η.val.app (op W) s) =
        f.app W (e.coefficients h s)) :
    (nativeSchemeLineProjectionLocalIso f P M e eP).hom =
      (SheafOfModules.overFunctor Y.ringCatSheaf U).map (nativeSchemeTensorPushforwardMap f L P M η) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  let C := e.tensorModuleCoefficients ((Scheme.Modules.pushforward f).obj M) W.unop.hom
  let D := nativeSchemePushforwardTensorFrameSectionEquiv f P M eP W.unop.hom
  apply D.injective
  have hl : D ((nativeSchemeLineProjectionLocalIso f P M e eP).hom.val.app W x) = C x := by
    change D (D.symm (C x)) = C x
    exact D.apply_symm_apply _
  refine hl.trans ?_
  symm
  change D ((nativeSchemeTensorPushforwardMap f L P M η).val.app (op W.unop.left) x) = C x
  have hx := e.tensorModuleCoefficients_reconstruct ((Scheme.Modules.pushforward f).obj M) W.unop.hom x
  conv_lhs => rw [← hx, nativeSchemeTensorPushforwardMap_tensorSection]
  change eP.tensorModuleCoefficients M ((Opens.map f.base).map W.unop.hom)
    (tensorSection P M (f ⁻¹ᵁ W.unop.left)
      (η.val.app (op W.unop.left) ((e.coefficients W.unop.hom).symm 1)) (C x)) = C x
  rw [LocalBundleFrame.tensorModuleCoefficients_tmul, hu, LinearEquiv.apply_symm_apply, map_one, one_smul]

end

end SGPT.Foundations.Schemes
