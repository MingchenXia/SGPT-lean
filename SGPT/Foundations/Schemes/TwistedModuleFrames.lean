import SGPT.Foundations.Schemes.LineBundleSectionRing

/-! # Genuine local frames for twisting arbitrary sheaf modules

An actual local line frame identifies the sheafified tensor with any actual
module sheaf.  Pure tensors, restriction, and changes of frame retain their
actual scalar actions.  These maps supply the twisting step for projective
section extension without assuming that the module has a graded presentation.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}}

local instance (U : X.Opens) :
    MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
  PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ X.sheaf.obj)

/-- The actual presheaf tensor coefficient map from a genuine line frame. -/
def tensorModuleFramePresheafIso {T : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) :
    bundlePresheafOver (bundleTensorPresheaf T M) U ≅ (M.over U).val :=
  bundleOverTensorPresheafIso T M U ≪≫
    MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e) (Iso.refl _) ≪≫
    MonoidalCategory.leftUnitor (M.over U).val

/-- A true line frame trivializes twisting of an arbitrary actual sheaf module. -/
def LocalBundleFrame.tensorModule {T : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) :
    (bundleTensor T M).over U ≅ M.over U :=
  bundleOverSheafificationIso (bundleTensorPresheaf T M) U ≪≫
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (tensorModuleFramePresheafIso e M) ≪≫ bundleOverCounitIso U (M.over U)

/-- Its forward map is the genuine sheafification adjoint of the tensor coefficient map. -/
theorem LocalBundleFrame.tensorModule_hom {T : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) :
    (e.tensorModule M).hom =
      (bundleOverSheafificationIso (bundleTensorPresheaf T M) U).hom ≫
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
        (tensorModuleFramePresheafIso e M).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app (M.over U) := by
  unfold LocalBundleFrame.tensorModule
  simp only [Iso.trans_hom, Functor.mapIso_hom, bundleOverCounitIso_hom]

/-- Applying the actual twisted-module frame to the tensor sheafification unit
recovers the literal presheaf tensor coefficient map. -/
theorem LocalBundleFrame.tensorModule_unit {T : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) :
    bundleSheafificationOverMap (bundleTensorPresheaf T M) U ≫
        (e.tensorModule M).hom.val = (tensorModuleFramePresheafIso e M).hom := by
  rw [LocalBundleFrame.tensorModule_hom]
  simp only [SheafOfModules.comp_val]
  rw [← Category.assoc, ← Category.assoc, bundleOverSheafificationIso_unit, Category.assoc]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
      (bundlePresheafOver (bundleTensorPresheaf T M) U) (M.over U)
      |>.apply_symm_apply (tensorModuleFramePresheafIso e M).hom

/-- The native section equivalence supplied by the true twisted-module frame. -/
def LocalBundleFrame.tensorModuleCoefficients {T : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) (i : V ⟶ U) :
    bundleSections (bundleTensor T M) V ≃ₗ[Γ(X, V)] bundleSections M V :=
  ((SheafOfModules.evaluation (R := X.ringCatSheaf.over U) (op (Over.mk i))).mapIso
    (e.tensorModule M)).toLinearEquiv

/-- Literal pure tensors have their literal scalar-multiple coefficients. -/
theorem tensorModuleFramePresheafIso_tmul {T : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) (i : V ⟶ U)
    (s : bundleSections T V) (t : bundleSections M V) :
    ((tensorModuleFramePresheafIso e M).hom.app (op (Over.mk i))).hom
      (s ⊗ₜ[Γ(X, V)] t) = e.coefficients i s • t := by
  change (MonoidalCategory.leftUnitor
    (ModuleCat.of Γ(X, V) (bundleSections M V))).hom
      (e.coefficients i s ⊗ₜ[Γ(X, V)] t) = _
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]

/-- The true sheafified pure tensor keeps that actual scalar-multiple coefficient. -/
theorem LocalBundleFrame.tensorModuleCoefficients_tmul {T : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) (i : V ⟶ U)
    (s : bundleSections T V) (t : bundleSections M V) :
    e.tensorModuleCoefficients M i (tensorSection T M V s t) = e.coefficients i s • t := by
  have h := congrArg (fun q => (q.app (op (Over.mk i))).hom (s ⊗ₜ[Γ(X, V)] t))
    (e.tensorModule_unit M)
  exact h.trans (tensorModuleFramePresheafIso_tmul e M i s t)

/-- True twisted-module coefficients commute with actual sheaf restrictions. -/
theorem LocalBundleFrame.tensorModuleCoefficients_restrict {T : X.Modules}
    {U V W : X.Opens} (e : LocalBundleFrame T U) (M : X.Modules)
    (i : V ⟶ U) (j : W ⟶ V) (s : bundleSections (bundleTensor T M) V) :
    e.tensorModuleCoefficients M (j ≫ i) ((bundleTensor T M).val.map j.op s) =
      M.val.map j.op (e.tensorModuleCoefficients M i s) :=
  PresheafOfModules.naturality_apply (e.tensorModule M).hom.val
    (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op s

/-- Every actual twisted section is the pure tensor of the genuine unit frame
section with its actual module coefficient. -/
theorem LocalBundleFrame.tensorModuleCoefficients_reconstruct {T : X.Modules}
    {U V : X.Opens} (e : LocalBundleFrame T U) (M : X.Modules) (i : V ⟶ U)
    (s : bundleSections (bundleTensor T M) V) :
    tensorSection T M V ((e.coefficients i).symm 1)
      (e.tensorModuleCoefficients M i s) = s := by
  apply (e.tensorModuleCoefficients M i).injective
  rw [LocalBundleFrame.tensorModuleCoefficients_tmul, LinearEquiv.apply_symm_apply, one_smul]

/-- Changes of genuine line frame act on actual twisted-module coefficients
by the actual transition unit. -/
theorem LocalBundleFrame.tensorModuleCoefficients_transition {T : X.Modules}
    {U V W : X.Opens} (e : LocalBundleFrame T U) (f : LocalBundleFrame T V)
    (M : X.Modules) (i : W ⟶ U) (j : W ⟶ V)
    (s : bundleSections (bundleTensor T M) W) :
    f.tensorModuleCoefficients M j s =
      (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) •
        e.tensorModuleCoefficients M i s := by
  conv_lhs => rw [← e.tensorModuleCoefficients_reconstruct M i s]
  rw [LocalBundleFrame.tensorModuleCoefficients_tmul,
    localBundleFrameTransition_coefficients, LinearEquiv.apply_symm_apply, mul_one]

end

end SGPT.Foundations.Schemes
