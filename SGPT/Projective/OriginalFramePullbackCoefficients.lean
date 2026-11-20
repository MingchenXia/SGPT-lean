import SGPT.Projective.OriginalLinePullbackMate

/-! Actual original global frame scalar readers under genuine module
pullback. Blueprint: original-frame-pullback-coefficients.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {L : Y.Modules}

/-- Pull back the ACTUAL original frame, retaining the actual module-sheaf
pullback and genuine structural unit isomorphism. -/
def globalFramePullback (e : L ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj L ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ nativeSchemePullbackUnitIso f

/-- The genuine frame coefficient square commutes with the ACTUAL
original adjunction unit, proved by its naturality and true unit mate. -/
theorem globalFramePullback_unit (e : L ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L ≫
      (Scheme.Modules.pushforward f).map (globalFramePullback f e).hom =
        e.hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (nativeSchemePullbackUnitIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _
      (nativeSchemePullbackUnitIso f).hom).symm.trans (nativeSchemePullbackUnitIso_mate f)
  change _ ≫ (Scheme.Modules.pushforward f).map
    ((Scheme.Modules.pullback f).map e.hom ≫ (nativeSchemePullbackUnitIso f).hom) = _
  rw [Functor.map_comp, ← Category.assoc]
  have hn : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map e.hom) =
      e.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality e.hom).symm
  exact (congrArg (fun γ => γ ≫ (Scheme.Modules.pushforward f).map
    (nativeSchemePullbackUnitIso f).hom) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun γ => e.hom ≫ γ) hu))

/-- EVERY actual original section on EVERY actual original open retains
its SAME actual original frame coefficient under the true pullback. -/
theorem globalFramePullback_coefficient (e : L ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (s : Γ(L, U)) :
    (globalFramePullback f e).hom.val.app (.op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op U) s) =
        f.app U (e.hom.val.app (.op U) s) := by
  exact congrArg (fun γ => γ.val.app (.op U) s) (globalFramePullback_unit f e)

/-- The actual original restricted frame has its original coefficient on
EVERY original open of the genuine original open subscheme. -/
theorem nativeRestriction_frame_coefficient {U : Y.Opens} (α : LocalBundleFrame L U)
    (V : U.toScheme.Opens) (j : U.ι ''ᵁ V ⟶ U)
    (s : Γ(L.restrict U.ι, V)) :
    α.nativeRestriction.hom.val.app (.op V) s =
      (U.ι.appIso V).hom (α.coefficients j s) := by
  rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
