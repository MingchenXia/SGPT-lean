import SGPT.Foundations.Schemes.NativeProjectivePowerCoordinateFrames
/-!
# NativeGeneratorPullbackTransitions

Actual locally invertible generators and the genuine adjunction-unit square identify real pulled-back frame transition units with their structural pullbacks.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X Y : Scheme.{u}}

/-- Genuine local invertibility supplies the actual pulled-back generator frame. -/
instance nativePullbackGlobalHom_over_isIso (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)] :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).map
      (nativePullbackGlobalHom f α)) := by
  have := (nativeModuleHom_over_isIso_iff_restrict α U).mp inferInstance
  have := nativePullbackGlobalHom_restrict_isIso f α U
  exact (nativeModuleHom_over_isIso_iff_restrict _ _).mpr inferInstance

/-- The real generator has actual coefficient one on every smaller generating open. -/
theorem nativeGlobalGeneratorFrame_hom_one {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)]
    {W : Y.Opens} (h : W ⟶ U) :
    (nativeGlobalGeneratorFrame α U).coefficients h
      (α.val.app (.op W) (1 : Γ(Y, W))) = 1 := by
  exact congrArg (fun a ↦ a.val.app (.op (Over.mk h)) (1 : Γ(Y, W)))
    (nativeGlobalGeneratorFrame α U).inv_hom_id

/-- The actual pulled-back generator transitions are precisely structural pullbacks of the original regular transition units. -/
theorem nativePullbackGeneratorFrame_transition (f : X ⟶ Y) {L : Y.Modules}
    (α β : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U V : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)]
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf V).map β)]
    (W : Y.Opens) (h : W ⟶ U) (k : W ⟶ V) :
    (localBundleFrameTransition (nativePullbackGeneratorFrame f α U)
      (nativePullbackGeneratorFrame f β V) ((Opens.map f.base).map h)
        ((Opens.map f.base).map k) : X.sheaf.obj.obj (.op (f ⁻¹ᵁ W))) =
      f.app W (localBundleFrameTransition (nativeGlobalGeneratorFrame α U)
        (nativeGlobalGeneratorFrame β V) h k : Y.sheaf.obj.obj (.op W)) := by
  let s : bundleSections L W := α.val.app (.op W) (1 : Γ(Y, W))
  let t := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s
  have ha := nativeGeneratorPullback_coefficient_square f α U W h s
  have hb := nativeGeneratorPullback_coefficient_square f β V W k s
  have hs : (nativeGlobalGeneratorFrame α U).coefficients h s = 1 :=
    nativeGlobalGeneratorFrame_hom_one α U h
  have ht := localBundleFrameTransition_coefficients
    (nativePullbackGeneratorFrame f α U) (nativePullbackGeneratorFrame f β V)
    ((Opens.map f.base).map h) ((Opens.map f.base).map k) t
  change (nativePullbackGeneratorFrame f α U).coefficients
    ((Opens.map f.base).map h) t = f.app W ((nativeGlobalGeneratorFrame α U).coefficients h s) at ha
  change (nativePullbackGeneratorFrame f β V).coefficients
    ((Opens.map f.base).map k) t = f.app W ((nativeGlobalGeneratorFrame β V).coefficients k s) at hb
  rw [hs, map_one] at ha
  rw [ha, mul_one] at ht
  have hr := localBundleFrameTransition_coefficients
    (nativeGlobalGeneratorFrame α U) (nativeGlobalGeneratorFrame β V) h k s
  rw [hs, mul_one] at hr
  exact ht.symm.trans (hb.trans (congrArg (f.app W) hr))

end
end SGPT.Foundations.Schemes
