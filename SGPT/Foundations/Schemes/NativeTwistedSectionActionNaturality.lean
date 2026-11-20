import SGPT.Foundations.Schemes.NativeLinePowerSectionNaturality
import SGPT.Foundations.Schemes.TwistedModuleSectionAction

/-!
# Naturality of the actual twisted section action

The action on an arbitrary actual module sheaf is independent of the line atlas
and commutes with the actual tensor powers of a given line-sheaf isomorphism.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {T : X.Modules}

private theorem top_restrict_comp (P : X.Modules) {V W : X.Opens} (j : V ⟶ W)
    (s : bundleSections P ⊤) :
    P.val.map j.op (P.val.map W.leTop.op s) = P.val.map V.leTop.op s := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- On every subordinate original chart, the actual twisted action has the
literal scalar-times-module coefficient. -/
theorem atlasTwistedGlobalAction_coefficients_subordinate (a : LineBundleAtlas T)
    (M : X.Modules) (d m : ℕ) (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M m) :
    ((a.frame i).tensorPower (d + m)).tensorModuleCoefficients M h
      ((bundleTensor (bundleTensorPower T (d + m)) M).val.map W.leTop.op
        (atlasTwistedGlobalAction a M d m s t)) =
    ((a.frame i).tensorPower d).coefficients h
      ((bundleTensorPower T d).val.map W.leTop.op s) •
    ((a.frame i).tensorPower m).tensorModuleCoefficients M h
      ((bundleTensor (bundleTensorPower T m) M).val.map W.leTop.op t) := by
  have hz := LocalBundleFrame.twisted_global_coefficients_restrict (a.frame i) M
    (d + m) h (atlasTwistedGlobalAction a M d m s t)
  change _ = M.val.map h.op
    (atlasTwistedGlobalCoefficients a M (d + m) i (atlasTwistedGlobalAction a M d m s t)) at hz
  rw [atlasTwistedGlobalAction_coefficients] at hz
  exact hz.trans ((M.val.map_smul h.op _ _).trans
    (congrArg₂ (· • ·)
      (LocalBundleFrame.global_coefficients_restrict (a.frame i) d h s).symm
      (LocalBundleFrame.twisted_global_coefficients_restrict (a.frame i) M m h t).symm))

/-- The actual action coefficient law holds in every genuine local line frame,
independently of the atlas used to construct the global action. -/
theorem atlasTwistedGlobalAction_anyFrame (a : LineBundleAtlas T) (M : X.Modules)
    (d m : ℕ) {U W : X.Opens} (e : LocalBundleFrame T U) (h : W ⟶ U)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M m) :
    (e.tensorPower (d + m)).tensorModuleCoefficients M h
      ((bundleTensor (bundleTensorPower T (d + m)) M).val.map W.leTop.op
        (atlasTwistedGlobalAction a M d m s t)) =
    (e.tensorPower d).coefficients h ((bundleTensorPower T d).val.map W.leTop.op s) •
      (e.tensorPower m).tensorModuleCoefficients M h
        ((bundleTensor (bundleTensorPower T m) M).val.map W.leTop.op t) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := M.val.presheaf) M.isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  let V := W ⊓ a.opens i
  let j : V ⟶ W := Opens.infLELeft _ _
  let k : V ⟶ a.opens i := Opens.infLERight _ _
  refine ⟨V, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change M.val.map j.op
      ((e.tensorPower (d + m)).tensorModuleCoefficients M h
        ((bundleTensor (bundleTensorPower T (d + m)) M).val.map W.leTop.op
          (atlasTwistedGlobalAction a M d m s t))) =
    M.val.map j.op
      ((e.tensorPower d).coefficients h ((bundleTensorPower T d).val.map W.leTop.op s) •
        (e.tensorPower m).tensorModuleCoefficients M h
          ((bundleTensor (bundleTensorPower T m) M).val.map W.leTop.op t))
  erw [M.val.map_smul, ← LocalBundleFrame.tensorModuleCoefficients_restrict,
    ← LocalBundleFrame.coefficients_restrict,
    ← LocalBundleFrame.tensorModuleCoefficients_restrict]
  simp only [top_restrict_comp]
  let z := (bundleTensor (bundleTensorPower T (d + m)) M).val.map V.leTop.op
    (atlasTwistedGlobalAction a M d m s t)
  let sv := (bundleTensorPower T d).val.map V.leTop.op s
  let tv := (bundleTensor (bundleTensorPower T m) M).val.map V.leTop.op t
  have hz := LocalBundleFrame.tensorModuleCoefficients_transition
    (e.tensorPower (d + m)) ((a.frame i).tensorPower (d + m)) M (j ≫ h) k z
  have hs := localBundleFrameTransition_coefficients
    (e.tensorPower d) ((a.frame i).tensorPower d) (j ≫ h) k sv
  have ht := LocalBundleFrame.tensorModuleCoefficients_transition
    (e.tensorPower m) ((a.frame i).tensorPower m) M (j ≫ h) k tv
  rw [localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val] at hz hs ht
  have ha := atlasTwistedGlobalAction_coefficients_subordinate a M d m i k s t
  apply ((localBundleFrameTransition e (a.frame i) (j ≫ h) k).isUnit.pow
    (d + m)).smul_bijective.injective
  change (localBundleFrameTransition e (a.frame i) (j ≫ h) k : X.sheaf.obj.obj (op V)) ^ (d + m) •
      (e.tensorPower (d + m)).tensorModuleCoefficients M (j ≫ h) z = _
  rw [← hz, ha, hs, ht]
  simp only [pow_add, ← mul_smul]
  congr 1
  ring

/-- The genuine global twisted action is independent of the line atlas. -/
theorem atlasTwistedGlobalAction_atlas_independent (a b : LineBundleAtlas T)
    (M : X.Modules) (d m : ℕ)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M m) :
    atlasTwistedGlobalAction a M d m s t = atlasTwistedGlobalAction b M d m s t := by
  apply atlasTwistedGlobalCoefficients_ext b M (d + m)
  intro i
  rw [atlasTwistedGlobalAction_coefficients]
  exact atlasTwistedGlobalAction_anyFrame a M d m (b.frame i) (𝟙 _) s t

/-- Literal tensor powers of any given line isomorphism and their tensor
transport on an arbitrary module intertwine the actual twisted section action. -/
theorem nativeLineTensorPowerIso_twistedGlobalAction {P Q : X.Modules} (E : P ≅ Q)
    (a : LineBundleAtlas P) (b : LineBundleAtlas Q) (M : X.Modules) (d m : ℕ)
    (s : bundlePowerGlobalSections P d) (t : bundleTwistedGlobalSections P M m) :
    (bundleTensorIso (nativeLineTensorPowerIso E (d + m)) (Iso.refl M)).hom.val.app (.op ⊤)
      (atlasTwistedGlobalAction a M d m s t) =
    atlasTwistedGlobalAction b M d m
      ((nativeLineTensorPowerIso E d).hom.val.app (.op ⊤) s)
      ((bundleTensorIso (nativeLineTensorPowerIso E m) (Iso.refl M)).hom.val.app (.op ⊤) t) := by
  apply atlasTwistedGlobalCoefficients_ext b M (d + m)
  intro i
  rw [atlasTwistedGlobalAction_coefficients]
  let p : LocalBundleFrame P (b.opens i) :=
    (SheafOfModules.overFunctor X.ringCatSheaf (b.opens i)).mapIso E ≪≫ b.frame i
  have hs (k : ℕ) (v : bundlePowerGlobalSections P k) :
      atlasPowerGlobalCoefficients b k i
        ((nativeLineTensorPowerIso E k).hom.val.app (.op ⊤) v) =
      (p.tensorPower k).coefficients (𝟙 _)
        ((bundleTensorPower P k).val.map (b.opens i).leTop.op v) := by
    unfold atlasPowerGlobalCoefficients
    rw [← PresheafOfModules.naturality_apply]
    exact nativeTensorPowerIso_frame_coefficients E p (b.frame i) (fun _ _ _ ↦ rfl) k (𝟙 _) _
  have ht (k : ℕ) (v : bundleTwistedGlobalSections P M k) :
      atlasTwistedGlobalCoefficients b M k i
        ((bundleTensorIso (nativeLineTensorPowerIso E k) (Iso.refl M)).hom.val.app (.op ⊤) v) =
      (p.tensorPower k).tensorModuleCoefficients M (𝟙 _)
        ((bundleTensor (bundleTensorPower P k) M).val.map (b.opens i).leTop.op v) := by
    unfold atlasTwistedGlobalCoefficients
    rw [← PresheafOfModules.naturality_apply]
    exact nativeTensorTwistIso_coefficients (nativeLineTensorPowerIso E k)
      (p.tensorPower k) ((b.frame i).tensorPower k)
      (fun W h s ↦ nativeTensorPowerIso_frame_coefficients E p (b.frame i)
        (fun _ _ _ ↦ rfl) k h s) M (𝟙 _) _
  rw [ht, hs, ht]
  exact atlasTwistedGlobalAction_anyFrame a M d m p (𝟙 _) s t

end
end SGPT.Foundations.Schemes
