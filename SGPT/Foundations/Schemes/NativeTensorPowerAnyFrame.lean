import SGPT.Foundations.Schemes.NativeTensorPowerIsoFrames
/-!
# NativeTensorPowerAnyFrame

The genuine additive and iterated tensor-power comparisons preserve coefficients in every actual local frame. True transition units and actual sheaf separation prove independence from their defining atlas.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}} {L : X.Modules}

/-- The actual iterated power comparison preserves coefficients in every genuine frame, independently of its defining atlas. -/
theorem nativeLineTensorPowerMulIso_anyFrame (a : LineBundleAtlas L) (r m : ℕ)
    {U W : X.Opens} (e : LocalBundleFrame L U) (h : W ⟶ U)
    (s : bundleSections (bundleTensorPower L (r * m)) W) :
    ((e.tensorPower r).tensorPower m).coefficients h
      ((nativeLineTensorPowerMulIso a r m).hom.val.app (.op W) s) =
      (e.tensorPower (r * m)).coefficients h s := by
  let E := nativeLineTensorPowerMulIso a r m
  let O := SheafOfModules.unit X.ringCatSheaf
  apply TopCat.Presheaf.IsSheaf.section_ext (F := O.val.presheaf) O.isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  let V := W ⊓ a.opens i
  let j : V ⟶ W := Opens.infLELeft _ _
  let k : V ⟶ a.opens i := Opens.infLERight _ _
  refine ⟨V, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change X.sheaf.obj.map j.op (((e.tensorPower r).tensorPower m).coefficients h
      (E.hom.val.app (.op W) s)) =
    X.sheaf.obj.map j.op ((e.tensorPower (r * m)).coefficients h s)
  rw [← LocalBundleFrame.coefficients_restrict, ← LocalBundleFrame.coefficients_restrict]
  have hn := PresheafOfModules.naturality_apply E.hom.val j.op s
  change E.hom.val.app (.op V) ((bundleTensorPower L (r * m)).val.map j.op s) =
    (bundleTensorPower (bundleTensorPower L r) m).val.map j.op (E.hom.val.app (.op W) s) at hn
  rw [← hn]
  let t := (bundleTensorPower L (r * m)).val.map j.op s
  have ha := localBundleFrameTransition_coefficients (e.tensorPower (r * m))
    ((a.frame i).tensorPower (r * m)) (j ≫ h) k t
  have hb := localBundleFrameTransition_coefficients ((e.tensorPower r).tensorPower m)
    (((a.frame i).tensorPower r).tensorPower m) (j ≫ h) k (E.hom.val.app (.op V) t)
  rw [localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val] at ha
  rw [localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower,
    ← pow_mul, Units.val_pow_eq_pow_val] at hb
  have he := nativeLineTensorPowerMulIso_coefficients a r m i k t
  change (((a.frame i).tensorPower r).tensorPower m).coefficients k
    (E.hom.val.app (.op V) t) = ((a.frame i).tensorPower (r * m)).coefficients k t at he
  have hu := (localBundleFrameTransition e (a.frame i) (j ≫ h) k).isUnit.pow (r * m)
  apply hu.mul_left_cancel
  exact hb.symm.trans (he.trans ha)
/-- The actual additive power comparison preserves coefficients in every genuine frame, independently of its defining atlas. -/
theorem nativeLineTensorPowerAddIso_anyFrame (a : LineBundleAtlas L) (m n : ℕ)
    {U W : X.Opens} (e : LocalBundleFrame L U) (h : W ⟶ U)
    (s : bundleSections (bundleTensorPower L (m + n)) W) :
    ((e.tensorPower m).tensor (e.tensorPower n)).coefficients h
      ((nativeLineTensorPowerAddIso a m n).hom.val.app (.op W) s) =
      (e.tensorPower (m + n)).coefficients h s := by
  let E := nativeLineTensorPowerAddIso a m n
  let O := SheafOfModules.unit X.ringCatSheaf
  apply TopCat.Presheaf.IsSheaf.section_ext (F := O.val.presheaf) O.isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  let V := W ⊓ a.opens i
  let j : V ⟶ W := Opens.infLELeft _ _
  let k : V ⟶ a.opens i := Opens.infLERight _ _
  refine ⟨V, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change X.sheaf.obj.map j.op (((e.tensorPower m).tensor (e.tensorPower n)).coefficients h
      (E.hom.val.app (.op W) s)) =
    X.sheaf.obj.map j.op ((e.tensorPower (m + n)).coefficients h s)
  rw [← LocalBundleFrame.coefficients_restrict, ← LocalBundleFrame.coefficients_restrict]
  have hn := PresheafOfModules.naturality_apply E.hom.val j.op s
  change E.hom.val.app (.op V) ((bundleTensorPower L (m + n)).val.map j.op s) =
    (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n)).val.map j.op (E.hom.val.app (.op W) s) at hn
  rw [← hn]
  let t := (bundleTensorPower L (m + n)).val.map j.op s
  have ha := localBundleFrameTransition_coefficients (e.tensorPower (m + n))
    ((a.frame i).tensorPower (m + n)) (j ≫ h) k t
  have hb := localBundleFrameTransition_coefficients ((e.tensorPower m).tensor (e.tensorPower n))
    (((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)) (j ≫ h) k (E.hom.val.app (.op V) t)
  rw [localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val] at ha
  rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
    localBundleFrameTransition_tensorPower, ← pow_add, Units.val_pow_eq_pow_val] at hb
  have he := nativeLineTensorPowerAddIso_coefficients a m n i k t
  change (((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)).coefficients k
    (E.hom.val.app (.op V) t) = ((a.frame i).tensorPower (m + n)).coefficients k t at he
  have hu := (localBundleFrameTransition e (a.frame i) (j ≫ h) k).isUnit.pow (m + n)
  apply hu.mul_left_cancel
  exact hb.symm.trans (he.trans ha)

end
end SGPT.Foundations.Schemes
