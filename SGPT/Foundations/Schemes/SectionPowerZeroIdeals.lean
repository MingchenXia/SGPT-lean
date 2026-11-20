import SGPT.Foundations.Schemes.TensorSectionZeroIdeals
import SGPT.Foundations.Schemes.EffectiveCartierIdealMultiplication

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine recursive powers of an ORIGINAL actual global line section,
with the TRUE unit section in native tensor degree zero. -/
def bundleGlobalSectionTensorPower {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤)) :
    ∀ m : ℕ, bundlePowerGlobalSections L m
  | 0 => (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from (1 : Γ(X, ⊤)))
  | m + 1 => tensorSection (bundleTensorPower L m) L ⊤
      (bundleGlobalSectionTensorPower L s m) s

/-- The literal section powers retain ORIGINAL frame coefficients, including
the actual unit in degree zero and original structural restrictions. -/
theorem LocalBundleFrame.globalSectionTensorPower_coefficients
    {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (s : Γ(L, ⊤)) (m : ℕ) :
    (e.tensorPower m).coefficients i
      ((bundleTensorPower L m).val.map V.leTop.op (bundleGlobalSectionTensorPower L s m)) =
      (e.coefficients i (L.val.map V.leTop.op s)) ^ m := by
  induction m with
  | zero =>
    change X.presheaf.map V.leTop.op 1 = _ ^ 0
    rw [map_one, pow_zero]
  | succ m ih =>
    change ((e.tensorPower m).tensor e).coefficients i
      ((bundleTensor (bundleTensorPower L m) L).val.map V.leTop.op
        (tensorSection (bundleTensorPower L m) L ⊤ (bundleGlobalSectionTensorPower L s m) s)) = _
    rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients, ih, pow_succ]

/-- The actual degree-zero unit section has the genuine UNIT zero ideal,
for every original atlas, including empty schemes. -/
theorem sectionZeroIdealSheaf_globalSectionTensorPower_zero {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroIdealSheaf (a.tensorPower 0) (bundleGlobalSectionTensorPower L s 0) = 1 := by
  apply Scheme.IdealSheafData.ext
  funext U
  change sectionZeroIdeal (SheafOfModules.unit X.ringCatSheaf)
    (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from (1 : Γ(X, ⊤))) U.val = ⊤
  let E : LocalBundleFrame (SheafOfModules.unit X.ringCatSheaf) ⊤ := Iso.refl _
  rw [sectionZeroIdeal_eq_span_frame _ E U.val.leTop]
  change Ideal.span {X.presheaf.map U.val.leTop.op 1} = ⊤
  rw [map_one, Ideal.span_singleton_one]

/-- Actual original section powers give EXACT native ideal-sheaf powers,
retaining scheme-theoretic multiplicities and the degree-zero unit. -/
theorem sectionZeroIdealSheaf_globalSectionTensorPower {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (m : ℕ) :
    sectionZeroIdealSheaf (a.tensorPower m) (bundleGlobalSectionTensorPower L s m) =
      (sectionZeroIdealSheaf a s) ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using sectionZeroIdealSheaf_globalSectionTensorPower_zero a s
  | succ m ih =>
    have h := sectionZeroIdealSheaf_tensorSection (a.tensorPower m) a
      (bundleGlobalSectionTensorPower L s m) s
    change sectionZeroIdealSheaf (a.tensorPower (m + 1))
      (tensorSection (bundleTensorPower L m) L ⊤ (bundleGlobalSectionTensorPower L s m) s) = _
    change sectionZeroIdealSheaf (a.tensorPower (m + 1))
      (tensorSection (bundleTensorPower L m) L ⊤ (bundleGlobalSectionTensorPower L s m) s) = _ at h
    rw [h, ih, pow_succ]

end
end SGPT.Foundations.Schemes
