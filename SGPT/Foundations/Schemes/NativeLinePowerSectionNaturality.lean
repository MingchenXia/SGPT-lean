import SGPT.Foundations.Schemes.NativeTensorPowerAnyFrame

/-!
# Naturality of multiplication on actual line-power sections

The original section product is the inverse additive tensor comparison on
pure tensors. It is independent of the atlas and natural in line isomorphisms.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {B : X.Modules}

/-- The original global section product is the inverse additive power
comparison applied to the actual pure tensor. -/
theorem nativeLineTensorPowerAddIso_inv_globalTensor (a : LineBundleAtlas B) (m n : ℕ)
    (s : bundlePowerGlobalSections B m) (t : bundlePowerGlobalSections B n) :
    (nativeLineTensorPowerAddIso a m n).inv.val.app (.op ⊤)
      (tensorSection (bundleTensorPower B m) (bundleTensorPower B n) ⊤ s t) =
      atlasPowerGlobalMul a m n s t := by
  apply atlasPowerGlobalCoefficients_ext a (m + n)
  intro i
  rw [atlasPowerGlobalMul_coefficients]
  unfold atlasPowerGlobalCoefficients
  rw [← PresheafOfModules.naturality_apply, tensorSection_restrict]
  exact nativeLineTensorPowerAddIso_inv_tensorSection a m n i (𝟙 _) _ _

/-- The forward additive power comparison sends the actual global section
product to the actual pure tensor. -/
theorem nativeLineTensorPowerAddIso_globalMul (a : LineBundleAtlas B) (m n : ℕ)
    (s : bundlePowerGlobalSections B m) (t : bundlePowerGlobalSections B n) :
    (nativeLineTensorPowerAddIso a m n).hom.val.app (.op ⊤)
      (atlasPowerGlobalMul a m n s t) =
      tensorSection (bundleTensorPower B m) (bundleTensorPower B n) ⊤ s t := by
  rw [← nativeLineTensorPowerAddIso_inv_globalTensor]
  exact congr($( (nativeLineTensorPowerAddIso a m n).inv_hom_id ).val.app (.op ⊤)
    |>.hom (tensorSection (bundleTensorPower B m) (bundleTensorPower B n) ⊤ s t))

/-- The actual section product has the product coefficient in every genuine
local frame, independently of its defining atlas. -/
theorem atlasPowerGlobalMul_anyFrame (a : LineBundleAtlas B) (m n : ℕ)
    {U W : X.Opens} (e : LocalBundleFrame B U) (h : W ⟶ U)
    (s : bundlePowerGlobalSections B m) (t : bundlePowerGlobalSections B n) :
    (e.tensorPower (m + n)).coefficients h
      ((bundleTensorPower B (m + n)).val.map W.leTop.op (atlasPowerGlobalMul a m n s t)) =
    (e.tensorPower m).coefficients h ((bundleTensorPower B m).val.map W.leTop.op s) *
      (e.tensorPower n).coefficients h ((bundleTensorPower B n).val.map W.leTop.op t) := by
  have hc := nativeLineTensorPowerAddIso_anyFrame a m n e h
    ((bundleTensorPower B (m + n)).val.map W.leTop.op (atlasPowerGlobalMul a m n s t))
  rw [PresheafOfModules.naturality_apply, nativeLineTensorPowerAddIso_globalMul,
    tensorSection_restrict, LocalBundleFrame.tensor_coefficients] at hc
  exact hc.symm

/-- The genuine global section product does not depend on the line atlas used
to construct its sheaf gluing. -/
theorem atlasPowerGlobalMul_atlas_independent (a b : LineBundleAtlas B) (m n : ℕ)
    (s : bundlePowerGlobalSections B m) (t : bundlePowerGlobalSections B n) :
    atlasPowerGlobalMul a m n s t = atlasPowerGlobalMul b m n s t := by
  apply atlasPowerGlobalCoefficients_ext b (m + n)
  intro i
  rw [atlasPowerGlobalMul_coefficients]
  exact atlasPowerGlobalMul_anyFrame a m n (b.frame i) (𝟙 _) s t

/-- Actual tensor powers of any given line isomorphism preserve the original
section products, with no compatibility assumption on the two atlases. -/
theorem nativeLineTensorPowerIso_globalMul {P Q : X.Modules} (E : P ≅ Q)
    (a : LineBundleAtlas P) (b : LineBundleAtlas Q) (m n : ℕ)
    (s : bundlePowerGlobalSections P m) (t : bundlePowerGlobalSections P n) :
    (nativeLineTensorPowerIso E (m + n)).hom.val.app (.op ⊤)
      (atlasPowerGlobalMul a m n s t) =
    atlasPowerGlobalMul b m n
      ((nativeLineTensorPowerIso E m).hom.val.app (.op ⊤) s)
      ((nativeLineTensorPowerIso E n).hom.val.app (.op ⊤) t) := by
  apply atlasPowerGlobalCoefficients_ext b (m + n)
  intro i
  rw [atlasPowerGlobalMul_coefficients]
  let p : LocalBundleFrame P (b.opens i) :=
    (SheafOfModules.overFunctor X.ringCatSheaf (b.opens i)).mapIso E ≪≫ b.frame i
  have hc (d : ℕ) (v : bundlePowerGlobalSections P d) :
      atlasPowerGlobalCoefficients b d i
        ((nativeLineTensorPowerIso E d).hom.val.app (.op ⊤) v) =
      (p.tensorPower d).coefficients (𝟙 _)
        ((bundleTensorPower P d).val.map (b.opens i).leTop.op v) := by
    unfold atlasPowerGlobalCoefficients
    rw [← PresheafOfModules.naturality_apply]
    exact nativeTensorPowerIso_frame_coefficients E p (b.frame i) (fun _ _ _ ↦ rfl) d (𝟙 _) _
  rw [hc, hc, hc]
  exact atlasPowerGlobalMul_anyFrame a m n p (𝟙 _) s t

end
end SGPT.Foundations.Schemes
