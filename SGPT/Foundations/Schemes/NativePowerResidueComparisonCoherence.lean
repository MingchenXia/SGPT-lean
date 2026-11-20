import SGPT.Foundations.Schemes.NativePowerResidueSectionAction
import SGPT.Foundations.Schemes.NativeTensorPowerIsoFrames
import SGPT.Foundations.Schemes.NativePolarizedResidueComparison

/-!
# Coherence of the original and polarized residue comparisons

The direct original-atlas residue comparison equals the additive-power
comparison followed by the iterated-power comparison used in polarization.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)

/-- The actual sheafified tensor transports compositions of isomorphisms. -/
theorem nativeBundleTensorIso_trans {P P' P'' Q Q' Q'' : X.Modules}
    (e : P ≅ P') (e' : P' ≅ P'') (f : Q ≅ Q') (f' : Q' ≅ Q'') :
    bundleTensorIso (e ≪≫ e') (f ≪≫ f') =
      bundleTensorIso e f ≪≫ bundleTensorIso e' f' := by
  apply Iso.ext
  simp only [bundleTensorIso, Functor.mapIso_hom, Iso.trans_hom,
    MonoidalCategory.tensorIso_hom, Functor.map_comp,
    ← MonoidalCategory.tensorHom_comp_tensorHom]

/-- Direct residue regrouping equals the additive and iterated power
regrouping composite used by the actual polarized comparison. -/
theorem nativeLineTensorPowerResidueIso_eq_add_mul {B : X.Modules}
    (a : LineBundleAtlas B) (q m r : ℕ) :
    nativeLineTensorPowerResidueIso a q m r =
      nativeLineTensorPowerAddIso a (q * m) r ≪≫
        bundleTensorIso (nativeLineTensorPowerMulIso a q m) (Iso.refl _) := by
  apply Iso.ext
  apply bundleHom_ext _ _ a.opens a.covers
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  change (nativeLineTensorPowerResidueIso a q m r).hom.val.app (.op W.unop.left) s =
    (bundleTensorIso (nativeLineTensorPowerMulIso a q m) (Iso.refl _)).hom.val.app
      (.op W.unop.left)
      ((nativeLineTensorPowerAddIso a (q * m) r).hom.val.app (.op W.unop.left) s)
  apply (((((a.frame i).tensorPower q).tensorPower m).tensor
    ((a.frame i).tensorPower r)).coefficients W.unop.hom).injective
  have ht := nativeTensorIso_frame_coefficients (nativeLineTensorPowerMulIso a q m)
    (Iso.refl (bundleTensorPower B r))
    ((a.frame i).tensorPower (q * m)) (((a.frame i).tensorPower q).tensorPower m)
    ((a.frame i).tensorPower r) ((a.frame i).tensorPower r)
    (fun W h s ↦ nativeLineTensorPowerMulIso_coefficients a q m i h s)
    (fun _ _ _ ↦ rfl) W.unop.hom
    ((nativeLineTensorPowerAddIso a (q * m) r).hom.val.app (.op W.unop.left) s)
  rw [nativeLineTensorPowerResidueIso_coefficients, ht,
    nativeLineTensorPowerAddIso_coefficients]

/-- The given polarized residue map factors through the very same original
residue regrouping whose section multiplication law has been proved. -/
theorem nativePolarizedLineResidueIso_eq_residue {Y : Scheme} (L : IntrinsicLineBundle Y)
    {K : Type} [Field K] (n : ℕ) (f : Y ⟶ polynomialProj K n) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)
    (m r : ℕ) :
    nativePolarizedLineResidueIso L n f q e m r =
      nativeLineTensorPowerResidueIso L.atlas q m r ≪≫
        bundleTensorIso (nativeLineTensorPowerIso e m ≪≫
          (nativePolynomialPullbackPowerIso K n f m).symm ≪≫
          (Scheme.Modules.pullback f).mapIso (nativePolynomialTwistingPowerIso K n m))
          (Iso.refl _) := by
  unfold nativePolarizedLineResidueIso nativePolarizedLinePowerIso
  rw [nativeLineTensorPowerResidueIso_eq_add_mul, Iso.trans_assoc]
  congr 1
  simpa only [Iso.refl_trans] using nativeBundleTensorIso_trans
    (nativeLineTensorPowerMulIso L.atlas q m)
    (nativeLineTensorPowerIso e m ≪≫
      (nativePolynomialPullbackPowerIso K n f m).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (nativePolynomialTwistingPowerIso K n m))
    (Iso.refl (bundleTensorPower L.sheaf r)) (Iso.refl _)

end
end SGPT.Foundations.Schemes
