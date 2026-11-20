import SGPT.Foundations.Schemes.TwistedModuleFrames
import SGPT.Foundations.Schemes.ModulePushforwardRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Final

/-! # Genuine native pullback frames

Native pullback preserves the actual structure sheaf, and its actual
composition comparisons transport a genuine line frame to the true
inverse-image open. No pulled-back line or frame is supplied as data.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace
open CategoryTheory.Functor

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{u}}

/-- The native inverse-image functor on actual opens is final because it
sends the actual terminal open to the actual terminal open. -/
theorem nativeSchemeInverseImageOpens_final (f : X ⟶ Y) :
    (Opens.map f.base).Final := by
  have : (fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    final_fromPUnit_of_isTerminal isTerminalTop
  have : (fromPUnit.{0} (⊤ : X.Opens)).Final :=
    final_fromPUnit_of_isTerminal isTerminalTop
  have : (fromPUnit.{0} (⊤ : Y.Opens) ⋙ Opens.map f.base).Final :=
    Functor.final_of_natIso (F := fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ ↦ eqToIso (by rfl)))
  exact Functor.final_of_final_comp (fromPUnit.{0} (⊤ : Y.Opens)) (Opens.map f.base)

/-- The genuine adjoint of the actual structure-ring morphism is the
canonical native pullback isomorphism of structure sheaves. -/
def nativeSchemePullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  have := nativeSchemeInverseImageOpens_final f
  let e : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

/-- The true unit isomorphism has the literal actual structural-ring
morphism as its adjunction mate. -/
theorem nativeSchemePullbackUnitIso_mate (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (nativeSchemePullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  by
    change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- Actual pullback and actual open restriction agree through the genuine
composition square of the native scheme maps. -/
def nativeSchemePullbackRestrictIso (f : X ⟶ Y) (U : Y.Opens) (L : Y.Modules) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app L ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

/-- A genuine over-site line frame gives the literal open-subscheme frame. -/
def LocalBundleFrame.nativeRestriction {L : Y.Modules} {U : Y.Opens}
    (e : LocalBundleFrame L U) :
    L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app L).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- A genuine native pullback frame on the actual inverse-image subscheme. -/
def LocalBundleFrame.nativePullbackRestriction (f : X ⟶ Y)
    {L : Y.Modules} {U : Y.Opens} (e : LocalBundleFrame L U) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  nativeSchemePullbackRestrictIso f U L ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e.nativeRestriction ≪≫
    nativeSchemePullbackUnitIso (f ∣_ U)

/-- The genuine pulled-back frame, returned to the native over-site spelling. -/
def LocalBundleFrame.nativePullback (f : X ⟶ Y) {L : Y.Modules} {U : Y.Opens}
    (e : LocalBundleFrame L U) :
    LocalBundleFrame ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) :=
  (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app _ ≪≫
      e.nativePullbackRestriction f ≪≫
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- Pulling back the actual atlas gives a genuine atlas of the actual native
pullback sheaf, with true inverse-image opens and true pulled-back frames. -/
def LineBundleAtlas.nativePullback (f : X ⟶ Y) {L : Y.Modules}
    (a : LineBundleAtlas L) : LineBundleAtlas ((Scheme.Modules.pullback f).obj L) where
  I := a.I
  opens i := f ⁻¹ᵁ a.opens i
  covers x := by
    obtain ⟨i, hi⟩ := a.covers (f.base x)
    exact ⟨i, hi⟩
  frame i := (a.frame i).nativePullback f

end

end SGPT.Foundations.Schemes
