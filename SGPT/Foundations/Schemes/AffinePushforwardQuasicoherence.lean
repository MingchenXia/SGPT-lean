import SGPT.Foundations.Schemes.ModulePushforwardAffine

/-! # Genuine global quasicoherence of affine pushforwards

Actual affine presentations and native open-site descent derive global
quasicoherence; no global-section finiteness is assumed.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A native quasicoherent module on an actual affine scheme has a true presentation. -/
def affineQuasicoherentPresentation {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] : M.Presentation := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let : N.IsQuasicoherent := isoPushforward_isQuasicoherent e M
  let : IsIso N.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ N).mp (inferInstance : N.IsQuasicoherent)
  let T := (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)
  let p : (tilde T).Presentation :=
    presentationTilde T Set.univ (by simp) _ (Submodule.span_eq _)
  let q : N.Presentation := p.ofIsIso N.fromTildeΓ
  exact (Scheme.Modules.presentationRestrict e.hom q).ofIsIso
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app M).hom

/-- The actual open-site equivalence transports true restricted presentations. -/
def nativeOverPresentation {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (p : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let e := Scheme.Modules.overEquiv U
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      e.inverse.obj (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let α : e.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (e.unitIso.app (M.over U)).symm
  exact (p.map e.inverse η).ofIsIso α.hom

/-- True covered restriction presentations produce native quasicoherent data. -/
def nativeQuasicoherentDataOfRestrictedPresentations {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (p : ∀ i, (M.restrict (U i).ι).Presentation) : M.QuasicoherentData where
  I := I
  X := U
  coversTop := by rwa [_root_.Opens.coversTop_iff]
  presentation i := nativeOverPresentation M (U i) (p i)

/-- Actual quasicoherence on all affine restrictions implies genuine global quasicoherence. -/
theorem nativeQuasicoherentOfAffineRestrictions {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ (U : X.Opens), IsAffineOpen U → (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨S, hS, hcover⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens ⊤
  let U : S → X.Opens := Subtype.val
  have hU : iSup U = ⊤ := by
    rw [← sSup_eq_iSup']
    exact hcover.symm
  let p (i : S) : (M.restrict (U i).ι).Presentation := by
    let : IsAffine (U i).toScheme := hS i.property
    let : (M.restrict (U i).ι).IsQuasicoherent := h (U i) (hS i.property)
    exact affineQuasicoherentPresentation (M.restrict (U i).ι)
  exact (nativeQuasicoherentDataOfRestrictedPresentations M U hU p).isQuasicoherent

/-- Every genuine affine morphism preserves actual global quasicoherence. -/
theorem affineMorphismPushforward_isQuasicoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  apply nativeQuasicoherentOfAffineRestrictions
  intro U hU
  let : IsAffine U.toScheme := hU
  let : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let N := (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)
  let : N.IsQuasicoherent :=
    affineSchemePushforward_isQuasicoherent (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (pushforwardRestrictIso f U M).symm (inferInstance : N.IsQuasicoherent)

/-- Native closed immersions preserve actual global quasicoherence. -/
theorem closedImmersionPushforward_isQuasicoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
  affineMorphismPushforward_isQuasicoherent f M

/-- A true line atlas produces quasicoherence of every actual closed pushforward power. -/
theorem LineBundleAtlas.closedImmersionPushforwardPower_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    ((Scheme.Modules.pushforward f).obj (bundleTensorPower L m)).IsQuasicoherent := by
  let := a.tensorPower_isQuasicoherent m
  exact closedImmersionPushforward_isQuasicoherent f (bundleTensorPower L m)

end

end SGPT.Foundations.Schemes
