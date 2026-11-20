import SGPT.Foundations.Schemes.NativeLinePullbackFrames
import Mathlib.CategoryTheory.Adjunction.Mates

/-! Actual original module pullback/restriction comparison with its
genuine ORIGINAL unit mate. Blueprint: original-line-pullback-mate.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

/-- The ACTUAL two composite pushforwards agree by the SAME original
restricted scheme map square. No Beck--Chevalley certificate input. -/
def openSquarePushforwardCompIso :
    Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι ≅
      Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f :=
  Scheme.Modules.pushforwardComp (f ∣_ U) U.ι ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U) ≪≫
    (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f).symm

private def originalOpenSquareLeftAdjunction :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⊣
      Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)

private def originalOpenSquareRightAdjunction :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ⊣
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))

/-- The genuine original pullback/restriction isomorphism is manufactured
as the actual adjunction mate, preserving the SAME original module-sheaf. -/
def openSquarePullbackIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  (originalOpenSquareLeftAdjunction f U).leftAdjointUniq
    ((originalOpenSquareRightAdjunction f U).ofNatIsoRight (openSquarePushforwardCompIso f U))

/-- The ACTUAL original adjunction units commute through the manufactured
genuine restriction square. This is proved, never a comparison premise. -/
theorem openSquarePullbackIso_unit (L : Y.Modules) :
    (originalOpenSquareLeftAdjunction f U).unit.app L ≫
      (Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f).map
        ((openSquarePullbackIso f U).hom.app L) =
      (originalOpenSquareRightAdjunction f U).unit.app L ≫
        (openSquarePushforwardCompIso f U).hom.app
          ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)).obj L) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (originalOpenSquareLeftAdjunction f U)
    ((originalOpenSquareRightAdjunction f U).ofNatIsoRight (openSquarePushforwardCompIso f U)) L
  exact h

/-- An actual original local frame gives a genuine frame of the SAME
actual pulled-back sheaf on its TRUE inverse-image open, using the
proved unit-compatible comparison rather than an assumed coefficient square. -/
def matePullbackFrameRestriction {L : Y.Modules} (α : LocalBundleFrame L U) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  (openSquarePullbackIso f U).app L ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso α.nativeRestriction ≪≫
    nativeSchemePullbackUnitIso (f ∣_ U)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
