import SGPT.Projective.OriginalNormalizationFiniteMap
import SGPT.Projective.OriginalPullbackFrameTransition
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! Actual ORIGINAL line adjunction unit into the SAME normalized pullback
is injective on EVERY original open. No section, smoothness, unit-injectivity
or finite-support comparison premise. Blueprint: original-normalization-line-unit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite

/-- Genuine schematic dominance and actual original frame readback make
an original line's ACTUAL adjunction unit injective on EVERY original open. -/
theorem originalDominantLineUnit_injective {Y Z : Scheme.{0}} (g : Z ⟶ Y)
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g]
    {L : Y.Modules} (a : LineBundleAtlas L) (U : Y.Opens) :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L).val.app (op U)) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L
  intro s t h
  apply a.section_ext U s t
  intro i
  let W := U ⊓ a.opens i
  let j : W ⟶ U := homOfLE inf_le_left
  let l : W ⟶ a.opens i := homOfLE inf_le_right
  apply g.app_injective W
  change g.app W ((a.frame i).coefficients l (L.val.map j.op s)) =
    g.app W ((a.frame i).coefficients l (L.val.map j.op t))
  rw [← matePullbackFrame_coefficient_simple g (a.frame i) l,
    ← matePullbackFrame_coefficient_simple g (a.frame i) l]
  congr 1
  have hs := PresheafOfModules.naturality_apply η.val j.op s
  have ht := PresheafOfModules.naturality_apply η.val j.op t
  exact hs.trans ((congrArg (((Scheme.Modules.pushforward g).obj
    ((Scheme.Modules.pullback g).obj L)).presheaf.map j.op) h).trans ht.symm)

variable (X : Scheme.{0}) [IsIntegral X]

/-- The ACTUAL original normalization is genuinely schematically dominant
on the SAME original reduced scheme, not an assumed injective coefficient map. -/
instance originalNormalizationMap_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (originalNormalizationMap X) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- Every ACTUAL original normalization coefficient map is injective,
on ALL original opens, including empty opens, with no affine restriction. -/
theorem originalNormalizationMap_app_injective (U : X.Opens) :
    Function.Injective ((originalNormalizationMap X).app U) :=
  (originalNormalizationMap X).app_injective U

/-- The genuine SAME original line adjunction unit into the actual
normalized pullback is injective on EVERY original open. No original
smoothness, normalization geometry, section or target-unit premise. -/
theorem originalNormalizationLineUnit_injective {L : X.Modules}
    (a : LineBundleAtlas L) (U : X.Opens) :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction
      (originalNormalizationMap X)).unit.app L).val.app (op U)) :=
  originalDominantLineUnit_injective (originalNormalizationMap X) a U

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
