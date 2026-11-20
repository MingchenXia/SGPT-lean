import SGPT.Projective.OriginalPullbackFrameTransition
import SGPT.Okounkov.SchemeComplexPointStalkEvaluation
import SGPT.Okounkov.SchemeLineBundleAnalyticTransitions

/-! Actual analytic values and transitions of SAME original pulled frames.
Blueprint: original-analytic-frame-pullback.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  (EX : ClosedProjectiveEmbedding (h ≫ f)) (EY : ClosedProjectiveEmbedding f)

/-- SAME original scalar values under the ACTUAL morphism. -/
theorem originalRegularFunction_pullback (U : Y.Opens) (r : Γ(Y, U))
    (p : SchemeComplexPoint (h ≫ f))
    (hp : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ U) :
    schemeOpenRegularFunction (h ≫ f) n EX (h ⁻¹ᵁ U) (h.app U r) p =
      schemeOpenRegularFunction f m EY U r (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  let := EX.isSeparated
  let := EX.quasiCompact
  let := EY.isSeparated
  let := EY.quasiCompact
  rw [schemeOpenRegularFunction_apply (h ≫ f) n EX (h ⁻¹ᵁ U) _ p hp,
    schemeOpenRegularFunction_apply f m EY U r
      (schemeComplexPointMap (h ≫ f) f h rfl p) hp,
    schemeNativeStalkGerm_eval, schemeNativeStalkGerm_eval]
  erw [← h.germ_stalkMap_apply]
  exact (congrArg (fun k : Y.presheaf.stalk
    (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p)) →+* ℂ =>
      k (Y.presheaf.germ U _ hp r))
        (schemeComplexPointStalkEval_comp (h ≫ f) f h rfl p)).symm

/-- Genuine analytic transitions of ANY original pulled local frames. -/
theorem matePullbackFrame_analytic_transition {L : Y.Modules} {U V : Y.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (p : SchemeComplexPoint (h ≫ f))
    (hpU : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ U)
    (hpV : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ V) :
    schemeFrameTransition (h ≫ f) n EX (matePullbackFrame h α) (matePullbackFrame h β) p =
      schemeFrameTransition f m EY α β (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  change schemeOpenRegularFunction (h ≫ f) n EX (h ⁻¹ᵁ (U ⊓ V)) _ p = _
  have ht := matePullbackFrame_transition h α β (homOfLE inf_le_left) (homOfLE inf_le_right)
  exact (congrArg (fun r : Γ(X, h ⁻¹ᵁ (U ⊓ V)) =>
    schemeOpenRegularFunction (h ≫ f) n EX (h ⁻¹ᵁ (U ⊓ V)) r p) ht).trans
      (originalRegularFunction_pullback f h n m EX EY (U ⊓ V) _ p ⟨hpU, hpV⟩)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
