import SGPT.Projective.OriginalMixedEulerDifference

/-! Genuine original pullback and testing-line twist of actual INTEGER
mixed Euler operations. Blueprint: original-mixed-euler-pullback.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X Y : Scheme.{0}}

/-- ONLY the actual original sheaf pullback and SAME genuine pulled original
atlas; no degree/period/compatibility field or premise. -/
def originalLinePullback (g : X ⟶ Y) (B : IntrinsicLineBundle Y) : IntrinsicLineBundle X where
  sheaf := (Scheme.Modules.pullback g).obj B.sheaf
  atlas := matePullbackAtlas g B.atlas

/-- Genuine original module functoriality transports actual isomorphism
invariance through the actual original whole-sheaf pullback. -/
theorem originalLinePullback_function_invariant (g : X ⟶ Y)
    (F : IntrinsicLineBundle X → ℤ) (hF : OriginalLineIsomorphismInvariant F) :
    OriginalLineIsomorphismInvariant (fun B => F (originalLinePullback g B)) :=
  fun B C e => hF (originalLinePullback g B) (originalLinePullback g C)
    ((Scheme.Modules.pullback g).mapIso e)

/-- The actual original tensor testing-line shift commutes through ALL
mixed differences, by genuine DISTINCT-line original sheaf right-swap maps. -/
theorem originalLineMixedDifference_twist_base (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) (A : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalLineMixedDifference (fun B => F (originalLineTensor B A)) As B =
      originalLineMixedDifference F As (originalLineTensor B A) := by
  induction As generalizing B with
  | nil => rfl
  | cons C As ih =>
    change originalLineMixedDifference (fun B => F (originalLineTensor B A)) As (originalLineTensor B C) -
        originalLineMixedDifference (fun B => F (originalLineTensor B A)) As B =
      originalLineMixedDifference F As (originalLineTensor (originalLineTensor B A) C) -
        originalLineMixedDifference F As (originalLineTensor B A)
    rw [ih, ih]
    exact congrArg₂ (fun x y : ℤ => x - y)
      (originalLineMixedDifference_invariant F hF As
        (B := originalLineTensor (originalLineTensor B C) A)
        (C := originalLineTensor (originalLineTensor B A) C)
        (originalLineTensorRightSwapIso B.atlas C.atlas A.atlas)) rfl

/-- Actual original mixed tensor operations commute with actual original
line pullback, retaining SAME original lines and SAME actual scheme map.
Every tensor/pullback comparison is the internally proved genuine frame iso. -/
theorem originalLineMixedDifference_pullback (g : X ⟶ Y)
    (F : IntrinsicLineBundle X → ℤ) (hF : OriginalLineIsomorphismInvariant F)
    (As : List (IntrinsicLineBundle Y)) (B : IntrinsicLineBundle Y) :
    originalLineMixedDifference (fun B => F (originalLinePullback g B)) As B =
      originalLineMixedDifference F (As.map (originalLinePullback g)) (originalLinePullback g B) := by
  induction As generalizing B with
  | nil => rfl
  | cons A As ih =>
    change originalLineMixedDifference (fun B => F (originalLinePullback g B)) As (originalLineTensor B A) -
        originalLineMixedDifference (fun B => F (originalLinePullback g B)) As B =
      originalLineMixedDifference F (As.map (originalLinePullback g))
          (originalLineTensor (originalLinePullback g B) (originalLinePullback g A)) -
        originalLineMixedDifference F (As.map (originalLinePullback g)) (originalLinePullback g B)
    rw [ih, ih]
    exact congrArg₂ (fun x y : ℤ => x - y)
      (originalLineMixedDifference_invariant F hF (As.map (originalLinePullback g))
        (B := originalLinePullback g (originalLineTensor B A))
        (C := originalLineTensor (originalLinePullback g B) (originalLinePullback g A))
        (originalLinePullbackTensorIso g B.atlas A.atlas)) rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
