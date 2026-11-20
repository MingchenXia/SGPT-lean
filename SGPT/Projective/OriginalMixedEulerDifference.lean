import SGPT.Projective.OriginalLineTensorArithmetic
import SGPT.Projective.OriginalArtinianLineEuler

/-! Independent original INTEGER mixed Euler differences of the actual
original section complexes. No native period/polarized diagonal definition.
Blueprint: original-mixed-euler-difference.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X : Scheme.{0}}

/-- Genuine actual original-line functional invariance under a genuine
original sheaf isomorphism; no metric/class/period relation is used. -/
def OriginalLineIsomorphismInvariant (F : IntrinsicLineBundle X → ℤ) : Prop :=
  ∀ A B, (A.sheaf ≅ B.sheaf) → F A = F B

/-- ACTUAL finite tensor differences of an original integer line functional,
retaining every independently specified actual original line and test line. -/
def originalLineMixedDifference (F : IntrinsicLineBundle X → ℤ) :
    List (IntrinsicLineBundle X) → IntrinsicLineBundle X → ℤ
  | [], B => F B
  | A :: As, B => originalLineMixedDifference F As (originalLineTensor B A) -
      originalLineMixedDifference F As B

/-- Genuine actual original sheaf isomorphisms transport ALL these original
finite differences, by actual original tensor-isomorphism functoriality. -/
theorem originalLineMixedDifference_invariant (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) (As : List (IntrinsicLineBundle X))
    {B C : IntrinsicLineBundle X} (e : B.sheaf ≅ C.sheaf) :
    originalLineMixedDifference F As B = originalLineMixedDifference F As C := by
  induction As generalizing B C with
  | nil => exact hF B C e
  | cons A As ih =>
    exact congrArg₂ (fun x y : ℤ => x - y)
      (ih (B := originalLineTensor B A) (C := originalLineTensor C A)
        (bundleTensorIso e (Iso.refl A.sheaf))) (ih (B := B) (C := C) e)

/-- Pointwise genuine original integer identities transport through actual
finite tensor differences without a limit/polynomial/period premise. -/
theorem originalLineMixedDifference_congr_function (F G : IntrinsicLineBundle X → ℤ)
    (h : ∀ B, F B = G B) (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalLineMixedDifference F As B = originalLineMixedDifference G As B := by
  induction As generalizing B with
  | nil => exact h B
  | cons A As ih =>
    exact congrArg₂ (fun x y : ℤ => x - y) (ih (originalLineTensor B A)) (ih B)

/-- Swap TWO distinct original tensor differences by the actual original
three-line sheaf isomorphism, with no commutation conclusion supplied. -/
theorem originalLineMixedDifference_swap (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) (A C : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalLineMixedDifference F (A :: C :: As) B =
      originalLineMixedDifference F (C :: A :: As) B := by
  have h := originalLineMixedDifference_invariant F hF As
    (B := originalLineTensor (originalLineTensor B A) C)
    (C := originalLineTensor (originalLineTensor B C) A)
    (originalLineTensorRightSwapIso B.atlas A.atlas C.atlas)
  change originalLineMixedDifference F As (originalLineTensor (originalLineTensor B A) C) -
      originalLineMixedDifference F As (originalLineTensor B A) -
      (originalLineMixedDifference F As (originalLineTensor B C) - originalLineMixedDifference F As B) =
    originalLineMixedDifference F As (originalLineTensor (originalLineTensor B C) A) -
      originalLineMixedDifference F As (originalLineTensor B C) -
      (originalLineMixedDifference F As (originalLineTensor B A) - originalLineMixedDifference F As B)
  omega

/-- The genuine FIRST actual original difference commutes through ALL the
remaining actual tensor differences, retaining the actual same test line. -/
theorem originalLineMixedDifference_commute_head (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) (A : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalLineMixedDifference F (A :: As) B =
      originalLineMixedDifference (fun B => F (originalLineTensor B A) - F B) As B := by
  induction As generalizing B with
  | nil => rfl
  | cons C As ih =>
    rw [originalLineMixedDifference_swap F hF A C As B]
    exact congrArg₂ (fun x y : ℤ => x - y) (ih (originalLineTensor B C)) (ih B)

variable (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- PURE ORIGINAL INTEGER mixed Euler differences: actual original line
sheaves/tensors and actual original chosen-cover section-complex Euler only.
This is not a definition of a source mixed number by a native integral or
polarization of a diagonal. Its scheme-intersection comparison is separate. -/
def originalMixedEulerDifference (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) : ℤ :=
  originalLineMixedDifference (fun C => originalProjectiveLineCechEuler f E C.sheaf) As B

/-- The genuine actual original Euler functional supplies its own full
isomorphism invariance, with no functional certificate input. -/
theorem originalProjectiveEuler_isomorphismInvariant :
    OriginalLineIsomorphismInvariant (fun C => originalProjectiveLineCechEuler f E C.sheaf) :=
  fun _ _ e => originalProjectiveLineCechEuler_eq_of_iso f E e

theorem originalMixedEulerDifference_invariant (As : List (IntrinsicLineBundle X))
    {B C : IntrinsicLineBundle X} (e : B.sheaf ≅ C.sheaf) :
    originalMixedEulerDifference f E As B = originalMixedEulerDifference f E As C :=
  originalLineMixedDifference_invariant _ (originalProjectiveEuler_isomorphismInvariant f E) As e

/-- The actual original distinct-line mixed Euler differences commute,
proved purely from actual original sheaf isomorphisms and integer arithmetic. -/
theorem originalMixedEulerDifference_swap (A C : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (A :: C :: As) B =
      originalMixedEulerDifference f E (C :: A :: As) B :=
  originalLineMixedDifference_swap _ (originalProjectiveEuler_isomorphismInvariant f E) A C As B

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
