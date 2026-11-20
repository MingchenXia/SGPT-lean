import SGPT.Projective.OriginalMixedEulerDifference
import SGPT.BDivisor.BD3CurveEulerTensorDifference
import Mathlib.Data.List.OfFn

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalMixedEulerCurveTerminal`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalMixedEulerCurveTerminal`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Genuine original line-direction transports and PURE ORIGINAL terminal
curve integer degree of mixed Euler operations; no native period.
Blueprint: original-mixed-euler-curve-terminal.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X : Scheme.{0}}

/-- Actual original sheaf isomorphisms of EACH line direction preserve the
ENTIRE genuine mixed operation; actual line tensor isos supply every transport. -/
theorem originalLineMixedDifference_congr_lines_bd3 (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) {As Cs : List (IntrinsicLineBundle X)}
    (h : List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) As Cs)
    (B : IntrinsicLineBundle X) :
    originalLineMixedDifference F As B = originalLineMixedDifference F Cs B := by
  induction h generalizing B with
  | nil => rfl
  | @cons A C As Cs he hrel ih =>
    obtain ⟨e⟩ := he
    have hfirst := (ih (originalLineTensor B A)).trans
      (originalLineMixedDifference_invariant F hF Cs
        (B := originalLineTensor B A) (C := originalLineTensor B C)
        (bundleTensorIso (Iso.refl B.sheaf) e))
    exact congrArg₂ (fun x y : ℤ => x - y) hfirst (ih B)

private theorem originalLines_forall2_ofFn_bd3 (k : ℕ)
    (As Cs : Fin k → IntrinsicLineBundle X) (e : ∀ i, (As i).sheaf ≅ (Cs i).sheaf) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) (List.ofFn As) (List.ofFn Cs) := by
  induction k with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons ⟨e 0⟩ (ih (fun i => As i.succ) (fun i => Cs i.succ) (fun i => e i.succ))

/-- Actual original direction isomorphisms for EVERY finite index transport
the genuine finite list operations without equating different original sheaves. -/
theorem originalLineMixedDifference_congr_ofFn_bd3 (F : IntrinsicLineBundle X → ℤ)
    (hF : OriginalLineIsomorphismInvariant F) (k : ℕ)
    (As Cs : Fin k → IntrinsicLineBundle X) (e : ∀ i, (As i).sheaf ≅ (Cs i).sheaf)
    (B : IntrinsicLineBundle X) :
    originalLineMixedDifference F (List.ofFn As) B = originalLineMixedDifference F (List.ofFn Cs) B :=
  originalLineMixedDifference_congr_lines_bd3 F hF (originalLines_forall2_ofFn_bd3 k As Cs e) B

private theorem originalLineMixedDifference_const_base_bd3 (d : ℤ) (As : List (IntrinsicLineBundle X))
    (B C : IntrinsicLineBundle X) :
    originalLineMixedDifference (fun _ => d) As B = originalLineMixedDifference (fun _ => d) As C := by
  induction As generalizing B C with
  | nil => rfl
  | cons A As ih =>
    exact congrArg₂ (fun x y : ℤ => x - y)
      (ih (originalLineTensor B A) (originalLineTensor C A)) (ih B C)

/-- A nonempty genuine original tensor difference of a true constant integer functional is zero. -/
theorem originalLineMixedDifference_const_cons_bd3 (d : ℤ) (A : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalLineMixedDifference (fun _ => d) (A :: As) B = 0 :=
  sub_eq_zero.mpr (originalLineMixedDifference_const_base_bd3 d As (originalLineTensor B A) B)

variable (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

theorem originalMixedEulerDifference_congr_lines_bd3 {As Cs : List (IntrinsicLineBundle X)}
    (h : List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) As Cs)
    (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E As B = originalMixedEulerDifference f E Cs B :=
  originalLineMixedDifference_congr_lines_bd3 _ (originalProjectiveEuler_isomorphismInvariant f E) h B

theorem originalMixedEulerDifference_congr_ofFn_bd3 (k : ℕ)
    (As Cs : Fin k → IntrinsicLineBundle X) (e : ∀ i, (As i).sheaf ≅ (Cs i).sheaf)
    (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (List.ofFn As) B = originalMixedEulerDifference f E (List.ofFn Cs) B :=
  originalLineMixedDifference_congr_ofFn_bd3 _ (originalProjectiveEuler_isomorphismInvariant f E) k As Cs e B

variable [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

/-- The genuine ORIGINAL terminal one-difference on an ENTIRE original
smooth projective curve is the independent original INTEGER degree of the
SAME direction line, regardless of ANY accumulated original test-line twist. -/
theorem originalMixedEulerDifference_curve_singleton_bd3 (A B : IntrinsicLineBundle X)
    (p : Spec (.of ℂ)) :
    originalMixedEulerDifference f E [A] B = originalCurveLineDegree_bd3 f E A.atlas p :=
  originalWholeCurve_arbitraryLineEulerDifference_bd3 f E A.atlas B.atlas p

/-- TWO or more genuine original mixed Euler differences vanish on the
ENTIRE original curve, by the independent constant degree, before any Chern period. -/
theorem originalMixedEulerDifference_curve_two_cons_bd3 (A C : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) (p : Spec (.of ℂ)) :
    originalMixedEulerDifference f E (A :: C :: As) B = 0 := by
  let F : IntrinsicLineBundle X → ℤ := fun B => originalProjectiveLineCechEuler f E B.sheaf
  change originalLineMixedDifference F (A :: C :: As) B = 0
  rw [originalLineMixedDifference_commute_head F (originalProjectiveEuler_isomorphismInvariant f E)]
  have hconst (B : IntrinsicLineBundle X) : F (originalLineTensor B A) - F B =
      originalCurveLineDegree_bd3 f E A.atlas p :=
    originalWholeCurve_arbitraryLineEulerDifference_bd3 f E A.atlas B.atlas p
  exact (originalLineMixedDifference_congr_function _ _ hconst (C :: As) B).trans
    (originalLineMixedDifference_const_cons_bd3 (originalCurveLineDegree_bd3 f E A.atlas p) C As B)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
