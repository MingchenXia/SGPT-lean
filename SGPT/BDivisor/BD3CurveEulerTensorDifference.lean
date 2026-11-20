import SGPT.BDivisor.BD3CurveEulerDegree
import SGPT.Projective.OriginalLineTensorArithmetic

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalCurveEulerTensorDifference`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalCurveEulerTensorDifference`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: PURE original whole-curve Euler tensor increments and integer degree
additivity for arbitrary original lines, before ANY native Chern period.
Blueprint: original-curve-euler-tensor-difference.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

/-- ANY original line increments the original Euler characteristic of ANY
other actual original line by its independent original INTEGER degree.
All actual Serre sections/zeros/lengths are produced; no metric/period input. -/
theorem originalWholeCurve_arbitraryLineEulerDifference_bd3 {L B : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas B) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler f E (bundleTensor B L) -
        originalProjectiveLineCechEuler f E B = originalCurveLineDegree_bd3 f E a p := by
  let P := originalCurveLinePresentation_bd3 f E a
  let d := (hyperplaneAtlas E).tensorPower P.exponent
  let c := pairwiseTensorAtlas a d
  have hS := originalWholeCurve_twistedEuler_eq_sectionZeroDegree_bd3 f E c b
    P.numerator P.numerator_nonzero p
  have hT := originalWholeCurve_twistedEuler_eq_sectionZeroDegree_bd3 f E d (b.tensor a)
    P.denominator P.denominator_nonzero p
  have hAssoc := originalProjectiveLineCechEuler_eq_of_iso f E
    (originalLineTensorAssociatorIso b a d)
  change originalProjectiveLineCechEuler f E (bundleTensor B L) -
    originalProjectiveLineCechEuler f E B = P.degree a p
  change originalProjectiveLineCechEuler f E (bundleTensor B L) -
    originalProjectiveLineCechEuler f E B =
      wholeCurveSectionZeroCycleDegree f E c P.numerator P.numerator_nonzero p -
        wholeCurveSectionZeroCycleDegree f E d P.denominator P.denominator_nonzero p
  omega

/-- PURE original integer degree is additive for ANY two actual original
lines, arbitrary actual tensor atlas, all original curve components/empty retained. -/
theorem originalCurveLineDegree_tensor_add_algebraic_bd3 {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (c : LineBundleAtlas (bundleTensor L N))
    (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E c p =
      originalCurveLineDegree_bd3 f E a p + originalCurveLineDegree_bd3 f E b p := by
  have hN := originalWholeCurve_arbitraryLineEulerDifference_bd3 f E b a p
  have hL := originalCurveLineDegree_eq_eulerDifference_bd3 f E a p
  have hLN := originalCurveLineDegree_eq_eulerDifference_bd3 f E c p
  omega

/-- The actual ORIGINAL unit line has degree zero without any metric/period. -/
theorem originalCurveLineDegree_unit_zero_algebraic_bd3
    (a : LineBundleAtlas (SheafOfModules.unit X.ringCatSheaf)) (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E a p = 0 := by
  rw [originalCurveLineDegree_eq_eulerDifference_bd3]
  exact sub_self _

/-- Genuine ORIGINAL power scaling of the independent INTEGER degree of
ANY original line, including power zero; no common-power descent premise. -/
theorem originalCurveLineDegree_tensorPower_algebraic_bd3 {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E (a.tensorPower m) p = (m : ℤ) * originalCurveLineDegree_bd3 f E a p := by
  induction m with
  | zero =>
    exact (originalCurveLineDegree_unit_zero_algebraic_bd3 f E (a.tensorPower 0) p).trans (by simp)
  | succ m ih =>
    have h := originalCurveLineDegree_tensor_add_algebraic_bd3 f E
      (a.tensorPower m) a (a.tensorPower (m + 1)) p
    rw [h, ih]
    push_cast
    ring

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
