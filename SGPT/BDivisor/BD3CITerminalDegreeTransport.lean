import SGPT.BDivisor.BD3CurveEulerDegree
import SGPT.Projective.WholeOriginalAlgebraicCI

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalCITerminalDegreeTransport`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalCITerminalDegreeTransport`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Genuine original sheaf-isomorphism and actual composite-embedding
transports for independent ORIGINAL terminal integer degrees.
Blueprint: original-ci-terminal-degree-transport.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

/-- PURE actual original integer degree is invariant under a genuine
original sheaf iso, by original integer Euler/degree arithmetic alone. -/
theorem originalCurveLineDegree_eq_of_sheafIso_bd3 {L M : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas M) (e : L ≅ M) (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E a p = originalCurveLineDegree_bd3 f E b p := by
  rw [originalCurveLineDegree_eq_eulerDifference_bd3, originalCurveLineDegree_eq_eulerDifference_bd3,
    originalProjectiveLineCechEuler_eq_of_iso f E e]

omit [IsSeparated f] [QuasiCompact f] in
/-- The actual original identity-curve embedding is the SAME original embedding. -/
theorem originalCurveOver_identity_embedding_bd3 :
    let C : OriginalCurveOver f :=
      { source := X, structureMap := f, inclusion := 𝟙 X, over_base := Category.id_comp f,
        closed := inferInstance, smooth := inferInstance }
    C.embedding E = E := by
  cases E
  simp only [OriginalCurveOver.embedding, Category.id_comp]

section Composite
variable {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (EY : ClosedProjectiveEmbedding g)
    {L : Y.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (Z : OriginalCurveOver (sectionZeroι a s ≫ g))

/-- The SAME original total CI embedding and iterated SAME original cut
embedding agree by the ACTUAL scheme-map associativity square. -/
theorem originalCurveOver_composite_embedding_bd3 :
    let R : OriginalCurveOver g :=
      { source := Z.source, structureMap := Z.structureMap,
        inclusion := Z.inclusion ≫ sectionZeroι a s,
        over_base := by rw [Category.assoc, Z.over_base],
        closed := inferInstance, smooth := Z.smooth }
    R.embedding EY = Z.embedding (EY.sectionZero a s) := by
  simp only [OriginalCurveOver.embedding, ClosedProjectiveEmbedding.sectionZero, Category.assoc]

end Composite
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
