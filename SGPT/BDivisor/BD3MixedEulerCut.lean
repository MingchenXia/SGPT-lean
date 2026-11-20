import SGPT.Projective.OriginalMixedEulerPullback
import SGPT.Projective.OriginalCICutEuler
import SGPT.BDivisor.BD3CurveEulerDegree
/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalMixedEulerCut`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalMixedEulerCut`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Genuine SAME-original-CI-cut recursion for independent original INTEGER
mixed Euler differences. Blueprint: original-mixed-euler-cut.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- GENUINE arbitrary distinct-line mixed Euler cut recursion. Primitive
original regularity is the only cutting condition; all original Cartier
Euler identities, actual whole-zero restriction and tensor transports are
proved, with SAME original sheaves/section/map and unchanged affine cover. -/
theorem originalRegularSection_mixedEuler_restriction_bd3
    (A : IntrinsicLineBundle X) (s : Γ(A.sheaf, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation A.sheaf s V))
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (A :: As) B =
      originalMixedEulerDifference (sectionZeroι A.atlas s ≫ f) (E.sectionZero A.atlas s)
        (As.map (originalLinePullback (sectionZeroι A.atlas s)))
        (originalLinePullback (sectionZeroι A.atlas s) (originalLineTensor B A)) := by
  let g := sectionZeroι A.atlas s
  let FX : IntrinsicLineBundle X → ℤ := fun B => originalProjectiveLineCechEuler f E B.sheaf
  let FD : IntrinsicLineBundle (sectionZeroSubscheme A.atlas s) → ℤ :=
    fun B => originalProjectiveLineCechEuler (g ≫ f) (E.sectionZero A.atlas s) B.sheaf
  let FG : IntrinsicLineBundle X → ℤ := fun B => FD (originalLinePullback g B)
  have hFX : OriginalLineIsomorphismInvariant FX := originalProjectiveEuler_isomorphismInvariant f E
  have hFD : OriginalLineIsomorphismInvariant FD :=
    originalProjectiveEuler_isomorphismInvariant (g ≫ f) (E.sectionZero A.atlas s)
  have hFG : OriginalLineIsomorphismInvariant FG := originalLinePullback_function_invariant g FD hFD
  have hOne (B : IntrinsicLineBundle X) : FX (originalLineTensor B A) - FX B =
      FG (originalLineTensor B A) := by
    have h := originalTwistedCartierEuler_eq_restricted f E A.atlas B.atlas s hinj
    change FX (originalLineTensor B A) = FX B + FG (originalLineTensor B A) at h
    omega
  change originalLineMixedDifference FX (A :: As) B =
    originalLineMixedDifference FD (As.map (originalLinePullback g))
      (originalLinePullback g (originalLineTensor B A))
  calc
    _ = originalLineMixedDifference (fun B => FX (originalLineTensor B A) - FX B) As B :=
      originalLineMixedDifference_commute_head FX hFX A As B
    _ = originalLineMixedDifference (fun B => FG (originalLineTensor B A)) As B :=
      originalLineMixedDifference_congr_function _ _ hOne As B
    _ = originalLineMixedDifference FG As (originalLineTensor B A) :=
      originalLineMixedDifference_twist_base FG hFG A As B
    _ = _ := originalLineMixedDifference_pullback g FD hFD As (originalLineTensor B A)

local instance mixedCutPointTopology_bd3 : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance mixedCutPointCharts_bd3 (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance mixedCutPointManifold_bd3 (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsSeparated f] [QuasiCompact f] : IsComplexManifold d (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f d

variable (n : ℕ) [SmoothOfRelativeDimension (n + 1) f] [IsSeparated f] [QuasiCompact f]
    (P : OriginalPositiveLine f (n + 1) E) (C : OriginalRegularCut f n E P)

/-- ONLY the SAME actual original cutting positive-power sheaf and original
power atlas. No regularity, Euler, degree or period comparison field. -/
def originalCICutLine_bd3 : IntrinsicLineBundle X where
  sheaf := bundleTensorPower P.sheaf C.nativeCut.power
  atlas := P.atlas.tensorPower C.nativeCut.power

/-- For ANY fixed actual original algebraic/native CI cut, its own original
section PRODUCES ALL required regularity, and the genuine original mixed
Euler difference is the SAME mixed Euler operation on its ENTIRE original
zero scheme with all remaining original lines literally pulled there.
No regularity/exactness/Euler/degree/period/tensor-comparison input. -/
theorem originalCICut_mixedEuler_restriction_bd3
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (originalCICutLine_bd3 f E n P C :: As) B =
      originalMixedEulerDifference (C.inclusion ≫ f) C.embedding
        (As.map (originalLinePullback C.inclusion))
        (originalLinePullback C.inclusion (originalLineTensor B (originalCICutLine_bd3 f E n P C))) :=
  originalRegularSection_mixedEuler_restriction_bd3 f E (originalCICutLine_bd3 f E n P C)
    C.originalSection (originalCICut_dualEvaluation_injective f n E P C) As B

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
