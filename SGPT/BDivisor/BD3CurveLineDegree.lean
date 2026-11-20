import SGPT.Projective.OriginalHyperplaneFractionalDegree
import SGPT.BDivisor.BD3SerreCurveSections
/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalCurveLineDegree`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalCurveLineDegree`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Independent ORIGINAL integral structural degree of ANY original line,
ordinary Serre numerator/denominator manufactured; no metric in definitions.
Blueprint: original-curve-line-degree.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L)

include a in
/-- Actual original Serre ordinary numerator/denominator, no physical metric or section input. -/
theorem exists_originalHyperplaneFractionalPresentation_bd3 :
    Nonempty (OriginalHyperplaneFractionalPresentation f E L) := by
  obtain ⟨M, hM, s, t, hs, ht⟩ := exists_originalHyperplaneTwist_sections_bd3 f E a
  exact ⟨⟨M, hM, s, t, hs, ht⟩⟩

/-- Ordinary actual ORIGINAL fractional presentation manufactured from actual original algebraic geometry. -/
def originalCurveLinePresentation_bd3 : OriginalHyperplaneFractionalPresentation f E L :=
  Classical.choice (exists_originalHyperplaneFractionalPresentation_bd3 f E a)

/-- PURE original signed structural integral degree; no physical metric, period or tensor-power division. -/
def originalCurveLineDegree_bd3 : AlgebraicCycle (Spec (.of ℂ)) ℤ :=
  (originalCurveLinePresentation_bd3 f E a).degree a

local instance actualLineDegreeTopology_bd3 : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance actualLineDegreeCharts_bd3 (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance actualLineDegreeManifold_bd3 (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

theorem originalCurveLineDegree_eq_ChernPeriod_bd3 (H : SchemeLineBundleMetric f 1 E L)
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((originalCurveLineDegree_bd3 f E a p : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) :=
  originalHyperplaneFractionalDegree_eq_ChernPeriod f E a H (originalCurveLinePresentation_bd3 f E a) p κ

theorem originalCurveLineDegree_eq_fractionalPresentation_bd3 (H : SchemeLineBundleMetric f 1 E L)
    (P : OriginalHyperplaneFractionalPresentation f E L) (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E a p = P.degree a p :=
  originalHyperplaneFractionalDegree_independent f E a H (originalCurveLinePresentation_bd3 f E a) P p

theorem originalCurveLineDegree_independent_atlas_bd3 (b : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f 1 E L) (p : Spec (.of ℂ)) :
    originalCurveLineDegree_bd3 f E a p = originalCurveLineDegree_bd3 f E b p := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let A := originalHyperplanePositiveLine f 1 E
  let κ : KahlerBackground 1 (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  have ha := originalCurveLineDegree_eq_ChernPeriod_bd3 f E a H p κ
  have hb := originalCurveLineDegree_eq_ChernPeriod_bd3 f E b H p κ
  have hp : slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature b)) := by
    apply slotIntegral_eq_of_bottChernRel
    intro i
    fin_cases i
    exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq (H.curvature_atlas_geometricallyEq a b)
  exact_mod_cast ha.trans (hp.trans hb.symm)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
