import SGPT.Projective.OriginalFractionalSectionCycle
import SGPT.Projective.OriginalProjectivePositiveLine

/-! PURE original integral structural degree of actual ordinary hyperplane
fractions. SAME original L, no metric/period in the degree definition.
Blueprint: original-hyperplane-fractional-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open NefMixedMass

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]

/-- ONLY ordinary actual original algebraic fraction data, retaining EVERY original component. -/
structure OriginalHyperplaneFractionalPresentation (L : X.Modules) where
  exponent : ℕ
  positiveExponent : 0 < exponent
  numerator : Γ(bundleTensor L (bundleTensorPower (hyperplaneBundle E) exponent), ⊤)
  denominator : Γ(bundleTensorPower (hyperplaneBundle E) exponent, ⊤)
  numerator_nonzero : SectionNonzeroOnComponents f E numerator
  denominator_nonzero : SectionNonzeroOnComponents f E denominator

namespace OriginalHyperplaneFractionalPresentation
variable {f E} {L : X.Modules}

/-- The genuine original signed ambient zero-minus-pole cycle, no metric or analytic input. -/
def cycle (P : OriginalHyperplaneFractionalPresentation f E L) (a : LineBundleAtlas L) :
    AlgebraicCycle X ℤ :=
  originalFractionalSectionCycle f E (pairwiseTensorAtlas a ((hyperplaneAtlas E).tensorPower P.exponent))
    ((hyperplaneAtlas E).tensorPower P.exponent) P.numerator P.numerator_nonzero
    P.denominator P.denominator_nonzero

/-- PURE ORIGINAL structural integral degree, no physical metric, period or power division. -/
def degree (P : OriginalHyperplaneFractionalPresentation f E L) (a : LineBundleAtlas L) :
    AlgebraicCycle (Spec (.of ℂ)) ℤ :=
  originalFractionalSectionDegree f E (pairwiseTensorAtlas a ((hyperplaneAtlas E).tensorPower P.exponent))
    ((hyperplaneAtlas E).tensorPower P.exponent) P.numerator P.numerator_nonzero
    P.denominator P.denominator_nonzero

end OriginalHyperplaneFractionalPresentation

local instance hyperplaneDegreeTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance hyperplaneDegreeCharts (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance hyperplaneDegreeManifold (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

theorem originalHyperplaneFractionalDegree_eq_ChernPeriod {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
    (P : OriginalHyperplaneFractionalPresentation f E L)
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((P.degree a p : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) :=
  originalFractionalSectionDegree_eq_ChernPeriod f E
    (pairwiseTensorAtlas a ((hyperplaneAtlas E).tensorPower P.exponent))
    ((hyperplaneAtlas E).tensorPower P.exponent) P.numerator P.numerator_nonzero
    P.denominator P.denominator_nonzero a H
    ((fubiniStudyMetric f E 1).tensorPower (hyperplaneAtlas E) P.exponent) p κ

theorem originalHyperplaneFractionalDegree_independent {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
    (P Q : OriginalHyperplaneFractionalPresentation f E L) (p : Spec (.of ℂ)) :
    P.degree a p = Q.degree a p := by
  let A := originalHyperplanePositiveLine f 1 E
  let κ : KahlerBackground 1 (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  have hP := originalHyperplaneFractionalDegree_eq_ChernPeriod f E a H P p κ
  have hQ := originalHyperplaneFractionalDegree_eq_ChernPeriod f E a H Q p κ
  exact_mod_cast hP.trans hQ.symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
