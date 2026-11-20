import SGPT.Projective.WholeCurveChernNative
import SGPT.IGood.DXMainTensorMetric
import SGPT.Projective.OriginalSectionZeroCycle

/-! Independent ENTIRE original zero-minus-pole cycle and structural
degree of an ordinary original tensor-section quotient.
Blueprint: original-fractional-section-cycle.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open NefMixedMass
open scoped BigOperators

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L N : X.Modules} (c : LineBundleAtlas (bundleTensor L N)) (b : LineBundleAtlas N)
  (s : Γ(bundleTensor L N, ⊤)) (hs : SectionNonzeroOnComponents f E s)
  (t : Γ(N, ⊤)) (ht : SectionNonzeroOnComponents f E t)

/-- Actual signed original zero cycle, independent of any physical metric or analytic period. -/
def originalFractionalSectionCycle : AlgebraicCycle X ℤ := by
  let := wholeCurveSectionZero_isArtinian f E c s hs
  let := wholeCurveSectionZero_isArtinian f E b t ht
  exact originalSectionZeroAmbientCycle c s - originalSectionZeroAmbientCycle b t

/-- Actual original structural signed zero-minus-pole degree, before any period comparison. -/
def originalFractionalSectionDegree : AlgebraicCycle (Spec (.of ℂ)) ℤ :=
  wholeCurveSectionZeroCycleDegree f E c s hs - wholeCurveSectionZeroCycleDegree f E b t ht

theorem originalFractionalSectionCycle_support_finite :
    (Function.support (originalFractionalSectionCycle f E c b s hs t ht)).Finite := by
  let := wholeCurveSectionZero_isArtinian f E c s hs
  let := wholeCurveSectionZero_isArtinian f E b t ht
  exact ((originalSectionZeroAmbientCycle_support_finite c s).union
    (originalSectionZeroAmbientCycle_support_finite b t)).subset (Function.support_sub _ _)

theorem originalFractionalSectionDegree_eq_finsum (p : Spec (.of ℂ)) :
    originalFractionalSectionDegree f E c b s hs t ht p =
      ∑ᶠ x : X, originalFractionalSectionCycle f E c b s hs t ht x := by
  let := wholeCurveSectionZero_isArtinian f E c s hs
  let := wholeCurveSectionZero_isArtinian f E b t ht
  change artinianStructuralPushforward (E.sectionZero c s) p -
    artinianStructuralPushforward (E.sectionZero b t) p =
    ∑ᶠ x : X, (originalSectionZeroAmbientCycle c s x - originalSectionZeroAmbientCycle b t x)
  rw [originalSectionZeroStructuralDegree_eq_finsum c s f E p,
    originalSectionZeroStructuralDegree_eq_finsum b t f E p]
  exact (finsum_sub_distrib (originalSectionZeroAmbientCycle_support_finite c s)
    (originalSectionZeroAmbientCycle_support_finite b t)).symm

local instance fractionalTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance fractionalCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance fractionalManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

theorem originalFractionalSectionDegree_eq_ChernPeriod (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f 1 E L) (K : SchemeLineBundleMetric f 1 E N)
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((originalFractionalSectionDegree f E c b s hs t ht p : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have hS := wholeCurveSectionZeroCycleDegree_eq_ChernPeriod f E c (H.tensorProduct K a b) s hs p κ
  have hT := wholeCurveSectionZeroCycleDegree_eq_ChernPeriod f E b K t ht p κ
  have hgeo := H.curvature_tensorProduct K a b c
  have hperiod : slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i)
      ((H.tensorProduct K a b).curvature c)) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a + K.curvature b)) := by
    apply slotIntegral_eq_of_bottChernRel
    intro i
    fin_cases i
    exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo
  have hconst (theta : ClosedRealOneOneForm 1 (SchemeComplexPoint f)) :
      (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) theta : Fin 1 → _) = fun _ => theta := by
    funext i
    fin_cases i
    rfl
  change ((wholeCurveSectionZeroCycleDegree f E c s hs p -
    wholeCurveSectionZeroCycleDegree f E b t ht p : ℤ) : ℝ) = _
  rw [Int.cast_sub, hS, hT, hperiod, hconst, hconst, hconst]
  have hadd := (slotIntegralMultilinear κ).map_update_add (fun _ => κ.form) 0
    (H.curvature a) (K.curvature b)
  simp only [slotIntegralMultilinear, MultilinearMap.mk'_apply] at hadd
  have hupdate (theta : ClosedRealOneOneForm 1 (SchemeComplexPoint f)) :
      Function.update (fun _ : Fin 1 => κ.form) 0 theta = fun _ => theta := by
    funext i
    fin_cases i
    simp
  simp only [hupdate] at hadd
  rw [hadd, add_sub_cancel_right]

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
