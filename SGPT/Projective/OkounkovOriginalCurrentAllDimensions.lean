import SGPT.Projective.OkounkovOriginalBookCurrent
import SGPT.Projective.OkounkovOriginalCurrentZero

/-! ENTIRE prop:Okocurrent, actual canonical original center, genuine native positive current / unconditional n0.
Blueprint: okounkov-original-current-all-dimensions.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent SGPT.Okounkov.AlgebraicValuation
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance currentAllDimensionsTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance currentAllDimensionsCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance currentAllDimensionsManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- ENTIRE current invariance at the ACTUAL original canonical center, native positive current and unconditional n0. -/
theorem centrePartialBodies_ownCones_eq_of_current_eq_allDimensions {L L' : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas L') (K : SchemeLineBundleMetric f n E L')
    (hbig : SGPT.LineBundle.IsBig f L n) (hbig' : SGPT.LineBundle.IsBig f L' n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (K.curvature b).val ψ)
    (hcur : letI := E.isSeparated; letI := E.quasiCompact;
      (by
        cases n with
        | zero => exact True
        | succ m => exact (thetaPotentialCurrent (H.curvature a).val φ hφ =
            thetaPotentialCurrent (K.curvature b).val ψ hψ) : Prop))
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hAc : IsCompact (centreOkounkovBody f v a)) (hAv : Convex ℝ (centreOkounkovBody f v a))
      (hBc : IsCompact (centreOkounkovBody f v b)) (hBv : Convex ℝ (centreOkounkovBody f v b)),
      centreOkounkovBody f v a = centreOkounkovBody f v b ∧
      0 < iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ ∧
      ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ =
        ValGen.partialBody f n E v (valuationCenter f v) b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) ψ := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  have hc := isNonnegAt_valuationCenter f v
  cases n with
  | zero =>
    obtain ⟨hAc,hAv,hBc,hBv,hbody,-,hvol,hpartial⟩ :=
      partialBodies_ownCones_eq_zeroDimension f E a H b K v c hφ hψ
    exact ⟨hAc,hAv,hBc,hBv,hbody,by rw [hvol]; exact zero_lt_one,hpartial⟩
  | succ m =>
    exact partialBodies_ownCones_eq_of_current_eq_positiveDimension f E a H b K hbig hbig' v hv c hc
      hφ hψ hcur hpos

end SGPT.Okounkov.OriginalBook
