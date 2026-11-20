import SGPT.Projective.OkounkovOriginalBookHCPPositive
import SGPT.Projective.OkounkovOriginalHCPZero

/-! ENTIRE printed thm:HCP, original arbitrary valuation/twist, actual I-volume domain, EVERY dimension.
Blueprint: okounkov-original-book-hcp.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance bookGeneralHCPTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookGeneralHCPCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookGeneralHCPManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- ENTIRE original thm:HCP including true eventual raw domain, canonical actual centre, arbitrary valuation and n0. -/
theorem tendsto_twistedMultiplierPolytope_general_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      (∀ᶠ k : ℕ in atTop,
        IsCompact (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k) ∧
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k).Nonempty) ∧
      Tendsto (fun k : ℕ => Metric.hausdorffDist
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k)
        (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
        atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  cases n with
  | zero =>
    let c := valuationCenter f v
    obtain ⟨hKc,hKv,heq,hlim⟩ := twistedMultiplierPolytope_eq_partialBody_zeroDimension f E a H v c r hφ
    obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
    have hA := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a c v
    let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
    have h1 : ((0:Fin 0 → ℝ),(1:ℝ))∈C.cone :=
      ⟨zero_le_one,0,by rw [hA]; exact mem_univ _,by simp⟩
    have hbody : ValGen.partialBody f 0 E v c a C φ=univ :=
      PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential C h1
    refine ⟨hKc,hKv,Eventually.of_forall (fun k => ?_),hlim⟩
    rw [heq k,hbody]
    exact ⟨isCompact_univ,⟨0,mem_univ _⟩⟩
  | succ m =>
    exact tendsto_twistedMultiplierPolytope_general_positiveDimension f E a aT H v hv r hφ hpos
end SGPT.Okounkov.OriginalBook
