import SGPT.Projective.OkounkovOriginalBookInfty
import SGPT.AlmostSemigroup.OkounkovExtension

/-! Actual classical original Γ∞ body equals partial body, and its GENUINE semigroup degree polytopes converge.
Blueprint: okounkov-original-infty-body-limit.tex. No raw multiplier-polytope conclusion is inferred from distance zero. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalInftyBodyLimit
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open SGPT.AlmostSemigroup.OkounkovExtension SGPT.AlmostSemigroup.Okounkov
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance inftyBodyLimitTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance inftyBodyLimitCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance inftyBodyLimitManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original full Γ∞ geometry, body identification and true Γ∞ degree limits with ALL producers internal. -/
theorem infty_body_eq_partialBody_and_degree_limit {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v) (c : X)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact; HasManifoldAnalyticSingularityType (n:=m+1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ''
          body (ValGen.inftySemigroup f E a c v φ) =
        ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ ∧
      Tendsto (fun k : ℕ => Metric.hausdorffDist
          (BodyGeometry.euclideanDegreeBody (ValGen.inftySemigroup f E a c v φ) k)
          (ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
        atTop (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨hKc,hKv,-,hSL,hfull⟩ :=
    OriginalBook.sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hG := hfull.2
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  let Γ := ValGen.inftySemigroup f E a c v φ
  have hΓC : Γ≤latticePoints C.cone := ValGen.inftySemigroup_le_cone f E a H c v hSL hφθ
  have hΓfull := (ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v hSL hG hφ hφan).1
  let S : FullSemigroup C := ⟨sourceSubset C Γ hΓC,hΓfull⟩
  have hT := (ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_analytic
    f E Y hY a H c v hSL hG hφ hφan).1
  let T : AlmostSpace C := ⟨ValGen.multiplierConeSubset f E a c v hSL φ,hT⟩
  have hzero : dist (fullToAlmost S) T=0 :=
    ValGen.dist_inftySemigroup_multiplierConeSubset_eq_zero f E Y hY a H c v hSL hG hφ hφan
  have hext : bodyExtension (fullToAlmost S)=bodyExtension T :=
    ((Metric.inseparable_iff.mpr hzero).map (continuous_bodyExtension C)).eq
  have hbody : (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm '' body Γ =
      ValGen.partialBody f (m+1) E v c a C φ := by
    calc
      _ = (bodyMap S : Set (EuclideanSpace ℝ (Fin (m+1)))) := rfl
      _ = (bodyExtension (fullToAlmost S) : Set (EuclideanSpace ℝ (Fin (m+1)))) :=
        congrArg (fun B : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) =>
          (B:Set (EuclideanSpace ℝ (Fin (m+1))))) (bodyExtension_source S).symm
      _ = (bodyExtension T : Set (EuclideanSpace ℝ (Fin (m+1)))) :=
        congrArg (fun B : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) =>
          (B:Set (EuclideanSpace ℝ (Fin (m+1))))) hext
      _ = _ := (ValGen.partialBody_eq a φ _ hT).symm
  refine ⟨hKc,hKv,hbody,?_⟩
  have hlim := BodyGeometry.tendsto_hausdorffDist_degreeBody C Γ hΓC S.generatedGroup_eq_top
  change Tendsto (fun k => Metric.hausdorffDist (BodyGeometry.euclideanDegreeBody Γ k)
    ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm '' body Γ)) atTop (𝓝 0) at hlim
  rw [hbody] at hlim
  exact hlim

end SGPT.Okounkov.OriginalInftyBodyLimit
