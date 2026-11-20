import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.ValGenInfty
import SGPT.Okounkov.PobDimZeroCore

/-! ENTIRE prop:GammaepsSp, SAME actual original raw infinity set/own-body cone, ALL dimensions.
Blueprint: okounkov-original-book-infty.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X)
include E hbig hv

/-- ENTIRE original analytic-singularity source statement, no cone/group/flag premise, including n0. -/
theorem inftySectionSet_mem_ownBody_fullSemigroupLocus_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n:=n) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hSI : AlgebraicValuation.inftySectionSet f n E v c a φ ⊆
        (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set ((Fin n → ℤ) × ℤ))),
      (⟨_,hSI⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
      Tendsto (ConeSubset.normalizedCardinality (⟨_,hSI⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)))
        atTop (𝓝 ((DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal / (n.factorial:ℝ))) ∧
      ConeSubset.volume (⟨_,hSI⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) =
        (DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal / (n.factorial:ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  obtain ⟨hKc,hKv,_,hSL,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a n E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := hfull.2
  have hSI : AlgebraicValuation.inftySectionSet f n E v c a φ ⊆
      (latticePoints C.cone : Set ((Fin n → ℤ) × ℤ)) :=
    fun _ hz => hSL (AlgebraicValuation.inftySectionSet_subset a φ hz)
  refine ⟨hKc,hKv,hSI,?_⟩
  cases n with
  | succ m =>
    exact ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v hSL hG hφ hφan
  | zero =>
    have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
    have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
    have heq := PobDimZero.valuation_inftySectionSet_eq f E Y hY a c v hφθ.quasiPshPotential
    have hN : PobDimZero.nonnegHeight ≤ latticePoints C.cone := by
      intro z hz
      exact hSI (heq.symm ▸ hz)
    have hUeq : (⟨_,hSI⟩ : ConeSubset C) = sourceSubset C PobDimZero.nonnegHeight hN :=
      Subtype.ext heq
    change (⟨_,hSI⟩ : ConeSubset C) ∈ fullSemigroupLocus C ∧
      Tendsto (ConeSubset.normalizedCardinality (⟨_,hSI⟩ : ConeSubset C)) atTop
        (𝓝 ((DiagonalMass.diagonalPotentialMass (H.curvature a) φ hφθ).toReal / ((0:ℕ).factorial:ℝ))) ∧
      ConeSubset.volume (⟨_,hSI⟩ : ConeSubset C) =
        (DiagonalMass.diagonalPotentialMass (H.curvature a) φ hφθ).toReal / ((0:ℕ).factorial:ℝ)
    rw [hUeq,PobDimZero.diagonalPotentialMass_eq_one (H.curvature a) hφθ]
    simp only [ENNReal.toReal_one,Nat.factorial_zero,Nat.cast_one,div_one]
    exact ⟨PobDimZero.sourceSubset_nonnegHeight_mem_fullSemigroupLocus C hN,
      PobDimZero.tendsto_normalizedCardinality_nonnegHeight C hN,
      PobDimZero.volume_sourceSubset_nonnegHeight C hN⟩

end SGPT.Okounkov.OriginalBook
