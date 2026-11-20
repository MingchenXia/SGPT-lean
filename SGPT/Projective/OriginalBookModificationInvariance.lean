import SGPT.Projective.OriginalModificationZeroPullback
import SGPT.Projective.OriginalModificationBodyComparison

/-! Entire original prop:birinvO in ALL dimensions and original arbitrary valuations.
The book's compact modification is the GIVEN finite smooth-centre blowup sequence;
actual analytic modification and target Kahler geometry are produced internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.AlmostSemigroup
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology ENNReal

private theorem original_nonempty {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) : Nonempty (SchemeComplexPoint f) := by
  have := E.locallyOfFiniteType
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  obtain ⟨P, hP⟩ := Ideal.exists_maximal Γ(X, U)
  obtain ⟨p, _⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P hP
  exact ⟨p⟩

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance modificationBookTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance modificationBookCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance modificationBookManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance modificationBookMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance modificationBookBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- Entire printed original modification invariance, canonical original centre and ALLn0.
Book compact modifications are finite smooth-centre blowup sequences (conventions13,
chapter_Okounkov389, appendix_unibranch70); no extra target Kahler or output certificate. -/
theorem modification_partialBody_invariant_allDimensions
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      BlowupSequences.IsBlowupSequence n (SchemeComplexPoint f) Z π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      letI : Nonempty (SchemeComplexPoint f) := original_nonempty f E;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    let c := valuationCenter f v
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      OriginalModification.AllDimensions.pullbackBody f n E a v c
        (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) π φ =
      ValGen.partialBody f n E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := original_nonempty f E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let c := valuationCenter f v
  cases n with
  | zero =>
    have hbig := original_isBig_of_positive_iVolume_allDimensions f 0 E a H hφ hpos
    obtain ⟨hKc,hKv,_,_,_⟩ :=
      sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a 0 E hbig v hv c
    exact ⟨hKc,hKv,OriginalModification.Zero.pullbackBody_eq_partialBody f E a H hφ π v c _⟩
  | succ m =>
    have hmod : IsAnalyticModification (n := m+1) π :=
      HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
    obtain ⟨_, N', Ψ', hΨ'⟩ := SGPT.GAGA.ChowBl.exists_isHolomorphicEmbedding_of_isBlowupSequence
      (SGPT.GAGA.H0S.isHolomorphicEmbedding_projectivePoint f E (m+1)) hseq
    obtain ⟨omegaZ⟩ := SGPT.GAGA.TowerAlg.nonempty_kahlerBackground_of_isHolomorphicEmbedding hΨ'
    obtain ⟨hKc,hKv,hbody⟩ := OriginalModification.exists_pullbackBody_eq_of_kahler
      f E a H v c hmod omegaZ hφ hv hpos
    refine ⟨hKc,hKv,?_⟩
    rw [OriginalModification.AllDimensions.pullbackBody_succ]
    exact hbody

end SGPT.Okounkov.OriginalBook
