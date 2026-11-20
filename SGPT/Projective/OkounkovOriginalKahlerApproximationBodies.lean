import SGPT.Projective.OkounkovOriginalBookPartial
import SGPT.AlmostSemigroup.OkounkovExtension

/-! Actual Kähler QEA and SAME arbitrary-valuation original partial-body limit, all producers internal.
Blueprint: okounkov-original-kahler-approximation-bodies.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance kahlerApproximationBodiesTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance kahlerApproximationBodiesCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance kahlerApproximationBodiesManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original Kähler approximation and genuine same-own-cone body convergence for arbitrary valuations. -/
theorem exists_original_kahler_approximation_partialBody_limit {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (U : ℕ → SchemeComplexPoint f → EReal) (_hU : PartialBody.IsKahlerQEA (H.curvature a) φ U),
      (∀ j, φ≤U j) ∧
      Tendsto (fun j => Metric.hausdorffDist
        (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (U j))
        (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
        atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨hKc,hKv,hKi,hS,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbig v hv (valuationCenter f v)
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let c := valuationCenter f v
  have hG := hfull.2
  let θ := H.curvature a
  let F := schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨U,hU⟩ := PartialBody.exists_isKahlerQEA hφ
  have hUK : ∀ j, IsKahlerCurrentPotential θ (U j) := fun j => (hU.2 j).2
  have hUθ : ∀ j, IsThetaPshPotential θ.val (U j) := fun j =>
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hUK j)
  have hd := hU.1.2.2.1
  have hle : ∀ j, φ≤U j := fun j x => (hd.1 x).le_of_tendsto (hd.2 x) j
  let K (j : ℕ) := PartialBody.generalPartialBody F θ (U j)
  have hKφ : PartialBody.generalPartialBody F θ φ = ⋂ j, K j := by
    rw [PartialBody.generalPartialBody_eq_kahlerPartialBody hφ,
      PartialBody.kahlerPartialBody_eq_kahlerPartialBodyOf hU,PartialBody.kahlerPartialBodyOf]
    exact iInter_congr fun j =>
      (PartialBody.generalPartialBody_eq_analyticPartialBody (hU.2 j).1 (hUK j)).symm
  have hanti : Antitone K := by
    intro i j hij
    change PartialBody.generalPartialBody F θ (U j) ⊆ PartialBody.generalPartialBody F θ (U i)
    rw [PartialBody.generalPartialBody_eq_kahlerPartialBody (hUK j),
      PartialBody.generalPartialBody_eq_kahlerPartialBody (hUK i)]
    exact (PartialBody.kahlerPartialBody_subset_of_iOrder (hUK j) (hUK i)
      (iOrderOnManifold_of_le (hUθ i).1.quasiPlurisubharmonic
        (show U j ≤ U i from fun x => by have hh := hd.1 x hij; exact hh))).1
  have hKcompact (j : ℕ) : IsCompact (K j) :=
    (PartialBody.convex_isCompact_generalPartialBody (F:=F) (hUθ j)).2
  let V := volume.real (PartialBody.generalPartialBody F θ φ)
  have hvolK : Tendsto (fun j => volume.real (K j)) atTop (𝓝 V) := by
    have hh := tendsto_measure_iInter_atTop (μ := (volume : Measure (Fin (m+1) → ℝ)))
      (fun j => (hKcompact j).isClosed.measurableSet.nullMeasurableSet) hanti
      ⟨0,(hKcompact 0).measure_lt_top.ne⟩
    rw [←hKφ] at hh
    exact (ENNReal.tendsto_toReal ((PartialBody.convex_isCompact_generalPartialBody (F:=F) hφθ).2.measure_lt_top.ne)).comp hh
  let S : AlmostSpace C := ⟨ValGen.multiplierConeSubset f E a c v hS φ,
    (ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_kahler f E Y hY a H c v hS hG hφ).1⟩
  let T (j : ℕ) : AlmostSpace C := ⟨ValGen.multiplierConeSubset f E a c v hS (U j),
    (ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_analytic f E Y hY a H c v hS hG
      (hUK j) (hU.1.2.1 j)).1⟩
  have hcountφ := ValGen.tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφθ
  have hdist (j : ℕ) : dist (T j) S = volume.real (K j)-V := by
    change dist (ValGen.multiplierConeSubset f E a c v hS (U j)) (ValGen.multiplierConeSubset f E a c v hS φ) = _
    rw [dist_comm]
    exact ValGen.dist_multiplierConeSubset_eq_of_subset f E a c v hS
      (ValGen.multiplierSectionSet_mono_of_le f E a c v (hUθ j).1.quasiPlurisubharmonic (hle j)) hcountφ
      (ValGen.tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG (hUθ j))
  have hTlim : Tendsto T atTop (𝓝 S) := tendsto_iff_dist_tendsto_zero.mpr (by
    simp only [hdist]
    simpa only [sub_self] using hvolK.sub_const V)
  have hbodylim := tendsto_iff_dist_tendsto_zero.mp ((continuous_bodyExtension C).tendsto S |>.comp hTlim)
  change Tendsto (fun j => Metric.hausdorffDist
    ((bodyExtension (T j)) : Set (EuclideanSpace ℝ (Fin (m+1))))
    ((bodyExtension S) : Set (EuclideanSpace ℝ (Fin (m+1))))) atTop (𝓝 0) at hbodylim
  have hTreader (j : ℕ) : ((bodyExtension (T j)) : Set (EuclideanSpace ℝ (Fin (m+1)))) =
      ValGen.partialBody f (m+1) E v c a C (U j) := (ValGen.partialBody_eq a (U j) _ (T j).property).symm
  have hSreader : ((bodyExtension S) : Set (EuclideanSpace ℝ (Fin (m+1)))) =
      ValGen.partialBody f (m+1) E v c a C φ := (ValGen.partialBody_eq a φ _ S.property).symm
  refine ⟨hKc,hKv,U,hU,hle,?_⟩
  simpa only [hTreader,hSreader,C,c,centreOkounkovBody] using hbodylim
end SGPT.Okounkov.OriginalBook
