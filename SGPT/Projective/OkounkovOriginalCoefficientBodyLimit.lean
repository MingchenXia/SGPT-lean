import SGPT.Projective.OkounkovConvexLeftNativeLimit
import SGPT.Projective.OkounkovOriginalRationalKahlerConcavity
import SGPT.Projective.OkounkovOriginalBookOrderContinuity

/-! Genuine native coefficient limits and SAME original arbitrary-valuation body continuity.
Blueprint: okounkov-original-coefficient-body-limit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance coefficientBodyLimitTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance coefficientBodyLimitCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance coefficientBodyLimitManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_partialBody_left_coefficient_limit_kahler {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) ψ)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) {I : Type*} (F : Filter I) (s : I → ℝ)
    (hs : ∀i, 0<s i ∧ s i<t) (hlim : Tendsto s F (𝓝 t)) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsKahlerCurrentPotential (H.curvature a) (convexComb t φ ψ) ∧
      (∀i,IsKahlerCurrentPotential (H.curvature a) (convexComb (s i) φ ψ)) ∧
      Tendsto (fun i => Metric.hausdorffDist
        (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb (s i) φ ψ))
        (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb t φ ψ)))
        F (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
  let θ := H.curvature a
  let omega := schemeProjectiveTNKahlerBackground f (m+1) E
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hψθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψ
  have hconv (r : ℝ) (hr0 : 0<r) (hr1 : r<1) :
      IsKahlerCurrentPotential θ (convexComb r φ ψ) := by
    have hh := TranscendentalCore.isKahlerCurrentPotential_add_smul hφ hψθ hr0 (sub_nonneg.mpr hr1.le)
    have hf : r•θ+(1-r)•θ=θ := by module
    rwa [hf] at hh
  have hχ := hconv t ht0 ht1
  have hχθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hχ
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφθ
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E a H hφ)
  obtain ⟨hclass,hKc,hKv,horder,hcont⟩ :=
    exists_common_ownBody_order_continuous_partialBody_allDimensions f (m+1) E a H hbig v hv
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hclass).toUniformSpace.toTopologicalSpace
  obtain ⟨G,hG,hreader⟩ := hcont
  let w : {w : ThetaPshL1 θ.val // HasPositivePotentialMass θ w.val w.property} :=
    ⟨⟨convexComb t φ ψ,hχθ⟩,PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hχ hχθ⟩
  let U : I → {w : ThetaPshL1 θ.val // HasPositivePotentialMass θ w.val w.property} := fun i =>
    ⟨⟨convexComb (s i) φ ψ,PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential
      (hconv (s i) (hs i).1 ((hs i).2.trans ht1))⟩,
      PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential
        (hconv (s i) (hs i).1 ((hs i).2.trans ht1)) _⟩
  have hnative : Tendsto (fun i => (U i).val) F (𝓝 w.val) :=
    ConvexLeftNativeLimit.tendsto_native_convexComb_from_left omega θ hclass hφθ hψθ ht0 ht1 F s hs hlim
  have hUlim : Tendsto U F (𝓝 w) := tendsto_subtype_rng.mpr hnative
  have hd := tendsto_iff_dist_tendsto_zero.mp ((hG.tendsto w).comp hUlim)
  change Tendsto (fun i => Metric.hausdorffDist
    ((G (U i)) : Set (EuclideanSpace ℝ (Fin (m+1))))
    ((G w) : Set (EuclideanSpace ℝ (Fin (m+1))))) F (𝓝 0) at hd
  refine ⟨hKc,hKv,hχ,(fun i => hconv (s i) (hs i).1 ((hs i).2.trans ht1)),?_⟩
  simpa only [hreader,U,w,θ] using hd
end SGPT.Okounkov.OriginalBook
