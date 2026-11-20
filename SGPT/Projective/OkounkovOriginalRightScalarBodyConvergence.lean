import SGPT.Projective.OkounkovNativeRightScalarConvergence
import SGPT.Projective.OkounkovOriginalBookOrderContinuity

/-! Actual own-body partial-body convergence under true native scalar weight approximation, arbitrary original valuation.
Blueprint: okounkov-original-right-scalar-body-convergence.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open ThetaPshL1Topology SingularCanonicalSingularityDistance DiagonalMass
open SGPT.Okounkov.AlgebraicValuation
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance rightScalarBodyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rightScalarBodyCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance rightScalarBodyManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- ONE actual own-body cone, true scaled current positivity and actual Hausdorff body convergence, no certificates. -/
theorem exists_right_scalar_partialBody_convergence {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (r₁ : ℝ), 1<r₁ ∧
      (∀ q : Ioo (1:ℝ) r₁, IsKahlerCurrentPotential (H.curvature a) (fun x => (q.val:EReal)*φ x)) ∧
      ∀ (I : Type*) (F : Filter I) (q : I → Ioo (1:ℝ) r₁), Tendsto (fun i => (q i).val) F (𝓝 1) →
        Tendsto (fun i => Metric.hausdorffDist
          (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)
            (fun x => ((q i).val:EReal)*φ x))
          (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
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
  obtain ⟨hclass,hKc,hKv,-,hcont⟩ := exists_common_ownBody_order_continuous_partialBody_allDimensions
    f (m+1) E a H hbig v hv
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hclass).toUniformSpace.toTopologicalSpace
  obtain ⟨G,hGc,hG⟩ := hcont
  obtain ⟨r₁,hr1,hscalar,hconv⟩ := NativeRightScalarConvergence.exists_right_scalar_native_convergence omega θ hclass hφ
  refine ⟨hKc,hKv,r₁,hr1,hscalar,?_⟩
  intro I F q hq
  let U : I → ThetaPshL1 θ.val := fun i => ⟨fun x => ((q i).val:EReal)*φ x,
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hscalar (q i))⟩
  let w : ThetaPshL1 θ.val := ⟨φ,PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ⟩
  have hU : Tendsto U F (𝓝 w) := hconv I F q hq
  have hw : HasPositivePotentialMass θ w.val w.property :=
    PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ w.property
  have hm (i : I) : HasPositivePotentialMass θ (U i).val (U i).property :=
    PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential (hscalar (q i)) (U i).property
  let V : I → {u : ThetaPshL1 θ.val // HasPositivePotentialMass θ u.val u.property} := fun i => ⟨U i,hm i⟩
  let W : {u : ThetaPshL1 θ.val // HasPositivePotentialMass θ u.val u.property} := ⟨w,hw⟩
  have hV : Tendsto V F (𝓝 W) := tendsto_subtype_rng.mpr hU
  have hlim := (tendsto_iff_dist_tendsto_zero.mp ((hGc.tendsto W).comp hV))
  change Tendsto (fun i => Metric.hausdorffDist
    ((G (V i)) : Set (EuclideanSpace ℝ (Fin (m+1))))
    ((G W) : Set (EuclideanSpace ℝ (Fin (m+1))))) F (𝓝 0) at hlim
  simpa only [hG] using hlim

end SGPT.Okounkov.OriginalBook
