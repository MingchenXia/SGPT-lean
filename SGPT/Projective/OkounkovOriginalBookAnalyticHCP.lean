import SGPT.Projective.OkounkovOriginalAnalyticUpperPoints
import SGPT.Projective.OkounkovFiniteValueHausdorff
import SGPT.Projective.OkounkovOriginalTwistedMultiplierAsymptotics

/-! Actual raw original analytic twisted multiplier polytopes converge to their SAME own-cone partial body.
Blueprint: okounkov-original-book-analytic-hcp.tex. Positive-dimensional source endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance bookAnalyticHCPTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookAnalyticHCPCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance bookAnalyticHCPManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Genuine analytic source Hausdorff limit for arbitrary original valuations and original twists, positive dimension. -/
theorem tendsto_twistedMultiplierPolytope_analytic_positiveDimension {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact; HasManifoldAnalyticSingularityType (n:=m+1) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      Tendsto (fun k : ℕ => Metric.hausdorffDist
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) k (r k) φ) k)
        (ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
        atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
  let c := valuationCenter f v
  have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨hKc,hKv,hupper⟩ := OriginalAnalyticUpperPoints.exists_analytic_twisted_values_eventually_near_partialBody
    f E a aT H hbig v hv r hφ hφan
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let K := ValGen.partialBody f (m+1) E v c a C φ
  obtain ⟨hKc₁,hKv₁,hKcompact,hKconv,hKnonempty,hKvolume⟩ :=
    OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry f E a H hbig v hv c hφ
  obtain ⟨hKc₂,hKv₂,hbody,hdegree⟩ :=
    OriginalInftyBodyLimit.infty_body_eq_partialBody_and_degree_limit f E a H hbig v hv c hφ hφan
  let e := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm
  let B := body (ValGen.inftySemigroup f E a c v φ)
  have heB : e '' B = K := hbody
  have hB : B = e.symm '' K := by rw [←heB]; simp only [←image_comp]; simp
  have hBc : IsCompact B := by rw [hB]; exact hKcompact.image e.symm.continuous
  have hBv : Convex ℝ B := by rw [hB]; exact hKconv.linear_image e.symm.toLinearMap
  have hvolImage : volume (e '' B) = volume B := PartialBody.volume_euclideanImage B
  let V : ℝ := (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ).toReal /
    ((m+1).factorial:ℝ)
  have hvolB : volume.real B = V := by
    rw [measureReal_def,←hvolImage,heB]
    have hKvolume' : volume K = iVolume (H.curvature a)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ / ((m+1).factorial:ℝ≥0∞) := hKvolume
    rw [hKvolume',ENNReal.toReal_div,ENNReal.toReal_natCast]
  have hpos := (PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hθ).trans_le
    (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f (m+1) E) hθ)
  have hfinite := original_iVolume_ne_top_allDimensions f (m+1) E a H hθ
  have hVpos : 0<V := div_pos (ENNReal.toReal_pos hpos.ne' hfinite) (by exact_mod_cast Nat.factorial_pos (m+1))
  let Q (k : ℕ) := AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ
  have hcount : Tendsto (fun k : ℕ => (k:ℝ)⁻¹^(m+1)*(Nat.card (Q k):ℝ)) atTop (𝓝 (volume.real B)) := by
    rw [hvolB]
    exact OriginalMultiplierAsymptotics.tendsto_normalized_twistedMultiplierValues_card f E a H hbig v hv c aT r hθ
  have hup : ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop, ∀ x∈Q k,
      ∃ z∈e '' B, dist (e ((k:ℝ)⁻¹ • Counting.integerCast x)) z ≤ η := by
    intro η hη
    filter_upwards [hupper η hη] with k hk x hx
    obtain ⟨z,hz,hd⟩ := hk x hx
    refine ⟨z,heB.symm ▸ hz,?_⟩
    rw [map_smul]
    change dist ((k:ℝ)⁻¹ • euclideanCast (m+1) x) z ≤ η
    exact hd
  have hlim := FiniteValueHausdorff.tendsto_hausdorffDist_of_euclidean_upper_and_count
    hBc hBv (hvolB ▸ hVpos) Q hup hcount
  refine ⟨hKc,hKv,?_⟩
  change Tendsto (fun k : ℕ => Metric.hausdorffDist
    ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ''
      convexHull ℝ ((fun x => (k:ℝ)⁻¹ • Counting.integerCast x) '' Q k)) (e '' B)) atTop (𝓝 0) at hlim
  rw [heB] at hlim
  simpa only [image_convexHull_eq_poly] using hlim
end SGPT.Okounkov.OriginalBook
