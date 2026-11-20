import SGPT.Projective.OkounkovOriginalGeneralUpperPoints
import SGPT.NAPotential.FSPosKahler

/-! Actual positive-dimension ENTIRE original HCP, arbitrary valuation, only positive ORIGINAL I-volume.
Blueprint: okounkov-original-book-hcp-positive.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open SGPT.NAPotential.FSPos
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance bookHCPPositiveTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookHCPPositiveCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookHCPPositiveManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Genuine original HCP, all raw degrees and arbitrary original twist/valuation, positive ORIGINAL I-volume. -/
theorem tendsto_twistedMultiplierPolytope_general_positiveDimension
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
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
        IsCompact (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) k (r k) φ) k) ∧
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) k (r k) φ) k).Nonempty) ∧
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
  let c := valuationCenter f v
  let aA := hyperplaneAtlas E
  let K₀ := fubiniStudyMetric f E (m+1)
  let P : SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) :=
    { power := 1
      power_pos := one_pos
      ambientDimension := E.ambientDimension
      map := E.map
      isClosedImmersion := E.closedImmersion
      over_base := E.over_base
      iso := bundleTensorLeftUnitIso (hyperplaneBundle E) }
  obtain ⟨hKc,hKv,hnear⟩ := exists_general_original_twisted_values_eventually_near_partialBody
    f E a aT H aA P K₀ (fubiniStudy_curvature_isKahler f (m+1) E) v hv r hφ hpos
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let K := ValGen.partialBody f (m+1) E v c a C φ
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφ hpos
  obtain ⟨hKc₁,hKv₁,hsub,hΓ,hvol,hbody,hKvolume⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f (m+1) E a H hbig v hv c hφ hpos
  have hKcompact : IsCompact K := ValGen.isCompact_setBody _ _
  have hKconv : Convex ℝ K := ValGen.convex_setBody _ _
  let Q := fun (ψ : SchemeComplexPoint f → EReal) (k : ℕ) =>
    AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) ψ
  let e := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm
  let B := e.symm '' K
  have heB : e '' B=K := by dsimp only [B]; rw [←image_comp]; simp
  have hBc : IsCompact B := hKcompact.image e.symm.continuous
  have hBv : Convex ℝ B := hKconv.linear_image e.symm.toLinearMap
  have hvolImage : volume (e '' B)=volume B := PartialBody.volume_euclideanImage B
  have hθ := hφ
  let V : ℝ := (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ).toReal /
    ((m+1).factorial:ℝ)
  have hvolB : volume.real B=V := by
    rw [measureReal_def,←hvolImage,heB]
    have hKvol : volume K=iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ /
      ((m+1).factorial:ℝ≥0∞) := hKvolume
    rw [hKvol,ENNReal.toReal_div,ENNReal.toReal_natCast]
  have hfinite := original_iVolume_ne_top_allDimensions f (m+1) E a H hθ
  have hVpos : 0<V := div_pos (ENNReal.toReal_pos hpos.ne' hfinite) (by exact_mod_cast Nat.factorial_pos (m+1))
  have hcount : Tendsto (fun k : ℕ => (k:ℝ)⁻¹^(m+1)*(Nat.card (Q φ k):ℝ)) atTop (𝓝 (volume.real B)) := by
    rw [hvolB]
    exact OriginalMultiplierAsymptotics.tendsto_normalized_twistedMultiplierValues_card f E a H hbig v hv c aT r hθ
  have hup : ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop, ∀ x∈Q φ k,
      ∃ z∈e '' B, dist (e ((k:ℝ)⁻¹ • Counting.integerCast x)) z≤η := by
    intro η hη
    filter_upwards [hnear η hη] with k hk x hx
    obtain ⟨z,hz,hd⟩ := hk x hx
    refine ⟨z,heB.symm ▸ hz,?_⟩
    rw [map_smul]
    change dist ((k:ℝ)⁻¹ • euclideanCast (m+1) x) z≤η
    exact hd
  have hlim := FiniteValueHausdorff.tendsto_hausdorffDist_of_euclidean_upper_and_count
    hBc hBv (hvolB ▸ hVpos) (Q φ) hup hcount
  have hdom := eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    f E a aT H hbig v hv c r hφ hpos
  refine ⟨hKc,hKv,?_,?_⟩
  · filter_upwards [hdom] with k hk
    exact ⟨hk.2,(hk.1.image _).convexHull⟩
  · change Tendsto (fun k : ℕ => Metric.hausdorffDist
      ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ''
        convexHull ℝ ((fun x => (k:ℝ)⁻¹ • Counting.integerCast x) '' Q φ k)) (e '' B)) atTop (𝓝 0) at hlim
    rw [heB] at hlim
    simpa only [image_convexHull_eq_poly] using hlim
end SGPT.Okounkov.OriginalBook
