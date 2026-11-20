import SGPT.Projective.OkounkovOriginalAnalyticHCPAllDimensions
import SGPT.Projective.OkounkovOriginalKahlerApproximationBodies
import SGPT.Projective.OkounkovOuterApproximationControl

/-! Genuine original HCP for arbitrary Kähler-current singularities, SAME raw Q/own partial body.
Blueprint: okounkov-original-book-kahler-hcp.tex. General positive-I-volume HCP remains separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance bookKahlerHCPTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookKahlerHCPCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookKahlerHCPManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual original raw HCP for ANY Kähler-current weight, no analytic-singularity premise. -/
theorem tendsto_twistedMultiplierPolytope_kahler_positiveDimension
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
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
  obtain ⟨hKc,hKv,U,hU,hle,hUlim⟩ := exists_original_kahler_approximation_partialBody_limit f E a H hbig v hv hφ
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let K := ValGen.partialBody f (m+1) E v c a C φ
  let F (j : ℕ) := ValGen.partialBody f (m+1) E v c a C (U j)
  obtain ⟨hKc₁,hKv₁,hKcompact,hKconv,hKnonempty,hKvolume⟩ :=
    OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry f E a H hbig v hv c hφ
  have hFgeom (j : ℕ) : IsCompact (F j) ∧ (F j).Nonempty := by
    obtain ⟨hKcj,hKvj,hFc,hFv,hFn,hFvol⟩ :=
      OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry f E a H hbig v hv c (hU.2 j).2
    exact ⟨hFc,hFn⟩
  let Q (ψ : SchemeComplexPoint f → EReal) (k : ℕ) :=
    AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) ψ
  let P (j k : ℕ) := poly (Q (U j)) k
  have hP (j : ℕ) : (∀ᶠ k : ℕ in atTop, IsCompact (P j k) ∧ (P j k).Nonempty) ∧
      Tendsto (fun k => Metric.hausdorffDist (P j k) (F j)) atTop (𝓝 0) := by
    obtain ⟨hKcj,hKvj,hdom,hlim⟩ := tendsto_twistedMultiplierPolytope_analytic_allDimensions
      f (m+1) E a aT H hbig v hv r (hU.2 j).2 (hU.1.2.1 j)
    exact ⟨hdom,hlim⟩
  let R (k : ℕ) := (fun x => (k:ℝ)⁻¹ • euclideanCast (m+1) x) '' Q φ k
  have hRP (j : ℕ) : ∀ᶠ k : ℕ in atTop, R k ⊆ P j k := by
    apply Eventually.of_forall
    intro k y hy
    obtain ⟨x,⟨s,hs,hI,hx⟩,rfl⟩ := hy
    have hθj := (hU.2 j).1.1
    have horder := iOrderOnManifold_of_le hθj.1.quasiPlurisubharmonic (hle j)
    have hxj : x∈Q (U j) k := by
      refine ⟨s,hs,?_,hx⟩
      rcases hI with hk | hI
      · exact Or.inl hk
      · by_cases hk0 : k=0
        · exact Or.inl hk0
        · refine Or.inr fun V α p hp => ?_
          exact SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold horder
            (by exact_mod_cast Nat.pos_of_ne_zero hk0) p _ (hI V α p hp)
    exact subset_convexHull ℝ _ (mem_image_of_mem _ hxj)
  have hnear := OuterApproximationControl.eventually_near_of_compact_outer_limits hKcompact hKnonempty
    F (fun j => (hFgeom j).1) (fun j => (hFgeom j).2) hUlim P
      (fun j => (hP j).1.mono (fun _ hk => ⟨hk.2,hk.1.isBounded⟩)) (fun j => (hP j).2) R hRP
  let e := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm
  let B := e.symm '' K
  have heB : e '' B=K := by dsimp only [B]; rw [←image_comp]; simp
  have hBc : IsCompact B := hKcompact.image e.symm.continuous
  have hBv : Convex ℝ B := hKconv.linear_image e.symm.toLinearMap
  have hvolImage : volume (e '' B)=volume B := PartialBody.volume_euclideanImage B
  have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  let V : ℝ := (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ).toReal /
    ((m+1).factorial:ℝ)
  have hvolB : volume.real B=V := by
    rw [measureReal_def,←hvolImage,heB]
    have hKvol : volume K=iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hθ /
      ((m+1).factorial:ℝ≥0∞) := hKvolume
    rw [hKvol,ENNReal.toReal_div,ENNReal.toReal_natCast]
  have hpos := (PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hθ).trans_le
    (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f (m+1) E) hθ)
  have hfinite := original_iVolume_ne_top_allDimensions f (m+1) E a H hθ
  have hVpos : 0<V := div_pos (ENNReal.toReal_pos hpos.ne' hfinite) (by exact_mod_cast Nat.factorial_pos (m+1))
  have hcount : Tendsto (fun k : ℕ => (k:ℝ)⁻¹^(m+1)*(Nat.card (Q φ k):ℝ)) atTop (𝓝 (volume.real B)) := by
    rw [hvolB]
    exact OriginalMultiplierAsymptotics.tendsto_normalized_twistedMultiplierValues_card f E a H hbig v hv c aT r hθ
  have hup : ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop, ∀ x∈Q φ k,
      ∃ z∈e '' B, dist (e ((k:ℝ)⁻¹ • Counting.integerCast x)) z≤η := by
    intro η hη
    filter_upwards [hnear η hη] with k hk x hx
    obtain ⟨z,hz,hd⟩ := hk _ ⟨x,hx,rfl⟩
    refine ⟨z,heB.symm ▸ hz,?_⟩
    rw [map_smul]
    change dist ((k:ℝ)⁻¹ • euclideanCast (m+1) x) z≤η
    exact hd
  have hlim := FiniteValueHausdorff.tendsto_hausdorffDist_of_euclidean_upper_and_count
    hBc hBv (hvolB ▸ hVpos) (Q φ) hup hcount
  refine ⟨hKc,hKv,?_⟩
  change Tendsto (fun k : ℕ => Metric.hausdorffDist
    ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ''
      convexHull ℝ ((fun x => (k:ℝ)⁻¹ • Counting.integerCast x) '' Q φ k)) (e '' B)) atTop (𝓝 0) at hlim
  rw [heB] at hlim
  simpa only [image_convexHull_eq_poly] using hlim

/-- The same genuine original Kähler-current raw HCP in EVERY original dimension. -/
theorem tendsto_twistedMultiplierPolytope_kahler_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f n E L)
    (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      Tendsto (fun k : ℕ => Metric.hausdorffDist
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k)
        (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ))
        atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  cases n with
  | zero =>
    obtain ⟨hKc,hKv,heq,hlim⟩ := twistedMultiplierPolytope_eq_partialBody_zeroDimension
      f E a H v (valuationCenter f v) r (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)
    exact ⟨hKc,hKv,hlim⟩
  | succ m => exact tendsto_twistedMultiplierPolytope_kahler_positiveDimension f E a aT H hbig v hv r hφ
end SGPT.Okounkov.OriginalBook
