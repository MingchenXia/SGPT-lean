import SGPT.Projective.OkounkovOriginalBookAnalyticHCP
import SGPT.Projective.OkounkovOriginalHCPZero

/-! Whole original analytic twisted Hausdorff theorem with actual raw domain, every dimension.
Blueprint: okounkov-original-analytic-hcp-all-dimensions.tex. -/
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
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance analyticHCPAllTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance analyticHCPAllCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance analyticHCPAllManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual positive original I-volume ensures the SAME raw twisted multiplier polytopes are eventually defined compact bodies. -/
theorem eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v) (c : X)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ᶠ k : ℕ in atTop,
      (AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ).Nonempty ∧
      IsCompact (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ) k) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let Q (k : ℕ) := AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ
  let V : ℝ := (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
    ((m+1).factorial:ℝ)
  have hfinite := original_iVolume_ne_top_allDimensions f (m+1) E a H hφ
  have hV : 0<V := div_pos (ENNReal.toReal_pos hpos.ne' hfinite) (by exact_mod_cast Nat.factorial_pos (m+1))
  have hcount := OriginalMultiplierAsymptotics.tendsto_normalized_twistedMultiplierValues_card
    f E a H hbig v hv c aT r hφ
  filter_upwards [(tendsto_order.mp hcount).1 0 hV] with k hk
  have hQ : (Q k).Nonempty := by
    by_contra he
    have hempty : Q k=∅ := not_nonempty_iff_eq_empty.mp he
    change 0<(k:ℝ)⁻¹^(m+1)*(Nat.card (Q k):ℝ) at hk
    simp only [hempty,Nat.card_eq_fintype_card,Fintype.card_ofIsEmpty,Nat.cast_zero,mul_zero] at hk
    exact lt_irrefl _ hk
  have hQfin := (OriginalTwistedMultiplierCount.twistedMultiplierValues_finite_card
    f E a hbig v hv c k (r k) hφ.1.quasiPlurisubharmonic).1
  exact ⟨hQ,(hQfin.image (fun x => (k:ℝ)⁻¹ • euclideanCast (m+1) x)).isCompact_convexHull ℝ⟩

/-- FULL source lma:twistedHcp for SAME original objects, arbitrary valuation, own body, ALL dimensions. -/
theorem tendsto_twistedMultiplierPolytope_analytic_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f n E L)
    (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact; HasManifoldAnalyticSingularityType (n:=n) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      (∀ᶠ k : ℕ in atTop,
        IsCompact (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k) ∧
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k).Nonempty) ∧
      Tendsto (fun k : ℕ => Metric.hausdorffDist
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f n E v (valuationCenter f v) k (r k) φ) k)
        (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)) atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  cases n with
  | zero =>
    obtain ⟨hKc,hKv,heq,hlim⟩ := twistedMultiplierPolytope_eq_partialBody_zeroDimension
      f E a H v (valuationCenter f v) r (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)
    refine ⟨hKc,hKv,?_,hlim⟩
    have : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 0)) := inferInstance
    exact Eventually.of_forall fun k =>
      ⟨(Set.toFinite _).isCompact,by
        have hne : (univ : Set (EuclideanSpace ℝ (Fin 0))).Nonempty := ⟨0,mem_univ _⟩
        have hpoly : (poly (fun k => AlgebraicValuation.twistedMultiplierValues f 0 E v (valuationCenter f v) k (r k) φ) k) ≠ ∅ := by
          intro hempty
          have hhaus := heq k
          have hset : (poly (fun k => AlgebraicValuation.twistedMultiplierValues f 0 E v (valuationCenter f v) k (r k) φ) k).Nonempty := by
            obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
            have h1 : ((0:Fin 0 → ℝ),(1:ℝ))∈(SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone := by
              refine ⟨zero_le_one,0,?_,by simp⟩
              rw [PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a (valuationCenter f v) v]
              exact mem_univ _
            rw [hhaus,PobDimZero.valuation_partialBody_eq_univ f E Y hY a (valuationCenter f v) v
              (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ).quasiPshPotential _ h1]
            exact hne
          exact hset.ne_empty hempty
        exact nonempty_iff_ne_empty.mpr hpoly⟩
  | succ m =>
    obtain ⟨hKc,hKv,hlim⟩ := tendsto_twistedMultiplierPolytope_analytic_positiveDimension f E a aT H hbig v hv r hφ hφan
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
    have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
    have hpos := (PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hθ).trans_le
      (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f (m+1) E) hθ)
    have hdomain := eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
      f E a aT H hbig v hv (valuationCenter f v) r hθ hpos
    refine ⟨hKc,hKv,?_,hlim⟩
    filter_upwards [hdomain] with k hk
    exact ⟨hk.2,(hk.1.image _).convexHull⟩
end SGPT.Okounkov.OriginalBook
