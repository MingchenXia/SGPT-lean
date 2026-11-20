import SGPT.Bergman.Quant2AlgebraicBM
import SGPT.Bergman.SourceConcaveLiminfDerivatives
import SGPT.Bergman.SourcePartialDonaldsonConcavity
import SGPT.Bergman.SourcePerturbedSupComparison

/-!
# Weak convergence of partial Bergman measures: analytic singularities

Source `prop:weakconvana` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 1178--1208).

Let `(K,v)` be a weighted subset, `μ ∈ BM(K,v)` and `φ ∈ PSH(X,θ)`, `θ = c₁(L,h)`, with analytic
singularities such that `θ_φ` is a Kähler current. The book proves
`β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_I(v)} = θⁿ_{P_{θ,K}[φ](v)}` by differentiating
`f_k(t) = L_{k,φ}(N^k_{v+tw,μ})` (concave, `f_k'(0) = ∫ w dβ^k_{v,φ,μ}`) and
`g(t) = E^φ_{θ,K}(v+tw)` (`prop:differential_P`) and applying `lma:conc_lim_der`.

As in the existing corrected-secant consumer `SGPT.Bergman.CorrectedSecant`, we use the lower
approximants `a_k(t) = L_{k,φ}(N^k_{v+tw,K}) ≤ f_k(t)`, whose limits `g(t)` are `eq:Lkconv`
(`Lkconv`) for the weighted subsets `(K, v+tw)`, together with `lma:BML` at `t = 0`; this avoids
the Bernstein--Markov property of `μ` for the perturbed weights `v + tw` (which the book uses).

The equality `θⁿ_{P_{θ,K}[φ]_I(v)} = θⁿ_{P_{θ,K}[φ](v)}` is proved unconditionally; the weak
convergence assumes the lower-bound half `RiemannRochLowerBound` of `thm:DXmain1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant2

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.PartialDonaldson SGPT.Bergman.QuantizationFrontier
open SGPT.Bergman.IGoodPartialEnvelope SGPT.Bergman.CorrectedSecant
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

omit [BorelSpace X] [ConnectedSpace X] in
/-- The Monge--Ampère measure depends only on the potential. -/
theorem sourcePotentialNonPluripolarMeasure_congr
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u v : X → EReal}
    (huv : u = v) (hu : (ofFixedModel n X).IsThetaPSH θ u)
    (hv : (ofFixedModel n X).IsThetaPSH θ v) :
    sourcePotentialNonPluripolarMeasure θ u hu = sourcePotentialNonPluripolarMeasure θ v hv := by
  subst huv
  rfl

/-- Source `prop:weakconvana`, equality part: for `φ` with analytic singularities and `θ_φ` a
Kähler current, `P_{θ,K}[φ]_I(v) = P_{θ,K}[φ](v)` (`cor:I-good_partial_env`, analytic
singularities being `I`-good). -/
theorem weakconvana_envelopes (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    partialIEnvelope (chernForm L hL) φ W.carrier W.erealWeight =
      partialEnvelope (chernForm L hL) φ W.carrier W.erealWeight := by
  obtain ⟨hφ, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hA : HasManifoldAnalyticSingularityType (n := n) φ :=
    hasRationalAnalyticType_iff_chartType.mp han
  have hgoodWith := SGPT.IGood.LogVolume.sourceIGoodWith_of_analytic omega hφ hA hφpos
  have hgood := (sourceIGood_iff_with_positive_background omega hφ hφpos).mpr hgoodWith
  obtain ⟨R, _hR, hRb⟩ := SGPT.Bergman.WeightedSubset.WeightedSubset.exists_real_abs_bound W
  exact partialIEnvelope_eq_partialEnvelope_of_iGood omega hφ hφpos hgood W.carrier W.erealWeight
    ⟨-R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hRb x)).1⟩

/-- Source `prop:weakconvana`: for a weighted subset `(K,v)`, `μ ∈ BM(K,v)` and `φ` with analytic
singularities such that `θ_φ` is a Kähler current, assuming the lower-bound half
`RiemannRochLowerBound` of `thm:DXmain1`,
`∫_X w dβ^k_{v,φ,μ} → ∫_X w dθⁿ_{P_{θ,K}[φ]_I(v)}` for every `w ∈ C⁰(X)`, and
`θⁿ_{P_{θ,K}[φ]_I(v)} = θⁿ_{P_{θ,K}[φ](v)}`. -/
theorem weakconvana
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ W.carrier W.erealWeight
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) := by
  intro θ P PI
  obtain ⟨hφ, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI :=
    (partialIEnvelope_eInfinity_continuous omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  have hEq : PI = P := weakconvana_envelopes omega L hL hcurrent han W
  have hP : (ofFixedModel n X).IsThetaPSH θ P := hEq ▸ hPI
  refine ⟨hP, hPI, sourcePotentialNonPluripolarMeasure_congr hEq hPI hP, fun w => ?_⟩
  let u : C(W.carrier, ℝ) := sourceBergmanTestRestriction W w
  let f : ℕ → ℝ → ℝ := fun k t => if hk : 0 < k then
    partialDonaldsonFunctional L T omega hvol k hk φ
      (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t) else 0
  let a : ℕ → ℝ → ℝ := fun k t =>
    supDonaldson omega hvol L T φ (sourcePerturbedWeightedSubset W u t) k
  let g : ℝ → ℝ := fun t => energyK omega hφ hφpos (sourcePerturbedWeightedSubset W u t)
  have hf : ∀ k, ConcaveOn ℝ univ (f k) := by
    intro k
    by_cases hk : 0 < k
    · simpa only [f, dif_pos hk] using
        sourcePartialDonaldson_concave L T W μ hBM k hk φ omega hvol u
    · simpa only [f, dif_neg hk] using (concaveOn_const (0 : ℝ) convex_univ)
  have hfderiv : ∀ k (hk : 0 < k), HasDerivAt (f k)
      (∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ) 0 := by
    intro k hk
    simpa only [f, dif_pos hk] using
      hasDerivAt_sourcePartialDonaldson_eq_global_Bergman L T W μ hBM k hk φ omega hvol w
  have hfd : ∀ k, DifferentiableAt ℝ (f k) 0 := by
    intro k
    by_cases hk : 0 < k
    · exact (hfderiv k hk).differentiableAt
    · simp only [f, dif_neg hk]
      exact differentiableAt_const _
  have hg := partialEquilibriumEnergy_hasDerivAt omega hφ hφpos W.isClosed_carrier
    W.nonPluripolar_carrier W.weight u 0
  have hgd : DifferentiableAt ℝ g 0 := hg.differentiableAt
  have hcompare : ∀ k t, a k t ≤ f k t := by
    intro k t
    by_cases hk : 0 < k
    · simp only [a, f, supDonaldson, dif_pos hk]
      exact sourcePartialDonaldson_sup_le_perturbedL2 L T W μ hBM k hk φ omega hvol u t
    · simp only [a, f, supDonaldson, dif_neg hk, le_refl]
  have ha : ∀ t, Tendsto (fun k => a k t) atTop (𝓝 (g t)) := fun t =>
    Lkconv omega hvol L T hL hT hcurrent han hRR hφ hφpos (sourcePerturbedWeightedSubset W u t)
  have hW0 : sourcePerturbedWeightedSubset W u 0 = W := by
    cases W
    simp only [sourcePerturbedWeightedSubset, zero_smul, add_zero]
  have hzero : Tendsto (fun k => a k 0 - f k 0) atTop (𝓝 0) := by
    have h := tendsto_partialDonaldson_sup_sub_perturbed_zero L T W μ hBM φ hL hT omega hvol u
    apply h.congr
    intro k
    by_cases hk : 0 < k
    · simp only [a, f, supDonaldson, dif_pos hk, hW0]
    · simp only [a, f, supDonaldson, dif_neg hk, sub_zero]
  have hlim := tendsto_deriv_of_concave_lower_approx_zero_difference hf hfd hgd hcompare ha hzero
  -- identify the derivatives
  have hderivf : ∀ᶠ k in atTop, deriv (f k) 0 = ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (hfderiv k hk).deriv
  have hPIeq : partialIEnvelope θ φ W.carrier (fun y => ((W.weight + (0 : ℝ) • u) y : EReal)) = PI := by
    congr 1
    funext y
    simp [SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight]
  have hderivg : deriv g 0 = ∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI := by
    have hgd' : deriv g 0 = _ := hg.deriv
    rw [hgd', sourcePotentialNonPluripolarMeasure_congr hPIeq _ hPI]
    have hK : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ PI hPI, x ∈ W.carrier := by
      filter_upwards [partialIEnvelope_continuous_contact_ae omega hφ hφpos W.isClosed_carrier
        W.nonPluripolar_carrier W.weight] with x hx
      exact hx.choose
    change ∫ x : W.carrier, w (x : X) ∂Measure.comap Subtype.val
      (sourcePotentialNonPluripolarMeasure θ PI hPI) = _
    rw [integral_subtype_comap W.isClosed_carrier.measurableSet (fun x => w x),
      Measure.restrict_eq_self_of_ae_mem hK]
  rw [← hderivg]
  exact hlim.congr' hderivf

end SGPT.Bergman.Quant2
