import SGPT.Bergman.Quant3QEAEnvelopes
import SGPT.Bergman.Quant3WeakLimit
import SGPT.Bergman.Quant2EnergySmooth
import SGPT.Bergman.SourceBergmanIOrderMonotonicity
import SGPT.Okounkov.PartialBodyKahler

/-!
# Weak convergence of partial Bergman measures: Kähler currents

Source `prop:mainKahcurr` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 1211--1252).

Let `X` be a connected compact Kähler manifold with `∫_X ωⁿ = 1`, `(L,h)`, `(T,h_T)` Hermitian
holomorphic line bundles with smooth metrics, `θ = c₁(L,h)`, `φ ∈ PSH(X,θ)` such that `θ_φ` is a
Kähler current, `(K,v)` a weighted subset and `μ ∈ BM(K,v)`. The book proves
`β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`.

## The book's proof and its formal counterpart

Take a quasi-equisingular approximation `(φ_j)` of `φ` by Kähler currents with analytic
singularities (`exists_isKahlerQEA`). Then

* `β^k_{v,φ,μ} ≤ β^k_{v,φ_j,μ}` (`rmk:Bergman:L797`, `sourcePartialBergmanMeasure_mono`);
* `β^k_{v,φ_j,μ} ⇀ θⁿ_{P_{θ,K}[φ_j]_𝓘(v)}` as `k → ∞` (`prop:weakconvana`, BERGMAN2's
  `Quant2.weakconvana`, which assumes the lower half `RiemannRochLowerBound` of `thm:DXmain1`
  for `φ_j`);
* `θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}` as `j → ∞` (`prop:conv_of_K_env`,
  `cor:quasi-equichar`, `thm:semicon`; file `Quant3QEAEnvelopes`);
* the total masses `β^k_{v,φ,μ}(X) = n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` converge to
  `vol(θ,φ) = ∫_X θⁿ_{P_{θ,K}[φ]_𝓘(v)}` (`eq:betaint_conv`, i.e. `thm:DXmain1` for `φ`).

The book concludes with weak cluster points `τ ≤ θⁿ_{P_{θ,K}[φ]_𝓘(v)}` and a comparison of
masses; we use the equivalent test-function form (`Quant3WeakLimit`).

The upper half `limsup ≤ vol(θ,φ)` of `eq:betaint_conv` is proved here **unconditionally**
(`limsup_normalizedH0_le_iVolume_of_kahlerCurrent`, from BERGMAN2's analytic case and the
approximation). The lower half `vol(θ,φ) ≤ liminf` is the hypothesis `RiemannRochLowerBound`
for `φ` and for the analytic approximants (`prop:DXmainanalytic`, `thm:DXmain1`), as in BERGMAN2's
entries.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant3

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The total mass of `β^k_{v,φ,μ}` is `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` for `k ≥ 1`. -/
theorem sourcePartialBergmanMeasure_univ (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) {k : ℕ} (hk : 0 < k) (φ : X → EReal) :
    sourcePartialBergmanMeasure L T W μ k φ univ = normalizedH0 L T φ k := by
  rw [sourcePartialBergmanMeasure_mass L T W μ hBM k hk φ, normalizedH0,
    sourceBergmanNormalization, ENNReal.ofReal_mul (by positivity)]

/-- `β^k_{v,φ,μ}` is a finite measure for `k ≥ 1`. -/
theorem sourcePartialBergmanMeasure_isFinite (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) {k : ℕ} (hk : 0 < k) (φ : X → EReal) :
    IsFiniteMeasure (sourcePartialBergmanMeasure L T W μ k φ) :=
  ⟨by rw [sourcePartialBergmanMeasure_univ L T W μ hBM hk φ, normalizedH0]
      exact ENNReal.ofReal_lt_top⟩

/-- `h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ h⁰(X, L^k ⊗ T ⊗ 𝓘(kψ))` when `φ ⪯_𝓘 ψ`. -/
theorem normalizedH0_le_of_sourceIOrder (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle n X)
    {φ ψ : X → EReal} (hI : sourceIOrder (ofFixedModel n X) φ ψ) {k : ℕ} (hk : 0 < k) :
    normalizedH0 L T φ k ≤ normalizedH0 L T ψ k := by
  have hBM := volX_BM omega hvol L T 0
  rw [← sourcePartialBergmanMeasure_univ L T _ _ hBM hk φ,
    ← sourcePartialBergmanMeasure_univ L T _ _ hBM hk ψ]
  exact SGPT.Bergman.IdealOrderMonotonicity.sourcePartialBergmanMeasure_mono L T _ _ hI k hk univ

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- A quasi-equisingular approximation of a Kähler current `θ_φ` (`θ = c₁(L,h)`) in `PSH(X,θ)`
by Kähler currents with analytic singularities (in the book's sense, `def:neatanasing`). -/
theorem exists_kahlerQEA_data (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    ∃ U : ℕ → X → EReal,
      SourceQuasiEquisingularApproximation (atlasClosedFormToNative (chernForm L hL)) φ U ∧
      (∀ j, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) (U j)) ∧
      (∀ j, (ofFixedModel n X).HasRationalAnalyticType (U j)) := by
  obtain ⟨U, hQ, hU⟩ := SGPT.Okounkov.PartialBody.exists_isKahlerQEA hcurrent
  refine ⟨U, ?_, fun j => (hU j).2, fun j => ?_⟩
  · simpa only [chernForm, sourceNativeAtlasForm_roundTrip] using hQ
  · exact hasRationalAnalyticType_iff_chartType.mpr
      (SGPT.Okounkov.TranscendentalCore.globalAnalyticCurrents_subset_analyticCurrents _ (hU j).1).2

/-- **The upper half of `thm:DXmain1` for Kähler currents** (in the Bergman framework,
unconditional): if `θ_φ` is a Kähler current, then
`limsup_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol(θ,φ)`. This is the book's Step 1 of the proof of
`thm:DXmain1` (upper bound): compare with a quasi-equisingular approximation `(φ_j)` by Kähler
currents with analytic singularities (BERGMAN2's `limsup_normalizedH0_le_iVolume`) and use
`vol(θ,φ_j) → vol(θ,φ)`. -/
theorem limsup_normalizedH0_le_iVolume_of_kahlerCurrent
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    limsup (fun k => normalizedH0 L T φ k) atTop ≤ sourceIVolume (chernForm L hL) φ hφ := by
  obtain ⟨_, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  obtain ⟨U, hQ, hUcur, han⟩ := exists_kahlerQEA_data L hL hcurrent
  choose hU _ using fun j => isThetaPSH_and_pos_of_kahlerCurrent omega L hL (hUcur j)
  have hlim := qea_sourceIVolume_tendsto omega hφ hφpos hQ hU
  refine ge_of_tendsto' hlim fun j => ?_
  have hI : sourceIOrder (ofFixedModel n X) φ (U j) :=
    sourceIOrder_of_singularityLE hφ (hU j)
      (SGPT.Okounkov.PartialBody.le_of_sourceQuasiEquisingularApproximation hQ j)
  calc limsup (fun k => normalizedH0 L T φ k) atTop
      ≤ limsup (fun k => normalizedH0 L T (U j) k) atTop := by
        refine limsup_le_limsup ?_
        filter_upwards [eventually_gt_atTop 0] with k hk
        exact normalizedH0_le_of_sourceIOrder omega hvol L T hI hk
    _ ≤ sourceIVolume (chernForm L hL) (U j) (hU j) :=
        limsup_normalizedH0_le_iVolume omega hvol L T hL hT (hUcur j) (han j) (hU j)

/-- `thm:DXmain1` for a Kähler current `θ_φ` (in the Bergman framework) follows from its lower
half `RiemannRochLowerBound`: `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol(θ,φ)`. -/
theorem tendsto_normalizedH0_of_kahlerCurrent
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ,
      Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨hφ, hlow⟩ := hRR
  exact ⟨hφ, tendsto_of_le_liminf_of_limsup_le hlow
    (limsup_normalizedH0_le_iVolume_of_kahlerCurrent omega hvol L T hL hT hcurrent hφ)⟩

/-- **Source `prop:mainKahcurr`**, assuming the lower half `RiemannRochLowerBound` of
`thm:DXmain1` for `φ` (`hRR`) and for the potentials with analytic singularities whose curvature
current is a Kähler current (`hRRan`, the lower half of `prop:DXmainanalytic`; it is used for the
quasi-equisingular approximants of `φ`): for every weighted subset `(K,v)` and `μ ∈ BM(K,v)`,
`∫_X w dβ^k_{v,φ,μ} → ∫_X w dθⁿ_{P_{θ,K}[φ]_𝓘(v)}` for every `w ∈ C⁰(X)`. -/
theorem mainKahcurr
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hRRan : ∀ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ →
      (ofFixedModel n X).HasRationalAnalyticType ψ → RiemannRochLowerBound (chernForm L hL) L T ψ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) := by
  intro θ PI
  obtain ⟨hφ, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI :=
    (partialIEnvelope_eInfinity_continuous omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  refine ⟨hPI, ?_⟩
  obtain ⟨U, hQ, hUcur, han⟩ := exists_kahlerQEA_data L hL hcurrent
  choose hU hUpos using fun j => isThetaPSH_and_pos_of_kahlerCurrent omega L hL (hUcur j)
  have hPj : ∀ j, (ofFixedModel n X).IsThetaPSH θ
      (partialIEnvelope θ (U j) W.carrier W.erealWeight) := fun j =>
    (partialIEnvelope_eInfinity_continuous omega (hU j) (hUpos j) W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  -- `prop:weakconvana` for the approximants
  have hγ : ∀ j (w : C(X, ℝ)), Tendsto
      (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k (U j)) atTop
      (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ (U j) W.carrier W.erealWeight) (hPj j))) := by
    intro j w
    obtain ⟨_, _, _, h⟩ := weakconvana omega hvol L T hL hT (hUcur j) (han j)
      (hRRan (U j) (hUcur j) (han j)) W μ hBM
    exact h w
  -- the comparison `β^k_{v,φ,μ} ≤ β^k_{v,φ_j,μ}`
  have hle : ∀ j, ∀ᶠ k in atTop, sourcePartialBergmanMeasure L T W μ k φ ≤
      sourcePartialBergmanMeasure L T W μ k (U j) := by
    intro j
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact SGPT.Bergman.IdealOrderMonotonicity.sourcePartialBergmanMeasure_mono L T W μ
      (sourceIOrder_of_singularityLE hφ (hU j)
        (SGPT.Okounkov.PartialBody.le_of_sourceQuasiEquisingularApproximation hQ j)) k hk
  have hfin : ∀ (ψ : X → EReal), ∀ᶠ k in atTop,
      IsFiniteMeasure (sourcePartialBergmanMeasure L T W μ k ψ) := fun ψ => by
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact sourcePartialBergmanMeasure_isFinite L T W μ hBM hk ψ
  -- `thm:semicon` along the approximation
  have hν := qea_partialIEnvelope_weakTendsto omega hφ hφpos hQ hU hUpos W hPj hPI
  -- the convergence of the total masses (`eq:betaint_conv`)
  have : IsFiniteMeasure (sourcePotentialNonPluripolarMeasure θ PI hPI) :=
    sourcePotentialMeasure_finite omega hPI
  have hνmass : sourcePotentialNonPluripolarMeasure θ PI hPI univ = sourceIVolume θ φ hφ :=
    partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight hPI
  have hmass : Tendsto (fun k => (sourcePartialBergmanMeasure L T W μ k φ univ).toReal) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ PI hPI univ).toReal) := by
    obtain ⟨hφ', hlim⟩ :=
      tendsto_normalizedH0_of_kahlerCurrent omega hvol L T hL hT hcurrent hRR
    rw [hνmass]
    have hfinvol : sourceIVolume θ φ hφ' ≠ ⊤ := by
      rw [← partialIEnvelope_mass_eq_sourceIVolume omega hφ' hφpos W.isClosed_carrier
        W.nonPluripolar_carrier W.weight hPI]
      exact (@measure_lt_top _ _ _ (sourcePotentialMeasure_finite omega hPI) univ).ne
    refine ((ENNReal.tendsto_toReal hfinvol).comp hlim).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    simp only [Function.comp_apply, sourcePartialBergmanMeasure_univ L T W μ hBM hk φ]
  exact tendsto_integral_of_eventually_le_of_mass
    (ν := sourcePotentialNonPluripolarMeasure θ PI hPI) _ (hfin φ) hmass
    (fun w hw ε hε => eventually_integral_le_of_le_of_tendsto _ _ _ _ hle
      (fun j => hfin (U j)) hγ hν w hw ε hε)

/-- **Source `prop:mainKahcurr`**, with the single hypothesis that the lower half of
`thm:DXmain1` holds for every `ψ ∈ PSH(X,θ)` such that `θ_ψ` is a Kähler current. -/
theorem mainKahcurr_of_lowerBound
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hRR : ∀ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ →
      RiemannRochLowerBound (chernForm L hL) L T ψ)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) :=
  mainKahcurr omega hvol L T hL hT hcurrent (hRR φ hcurrent) (fun ψ hψ _ => hRR ψ hψ) W μ hBM

end SGPT.Bergman.Quant3
