import SGPT.Bergman.Quant4LowerBound
import SGPT.IGood.DXLow2Upper

/-!
# `thm:DXmain1` for big line bundles and `thm:pBMconvergence`, in the Bergman framework

Blueprint `claude-dx-low2`, node `claude-dx-low2:bergman-pbm`. With the lower half
(`Quant4.riemannRochLowerBound`, every `φ`) and the upper half
(`SGPT.IGood.DXLow2.riemannRochUpperBound_of_kahlerCurrent`: every `φ` as soon as `PSH(X, θ)`
contains a Kähler current, i.e. `L` is big) of the asymptotic Riemann–Roch formula:

* `tendsto_normalizedH0_of_big`: `thm:DXmain1` for every `φ ∈ PSH(X, θ)` when `θ = c₁(L, h)`
  carries a Kähler current: `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`;
* `tendsto_normalizedH0_of_pos`: the same for every `φ ∈ PSH(X, θ)_{>0}`;
* `pBMconvergence`: source `thm:pBMconvergence`, without hypotheses: for `φ ∈ PSH(X, θ)_{>0}`,
  every weighted subset `(K, v)` and `μ ∈ BM(K, v)`, `β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Bergman.Quant4

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.SingularWeightedHilbert
open SGPT.Bergman.Quant2 SGPT.Bergman.Quant3
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **`thm:DXmain1` for big line bundles** (Bergman framework): if `θ = c₁(L, h)` carries a Kähler
current `θ_ψ`, then for every `φ ∈ PSH(X, θ)` and every twist `T`,
`n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_of_big
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {ψ : X → EReal} (hψ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨h1, hlow⟩ := riemannRochLowerBound omega hvol L T hL hT hφ
  obtain ⟨h2, hup⟩ := SGPT.IGood.DXLow2.riemannRochUpperBound_of_kahlerCurrent omega hvol hL hT hψ hφ
  exact tendsto_of_le_liminf_of_limsup_le hlow hup

/-- **`thm:DXmain1` for potentials of positive mass** (Bergman framework, the book's Steps 1–2):
for `φ ∈ PSH(X, θ)_{>0}` and every twist `T`, `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_of_pos
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨m, hmc, -, -, -⟩ := exists_increasing_kahlerCurrent_minorants omega L hL hφ hφpos
  exact tendsto_normalizedH0_of_big omega hvol L T hL hT (hmc 0) hφ

/-- **Source `thm:pBMconvergence`** (unconditional): for `φ ∈ PSH(X, θ)_{>0}`, every weighted
subset `(K, v)` and `μ ∈ BM(K, v)`, `∫_X w dβ^k_{v,φ,μ} → ∫_X w dθⁿ_{P_{θ,K}[φ]_𝓘(v)}` for every
`w ∈ C⁰(X)`. -/
theorem pBMconvergence
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) :=
  Quant3.pBMconvergence omega hvol L T hL hT
    (fun _ hψ => SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hψ) hφ hφpos
    (SGPT.IGood.DXLow2.riemannRochUpperBound_of_pos omega hvol hL hT hφ hφpos) W μ hBM

end SGPT.Bergman.Quant4
