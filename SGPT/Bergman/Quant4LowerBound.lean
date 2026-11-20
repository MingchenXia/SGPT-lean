import SGPT.IGood.DXLow2Final
import SGPT.Bergman.Quant2WeakConvAna
import SGPT.Bergman.Quant3PBMConvergence

/-!
# The Bergman-chapter statements without the Riemann–Roch hypothesis

Blueprint `claude-dx-low2`, node `claude-dx-low2:bergman`. Lanes BERGMAN2 and BERGMAN3 proved
`prop:smooth_weak_conv`, `prop:quant_I_smooth`, `cor:Ninfdifflim`, `prop:quant_I_algebraic_BM`,
`cor:LktoI`, `prop:weakconvana` (`SGPT/Bergman/Quant2*.lean`) and `prop:mainKahcurr`
(`SGPT/Bergman/Quant3MainKahcurr.lean`) under the hypothesis `RiemannRochLowerBound`, the lower half
`vol θ_φ ≤ liminf_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` of `thm:DXmain1`. Lane DX-LOW2 proves this
lower half for every Kähler current (`SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent`)
and, with BERGMAN3's `le_liminf_normalizedH0`, for every `φ ∈ PSH(X, θ)`
(`riemannRochLowerBound`). Instantiating the hypothesis gives the unconditional statements below.

In all statements `X` is a connected compact Kähler manifold with `∫_X ωⁿ = 1`, `(L, h)` and
`(T, h_T)` are Hermitian holomorphic line bundles with smooth metrics and `θ = c₁(L, h)`.
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
open SGPT.Bergman.ContactConcentration SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.PartialDonaldson SGPT.Bergman.QuantizationFrontier
open SGPT.Bergman.Quant2 SGPT.Bergman.Quant3
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-! ### The lower half of `thm:DXmain1` -/

/-- **The lower half of `thm:DXmain1` for every `φ ∈ PSH(X, θ)`** (Bergman framework, every
twist `T`): `vol θ_φ ≤ liminf_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. For Kähler currents this is
DX-LOW2's `riemannRochLowerBound_of_isKahlerCurrent`; for `φ` of positive volume, apply BERGMAN3's
`le_liminf_normalizedH0` (increasing Kähler-current minorants) to `P_θ[φ]_𝓘`, which has the same
multiplier ideals and volume; if `vol θ_φ = 0` there is nothing to prove. -/
theorem riemannRochLowerBound (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  refine ⟨hφ, ?_⟩
  rcases (zero_le : (0 : ℝ≥0∞) ≤ sourceIVolume (chernForm L hL) φ hφ).eq_or_lt with h0 | hpos
  · rw [← h0]; exact zero_le
  have hP := isThetaPSH_sourceIEnvelope hφ
  have hPpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL)
      (sourceIEnvelope (chernForm L hL) φ) hP univ := hpos
  obtain ⟨hP', hlow⟩ := le_liminf_normalizedH0 omega hvol L T hL
    (fun ψ hψ => SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hψ) hP hPpos
  rw [sourceIVolume_sourceIEnvelope hφ] at hlow
  refine hlow.trans (liminf_le_liminf ?_)
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact normalizedH0_le_of_sourceIOrder omega hvol L T (sourceIEquivalent_iEnvelope hφ).2 hk

/-- **`thm:DXmain1` for Kähler currents** (Bergman framework): if `θ_φ` is a Kähler current,
`n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_of_kahlerCurrent
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ,
      Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) :=
  Quant3.tendsto_normalizedH0_of_kahlerCurrent omega hvol L T hL hT hcurrent
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent)

/-! ### `prop:smooth_weak_conv` -/

/-- **Source `prop:smooth_weak_conv`** (unconditional): for `φ ∈ PSH(X, θ)` with analytic
singularities and `θ_φ` a Kähler current and `v ∈ C^∞(X)`,
`β^k_{v,φ,ωⁿ} ⇀ θⁿ_{P_{θ,X}[φ]_𝓘(v)} = θⁿ_{P_{θ,X}[φ](v)}` (against every continuous test
function). -/
theorem smooth_weak_conv
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      ∀ f : C(X, ℝ), Tendsto (fun k => ∫ x, f x ∂sourcePartialBergmanMeasure L T
          (wholeWeightedSubset v) ((kahlerVolume omega).comap
            (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ)
        atTop (𝓝 (∫ x, f x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) :=
  Quant2.smooth_weak_conv omega hvol L T hL hT v hv hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent)

/-- **Source `prop:smooth_weak_conv`**, as weak convergence of finite measures (`k = j + 1`). -/
theorem smooth_weak_conv_finiteMeasure
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI)
      (M : FiniteMeasure X), PI = P ∧ (M : Measure X) = sourcePotentialNonPluripolarMeasure θ PI hPI ∧
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv (j+1) (Nat.succ_pos j) φ)
        atTop (𝓝 M) :=
  Quant2.smooth_weak_conv_finiteMeasure omega hvol L T hL hT v hv hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent)

/-! ### `prop:quant_I_smooth` and `cor:Ninfdifflim` -/

/-- **Source `prop:quant_I_smooth`, `eq:LdiffonXsmoothmeasure`** (unconditional):
`L_{k,φ}(N^k_{w,ωⁿ}) - L_{k,φ}(N^k_{w',ωⁿ}) → E^φ_{θ,X}(w) - E^φ_{θ,X}(w')`. -/
theorem quant_I_smooth
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w w' : C(X, ℝ)) :
    Tendsto (fun k => donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ w' k) atTop
      (𝓝 (energyX omega hφ hφpos w - energyX omega hφ hφpos w')) :=
  Quant2.quant_I_smooth omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos w w'

/-- **Source `prop:quant_I_smooth`, `eq:LdiffonXsmoothmeasure2`** (unconditional):
`L_{k,φ}(N^k_{w,ωⁿ}) → E^φ_{θ,X}(w)`. -/
theorem quant_I_smooth_single
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w : C(X, ℝ)) :
    Tendsto (fun k => donaldsonL2 omega hvol L T φ w k) atTop (𝓝 (energyX omega hφ hφpos w)) :=
  Quant2.quant_I_smooth_single omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos w

/-- **Source `cor:Ninfdifflim`** (unconditional): `L_{k,φ}(N^k_{w,X}) → E^φ_{θ,X}(w)`. -/
theorem Ninfdifflim
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w : C(X, ℝ)) :
    Tendsto (fun k => supDonaldson omega hvol L T φ (wholeWeightedSubset w) k) atTop
      (𝓝 (energyX omega hφ hφpos w)) :=
  Quant2.Ninfdifflim omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos w

/-! ### `prop:quant_I_algebraic_BM` and `cor:LktoI` -/

/-- **Source `prop:quant_I_algebraic_BM`, `eq:Lkconv`** (unconditional):
`L_{k,φ}(N^k_{v,K}) → E^φ_{θ,K}(v)` for every weighted subset `(K, v)`. -/
theorem Lkconv
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    Tendsto (fun k => supDonaldson omega hvol L T φ W k) atTop
      (𝓝 (energyK omega hφ hφpos W)) :=
  Quant2.Lkconv omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos W

/-- **Source `prop:quant_I_algebraic_BM`, `eq:LkdiffconvtoI`** (unconditional):
`L_{k,φ}(N^k_{v,K}) - L_{k,φ}(N^k_{v',K'}) → E^φ_{θ,K}(v) - E^φ_{θ,K'}(v')`. -/
theorem quant_I_algebraic_BM
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W W' : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    Tendsto (fun k => supDonaldson omega hvol L T φ W k - supDonaldson omega hvol L T φ W' k)
      atTop (𝓝 (energyK omega hφ hφpos W - energyK omega hφ hφpos W')) :=
  Quant2.quant_I_algebraic_BM omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos W W'

/-- **Source `cor:LktoI`** (unconditional): for `μ ∈ BM(K, v)`,
`L_{k,φ}(N^k_{v,μ}) → E^φ_{θ,K}(v)`. -/
theorem LktoI
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    Tendsto (fun k => l2Donaldson omega hvol L T φ W μ hBM k) atTop
      (𝓝 (energyK omega hφ hφpos W)) :=
  Quant2.LktoI omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) hφ hφpos W μ hBM

/-! ### `prop:weakconvana` and `prop:mainKahcurr` -/

/-- **Source `prop:weakconvana`** (unconditional): for `φ` with analytic singularities such that
`θ_φ` is a Kähler current, every weighted subset `(K, v)` and `μ ∈ BM(K, v)`,
`β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)} = θⁿ_{P_{θ,K}[φ](v)}`. -/
theorem weakconvana
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let P := partialEnvelope θ φ W.carrier W.erealWeight
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) :=
  Quant2.weakconvana omega hvol L T hL hT hcurrent han
    (SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hcurrent) W μ hBM

/-- **Source `prop:mainKahcurr`** (unconditional): for `φ ∈ PSH(X, θ)` such that `θ_φ` is a
Kähler current, every weighted subset `(K, v)` and `μ ∈ BM(K, v)`,
`β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`. -/
theorem mainKahcurr
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) :=
  Quant3.mainKahcurr_of_lowerBound omega hvol L T hL hT
    (fun _ hψ => SGPT.IGood.DXLow2.riemannRochLowerBound_of_isKahlerCurrent hL hT hψ) hcurrent W μ hBM

end SGPT.Bergman.Quant4
