import SGPT.Bergman.Quant3MainKahcurr
import SGPT.Envelopes.SourceIncreasingMixedProducts
import SGPT.Envelopes.SourcePositiveMassCurrents

/-!
# Convergence of partial Bergman measures

Source `thm:pBMconvergence` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 817--822, proof lines 1257--1288).

For `φ ∈ PSH(X,θ)_{>0}`, a weighted subset `(K,v)` and `μ ∈ BM(K,v)`, the book proves
`β^k_{v,φ,μ} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`.

## The book's proof and its formal counterpart

By `lma:kahcurrentposmass` there are `φ_j ↗ φ` (almost everywhere) with `θ_{φ_j}` Kähler
currents (`sourcePositiveMass_kahlerCurrent_and_increasingMinorants`; here `φ_j ≤ φ`). Then

* `β^k_{v,φ_j,μ} ≤ β^k_{v,φ,μ}` (`rmk:Bergman:L797`);
* `β^k_{v,φ_j,μ} ⇀ θⁿ_{P_{θ,K}[φ_j]_𝓘(v)}` as `k → ∞` (`prop:mainKahcurr`, `Quant3.mainKahcurr`);
* `θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}` as `j → ∞` (the increasing case of
  `prop:conv_of_K_env` and `cor:incseqnppcont`);
* the total masses converge (`eq:betaint_conv`, i.e. `thm:DXmain1` for `φ`).

The book first replaces `φ` by `P_{θ,K}[φ]_𝓘(v)` (same multiplier ideals); with the formal
`prop:conv_of_K_env` (which needs no normalization of `φ`) this step is not needed.

## Hypotheses

Only `thm:DXmain1` is assumed, through the two halves of `eq:betaint_conv`:

* the lower half `RiemannRochLowerBound` for every `ψ ∈ PSH(X,θ)` such that `θ_ψ` is a Kähler
  current (used through `prop:mainKahcurr` for the `φ_j` and their analytic approximants);
* the upper half `RiemannRochUpperBound` for `φ` itself:
  `limsup_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol(θ,φ)`.

The lower half for `φ` itself is **proved** here (`le_liminf_normalizedH0`): it follows from the
convergence for the `φ_j`. The upper half is proved for Kähler currents
(`limsup_normalizedH0_le_iVolume_of_kahlerCurrent`), but not for general `φ` (the book's Step 2
of `thm:DXmain1` perturbs `L` by an ample line bundle). `pBMconvergence_of_DXmain1` states the
theorem with the single hypothesis "`thm:DXmain1` holds for every `ψ ∈ PSH(X,θ)_{>0}`".
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant3

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.MonotonePartialEnvelopes SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

/-- Convergence in `ℝ` of `(u_k).toReal` from `limsup u_k ≤ a` and eventual lower bounds. -/
theorem tendsto_toReal_of_limsup_le_of_eventually_ge {u : ℕ → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (hup : limsup u atTop ≤ a)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.toReal - ε ≤ (u k).toReal) :
    Tendsto (fun k => (u k).toReal) atTop (𝓝 a.toReal) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have h1 : ∀ᶠ k in atTop, u k < ENNReal.ofReal (a.toReal + ε / 2) := by
    refine eventually_lt_of_limsup_lt ?_
    calc limsup u atTop ≤ a := hup
      _ = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
      _ < ENNReal.ofReal (a.toReal + ε / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and (hlow (ε / 2) hε2))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hN k hk
  have hk1' := ENNReal.toReal_lt_of_lt_ofReal hk1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The upper half of `thm:DXmain1` (asymptotic Riemann--Roch) for the data `(L,T,φ)`:
`limsup_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol(θ_φ)`, `vol(θ_φ) = ∫_X θⁿ_{P_θ[φ]_𝓘}`. -/
def RiemannRochUpperBound (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) : Prop :=
  ∃ hφ : (ofFixedModel n X).IsThetaPSH θ φ,
    limsup (fun k => normalizedH0 L T φ k) atTop ≤ sourceIVolume θ φ hφ

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- `t s + (1-t) u ≤ u` for `s ≤ u`, `u < ∞` and `t > 0`. -/
theorem convexComb_le_right {s u : X → EReal} (hsu : s ≤ u) (hutop : ∀ x, u x ≠ ⊤)
    {t : ℝ} (ht0 : 0 < t) : convexComb t s u ≤ u := by
  intro x
  rw [convexComb_apply]
  by_cases hsb : s x = ⊥
  · rw [hsb, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  have hub : u x ≠ ⊥ := fun h => hsb (le_bot_iff.mp (h ▸ hsu x))
  obtain ⟨a, ha⟩ : ∃ a : ℝ, u x = a := ⟨(u x).toReal, (EReal.coe_toReal (hutop x) hub).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, s x = b :=
    ⟨(s x).toReal, (EReal.coe_toReal (ne_top_of_le_ne_top (hutop x) (hsu x)) hsb).symm⟩
  have hba : b ≤ a := by
    have := hsu x
    rw [ha, hb] at this
    exact EReal.coe_le_coe_iff.mp this
  rw [ha, hb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  nlinarith

/-- **`lma:kahcurrentposmass` in the form used by the proof of `thm:pBMconvergence`**: for
`φ ∈ PSH(X,θ)_{>0}`, `θ = c₁(L,h)`, there are `φ_j ∈ PSH(X,θ)`, increasing, `φ_j ≤ φ`,
`φ_j → φ` almost everywhere, with `θ_{φ_j}` Kähler currents. -/
theorem exists_increasing_kahlerCurrent_minorants (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ) :
    ∃ m : ℕ → X → EReal, (∀ j, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) (m j)) ∧
      Monotone m ∧ (∀ j, m j ≤ φ) ∧
      ∀ᵐ x ∂sourceKahlerVolume omega, Tendsto (fun j => m j x) atTop (𝓝 (φ x)) := by
  obtain ⟨δ, hδ, s, hs, hsu, -, hm, hmono, hkc, hae⟩ :=
    sourcePositiveMass_kahlerCurrent_and_increasingMinorants omega hφ hφpos
  refine ⟨sourceCurrentMinorant φ s, fun j => ?_, hmono, fun j => ?_, hae⟩
  · have hc : 0 < ((j : ℝ) + 2)⁻¹ * δ := mul_pos (sourceCurrentMinorant_weights j).1 hδ
    have h := (sourceStrictCurrent_iff omega hc).mpr (hkc j)
    have hn := (isThetaPSH_iff_nativeThetaPotential _ _).mp h
    rw [sourceNativeAtlasForm_roundTrip] at hn
    refine ⟨KahlerBackground.smul hc omega, ?_⟩
    simpa only [KahlerBackground.smul_form, chernForm, sourceNativeAtlasForm_roundTrip] using hn
  · exact convexComb_le_right hsu
      (fun x => ((isThetaPSH_iff_nativeThetaPotential _ φ).mp hφ).1.quasiPlurisubharmonic.ne_top x)
      (sourceCurrentMinorant_weights j).1

/-- **The increasing case of `prop:conv_of_K_env` and `cor:incseqnppcont`**: if `φ_j ↗ φ`
almost everywhere (`φ_j, φ ∈ PSH(X,θ)_{>0}`), then
`θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`. -/
theorem increasing_partialIEnvelope_weakTendsto (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {m : ℕ → X → EReal} (hm : ∀ j, (ofFixedModel n X).IsThetaPSH θ (m j))
    (hmpos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (m j) (hm j) univ)
    (hmono : Monotone m)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hae : ∀ᵐ x ∂sourceKahlerVolume omega, Tendsto (fun j => m j x) atTop (𝓝 (φ x)))
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (hPj : ∀ j, (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ (m j) W.carrier W.erealWeight))
    (hP : (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ φ W.carrier W.erealWeight))
    (w : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ (m j) W.carrier W.erealWeight) (hPj j)) atTop
      (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ W.carrier W.erealWeight) hP)) := by
  obtain ⟨hmonoP, husc, -⟩ := (partialEnvelopes_increasing omega hm hmpos hmono hφ hφpos hae W).2
  obtain ⟨R, -, hR⟩ := SGPT.Bergman.WeightedSubset.WeightedSubset.exists_real_abs_bound W
  obtain ⟨-, hB⟩ := SGPT.Bergman.PartialEnvelopeUniformBound.partialEnvelopes_uniform_bound_at_sup
    omega θ W.nonPluripolar_carrier (fun x => W.weight x) ⟨R, hR⟩
  have hC : ∀ (a : Fin n) (j : ℕ) (x : X),
      partialIEnvelope θ (m j) W.carrier W.erealWeight x ≤
        ((SGPT.Bergman.PartialEnvelopeUniformBound.uniformUpperBound θ W.nonPluripolar_carrier (sSup (range (fun x => W.weight x))) : ℝ) :
          EReal) :=
    fun _ j x => (hB (m j) (hm j) (hmpos j)).2 x
  have hconv := sourceIncreasingMixed_sequence_weakTendsto omega (θ := fun _ : Fin n => θ)
    (u := fun j _ => partialIEnvelope θ (m j) W.carrier W.erealWeight) (fun j _ => hPj j)
    (fun _ => hmonoP) hC
  have h := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
    (BoundedContinuousFunction.mkOfCompact w)
  simp only [BoundedContinuousFunction.mkOfCompact_apply, sourceFiniteMixedNonPluripolarMeasure_coe,
    sourceMixedNonPluripolarMeasure_diagonal] at h
  have hu' : (ofFixedModel n X).IsThetaPSH θ
      (uscRegularization (⨆ i, partialIEnvelope θ (m i) W.carrier W.erealWeight)) := husc ▸ hP
  convert h using 3
  all_goals first
    | exact SGPT.Bergman.Quant2.sourcePotentialNonPluripolarMeasure_congr husc.symm hP hu'
    | rfl

/-- **Lower half of `thm:DXmain1` for `φ ∈ PSH(X,θ)_{>0}`**, from the lower half for Kähler
currents (in the Bergman framework): `vol(θ,φ) ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`.
Together with the lower bounds for the increasing Kähler-current minorants `φ_j` and
`vol(θ,φ_j) → vol(θ,φ)` (as in the book's Step 2 of `thm:DXmain1`, with `φ_j` instead of
`(1-t)φ + tψ`). -/
theorem le_liminf_normalizedH0
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L)
    (hRR : ∀ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ →
      RiemannRochLowerBound (chernForm L hL) L T ψ)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  refine ⟨hφ, ?_⟩
  obtain ⟨m, hmc, hmono, hmle, hae⟩ :=
    exists_increasing_kahlerCurrent_minorants omega L hL hφ hφpos
  choose hm hmpos using fun j => isThetaPSH_and_pos_of_kahlerCurrent omega L hL (hmc j)
  let W := wholeWeightedSubset (n := n) (0 : C(X, ℝ))
  have hPj : ∀ j, (ofFixedModel n X).IsThetaPSH (chernForm L hL)
      (partialIEnvelope (chernForm L hL) (m j) W.carrier W.erealWeight) := fun j =>
    (partialIEnvelope_eInfinity_continuous omega (hm j) (hmpos j) W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  have hP : (ofFixedModel n X).IsThetaPSH (chernForm L hL)
      (partialIEnvelope (chernForm L hL) φ W.carrier W.erealWeight) :=
    (partialIEnvelope_eInfinity_continuous omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  have hconv := increasing_partialIEnvelope_weakTendsto omega hm hmpos hmono hφ hφpos hae W hPj hP
    (ContinuousMap.const X 1)
  simp only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one] at hconv
  have hmass : ∀ j, sourcePotentialNonPluripolarMeasure (chernForm L hL)
      (partialIEnvelope (chernForm L hL) (m j) W.carrier W.erealWeight) (hPj j) univ =
        sourceIVolume (chernForm L hL) (m j) (hm j) := fun j =>
    partialIEnvelope_mass_eq_sourceIVolume omega (hm j) (hmpos j) W.isClosed_carrier
      W.nonPluripolar_carrier W.weight (hPj j)
  have hmassφ : sourcePotentialNonPluripolarMeasure (chernForm L hL)
      (partialIEnvelope (chernForm L hL) φ W.carrier W.erealWeight) hP univ =
        sourceIVolume (chernForm L hL) φ hφ :=
    partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight hP
  have hfin : ∀ j, sourceIVolume (chernForm L hL) (m j) (hm j) ≠ ⊤ := fun j => by
    rw [← hmass j]
    exact (@measure_lt_top _ _ _ (sourcePotentialMeasure_finite omega (hPj j)) univ).ne
  have hfinφ : sourceIVolume (chernForm L hL) φ hφ ≠ ⊤ := by
    rw [← hmassφ]
    exact (@measure_lt_top _ _ _ (sourcePotentialMeasure_finite omega hP) univ).ne
  simp only [Measure.real, hmass, hmassφ] at hconv
  have hvolj : Tendsto (fun j => sourceIVolume (chernForm L hL) (m j) (hm j)) atTop
      (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
    have := (ENNReal.tendsto_ofReal hconv)
    simpa only [ENNReal.ofReal_toReal (hfin _), ENNReal.ofReal_toReal hfinφ] using this
  refine le_of_tendsto' hvolj fun j => ?_
  obtain ⟨hmj, hlow⟩ := hRR (m j) (hmc j)
  have hI : sourceIOrder (ofFixedModel n X) (m j) φ :=
    sourceIOrder_of_singularityLE (hm j) hφ
      ((singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by simpa using hmle j x⟩)
  calc sourceIVolume (chernForm L hL) (m j) (hm j)
      ≤ liminf (fun k => normalizedH0 L T (m j) k) atTop := hlow
    _ ≤ liminf (fun k => normalizedH0 L T φ k) atTop := by
        refine liminf_le_liminf ?_
        filter_upwards [eventually_gt_atTop 0] with k hk
        exact normalizedH0_le_of_sourceIOrder omega hvol L T hI hk

/-- **Source `thm:pBMconvergence`**, assuming the two halves of `eq:betaint_conv`
(i.e. of `thm:DXmain1`) that are not proved in the Bergman framework: the lower half
`RiemannRochLowerBound` for every `ψ ∈ PSH(X,θ)` with `θ_ψ` a Kähler current (`hRR`) and the
upper half `RiemannRochUpperBound` for `φ` (`hUp`). For `φ ∈ PSH(X,θ)_{>0}`, every weighted
subset `(K,v)` and `μ ∈ BM(K,v)`: `∫_X w dβ^k_{v,φ,μ} → ∫_X w dθⁿ_{P_{θ,K}[φ]_𝓘(v)}` for every
`w ∈ C⁰(X)`. -/
theorem pBMconvergence
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hRR : ∀ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ →
      RiemannRochLowerBound (chernForm L hL) L T ψ)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (hUp : RiemannRochUpperBound (chernForm L hL) L T φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) := by
  intro θ PI
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI :=
    (partialIEnvelope_eInfinity_continuous omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  refine ⟨hPI, ?_⟩
  obtain ⟨m, hmc, hmono, hmle, hae⟩ :=
    exists_increasing_kahlerCurrent_minorants omega L hL hφ hφpos
  choose hm hmpos using fun j => isThetaPSH_and_pos_of_kahlerCurrent omega L hL (hmc j)
  have hPj : ∀ j, (ofFixedModel n X).IsThetaPSH θ
      (partialIEnvelope θ (m j) W.carrier W.erealWeight) := fun j =>
    (partialIEnvelope_eInfinity_continuous omega (hm j) (hmpos j) W.isClosed_carrier
      W.nonPluripolar_carrier W.weight).1
  -- `prop:mainKahcurr` for the minorants
  have hγ : ∀ j (w : C(X, ℝ)), Tendsto
      (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k (m j)) atTop
      (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ (m j) W.carrier W.erealWeight) (hPj j))) := by
    intro j w
    obtain ⟨_, h⟩ := mainKahcurr_of_lowerBound omega hvol L T hL hT hRR (hmc j) W μ hBM
    exact h w
  -- the comparison `β^k_{v,φ_j,μ} ≤ β^k_{v,φ,μ}`
  have hle : ∀ j, ∀ᶠ k in atTop, sourcePartialBergmanMeasure L T W μ k (m j) ≤
      sourcePartialBergmanMeasure L T W μ k φ := by
    intro j
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact SGPT.Bergman.IdealOrderMonotonicity.sourcePartialBergmanMeasure_mono L T W μ
      (sourceIOrder_of_singularityLE (hm j) hφ
        ((singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by simpa using hmle j x⟩)) k hk
  have hfin : ∀ᶠ k in atTop, IsFiniteMeasure (sourcePartialBergmanMeasure L T W μ k φ) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact sourcePartialBergmanMeasure_isFinite L T W μ hBM hk φ
  -- the increasing case of `prop:conv_of_K_env` and `cor:incseqnppcont`
  have hν := increasing_partialIEnvelope_weakTendsto omega hm hmpos hmono hφ hφpos hae W hPj hPI
  have hlow := eventually_integral_ge_of_ge_of_tendsto _ _ _
    (sourcePotentialNonPluripolarMeasure θ PI hPI) hle hfin hγ hν
  -- the convergence of the total masses (`eq:betaint_conv`)
  have : IsFiniteMeasure (sourcePotentialNonPluripolarMeasure θ PI hPI) :=
    sourcePotentialMeasure_finite omega hPI
  have hνmass : sourcePotentialNonPluripolarMeasure θ PI hPI univ = sourceIVolume θ φ hφ :=
    partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos W.isClosed_carrier
      W.nonPluripolar_carrier W.weight hPI
  have hmass : Tendsto (fun k => (sourcePartialBergmanMeasure L T W μ k φ univ).toReal) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ PI hPI univ).toReal) := by
    refine tendsto_toReal_of_limsup_le_of_eventually_ge
      (@measure_lt_top _ _ _ this univ).ne ?_ fun ε hε => ?_
    · obtain ⟨hφ', hup⟩ := hUp
      rw [hνmass]
      calc limsup (fun k => sourcePartialBergmanMeasure L T W μ k φ univ) atTop
          = limsup (fun k => normalizedH0 L T φ k) atTop := by
            refine limsup_congr ?_
            filter_upwards [eventually_gt_atTop 0] with k hk
            exact sourcePartialBergmanMeasure_univ L T W μ hBM hk φ
        _ ≤ sourceIVolume θ φ hφ' := hup
    · filter_upwards [hlow (ContinuousMap.const X 1) (fun _ => zero_le_one) ε hε, hfin]
        with k hk hkfin
      simpa only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one,
        Measure.real] using hk
  exact tendsto_integral_of_eventually_ge_of_mass
    (ν := sourcePotentialNonPluripolarMeasure θ PI hPI) _ hfin hmass hlow

/-- **Source `thm:pBMconvergence`**, with the single hypothesis that `thm:DXmain1` holds (in the
Bergman framework, `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kψ)) → vol(θ,ψ)`) for every
`ψ ∈ PSH(X,θ)_{>0}`; this is how the book uses `thm:DXmain1` (`eq:betaint_conv`). -/
theorem pBMconvergence_of_DXmain1
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hDX : ∀ (ψ : X → EReal) (hψ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) ψ),
      0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) ψ hψ univ →
      Tendsto (fun k => normalizedH0 L T ψ k) atTop (𝓝 (sourceIVolume (chernForm L hL) ψ hψ)))
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    let θ := chernForm L hL
    let PI := partialIEnvelope θ φ W.carrier W.erealWeight
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ PI,
      ∀ w : C(X, ℝ), Tendsto (fun k => ∫ x, w x ∂sourcePartialBergmanMeasure L T W μ k φ)
        atTop (𝓝 (∫ x, w x ∂sourcePotentialNonPluripolarMeasure θ PI hPI)) := by
  refine pBMconvergence omega hvol L T hL hT (fun ψ hψc => ?_) hφ hφpos
    ⟨hφ, (hDX φ hφ hφpos).limsup_eq.le⟩ W μ hBM
  obtain ⟨hψ, hψpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hψc
  exact ⟨hψ, (hDX ψ hψ hψpos).liminf_eq.ge⟩

end SGPT.Bergman.Quant3
