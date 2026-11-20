import SGPT.Bergman.Quant2SmoothWeakConv
import SGPT.Bergman.Quant2WeakConvAna
import SGPT.Bergman.SourcePartialEnvelopeMonotoneConvergence
import SGPT.NPP.CapacityConvergenceSemicon
import SGPT.PSH.SourceIEnvelopeSingularityContinuity
import SGPT.PSH.SourceIGoodAnalyticCharacterization
import SGPT.PSH.SourceQuasiEquisingularCriterion
import SGPT.Envelopes.CapacityConsumersEdiff
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit

/-!
# Partial `𝓘`-envelopes along a quasi-equisingular approximation

The envelope part of the proof of `prop:mainKahcurr`
(`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`, lines 1211--1252):
for `φ ∈ PSH(X,θ)` with positive mass and a quasi-equisingular approximation `(φ_j)` of `φ`
**in `PSH(X,θ)`** (all `φ_j` are `θ`-psh), and a weighted subset `(K,v)`,

* `tendsto_sourceIEnvelope_of_qea` (`cor:quasi-equichar` in the class `θ` itself):
  `φ_j → P_θ[φ]_𝓘` in `d_S`;
* `qea_partialIEnvelope_decreasing` (the decreasing case of `prop:conv_of_K_env` applied to the
  limit `P_θ[φ]_𝓘`, and `P_{θ,K}[P_θ[φ]_𝓘]_𝓘(v) = P_{θ,K}[φ]_𝓘(v)`):
  `P_{θ,K}[φ_j]_𝓘(v) ↘ P_{θ,K}[φ]_𝓘(v)` pointwise;
* `qea_partialIEnvelope_mass_tendsto` (`eq:inproofeqmass`, via `thm:contvolu`):
  `∫_X θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} → ∫_X θⁿ_{P_{θ,K}[φ]_𝓘(v)}`;
* `qea_partialIEnvelope_weakTendsto` (`thm:semicon`):
  `θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}` against every continuous function.

The existing `cor:quasi-equichar` (`sourceQuasiEquisingular_enlarged_tendsto`) is stated in the
enlarged classes `θ + tω`; here all `φ_j` are `θ`-psh and we use the native fixed-class limit
`iInf_envelopes_eq_iEnvelope_and_native_limit` of SGPT.Foundations.Analysis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant3

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.MonotonePartialEnvelopes
open scoped Topology ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The `𝓘`-envelope `P_θ[φ]_𝓘` of a potential with positive mass has positive mass. -/
theorem sourceIEnvelope_pos (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceIEnvelope θ φ)
      (isThetaPSH_sourceIEnvelope hφ) univ := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have h := (originalIEnvelope_positive_iGood omega (atlasClosedFormToNative θ) φ hn hpos).1
  have he := sourceIEnvelope_eq_native θ φ hφ
  have hE : (ofFixedModel n X).IsThetaPSH θ
      (iSingularityEnvelope (atlasClosedFormToNative θ).val φ) := he ▸ isThetaPSH_sourceIEnvelope hφ
  rw [SGPT.Bergman.Quant2.sourcePotentialNonPluripolarMeasure_congr he _ hE]
  exact h

omit [BorelSpace X] in
/-- `vol(θ, P_θ[φ]_𝓘) = vol(θ, φ)`. -/
theorem sourceIVolume_sourceIEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) :
    sourceIVolume θ (sourceIEnvelope θ φ) (isThetaPSH_sourceIEnvelope hφ) =
      sourceIVolume θ φ hφ := by
  unfold sourceIVolume
  rw [SGPT.Bergman.Quant2.sourcePotentialNonPluripolarMeasure_congr
    (sourceIEnvelope_idempotent hφ) _ (isThetaPSH_sourceIEnvelope hφ)]

/-- **`cor:quasi-equichar` in the class `θ`**: a quasi-equisingular approximation `(φ_j)` of
`φ ∈ PSH(X,θ)_{>0}` all of whose terms are `θ`-psh converges to `P_θ[φ]_𝓘` in `d_S`. -/
theorem tendsto_sourceIEnvelope_of_qea (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {U : ℕ → X → EReal}
    (hQ : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) φ U)
    (hU : ∀ j, (ofFixedModel n X).IsThetaPSH θ (U j)) :
    Tendsto (fun j => (⟨U j, hU j⟩ : SourceThetaPotentialL1 θ)) atTop
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig)
        ⟨sourceIEnvelope θ φ, isThetaPSH_sourceIEnvelope hφ⟩) := by
  obtain ⟨kappa, ε, happ⟩ := native_of_sourceQuasiEquisingularApproximation hQ
  have hUn : ∀ j, IsThetaPshPotential (atlasClosedFormToNative θ).val (U j) := fun j =>
    (isThetaPSH_iff_nativeThetaPotential θ _).mp (hU j)
  obtain ⟨_, hI, _, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      kappa (atlasClosedFormToNative θ) hbig happ hUn hpos
  rw [sourceSingularity_tendsto_auxiliary_iff atTop omega kappa θ hbig,
    sourceSingularity_tendsto_iff_native atTop kappa θ hbig]
  have he := sourceIEnvelope_eq_native θ φ hφ
  have htarget : sourceThetaPotentialL1EquivNative θ
      ⟨sourceIEnvelope θ φ, isThetaPSH_sourceIEnvelope hφ⟩ =
        ⟨iSingularityEnvelope (atlasClosedFormToNative θ).val φ, hI⟩ :=
    Subtype.ext he
  rw [htarget]
  exact hlim

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The terms of a quasi-equisingular approximation decrease. -/
theorem antitone_of_sourceQEA {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    {U : ℕ → X → EReal} (hQ : SourceQuasiEquisingularApproximation θ φ U) : Antitone U :=
  fun _ _ hij x => hQ.2.2.1.1 x hij

omit [MeasurableSpace X] [BorelSpace X] in
/-- `P_{θ,K}[φ]_𝓘(v)` depends only on the `𝓘`-class of `φ`: it is unchanged when `φ` is
replaced by `P_θ[φ]_𝓘`. -/
theorem partialIEnvelope_sourceIEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) (K : Set X) (f : K → EReal) :
    partialIEnvelope θ (sourceIEnvelope θ φ) K f = partialIEnvelope θ φ K f :=
  le_antisymm (partialIEnvelope_mono_reference θ K f (sourceIEquivalent_iEnvelope hφ).2)
    (partialIEnvelope_mono_reference θ K f (sourceIEquivalent_iEnvelope hφ).1)

/-- **The decreasing case of `prop:conv_of_K_env` along a quasi-equisingular approximation**
(proof of `prop:mainKahcurr`): `P_{θ,K}[φ_j]_𝓘(v) ↘ P_{θ,K}[φ]_𝓘(v)` pointwise. -/
theorem qea_partialIEnvelope_decreasing (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {U : ℕ → X → EReal}
    (hQ : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) φ U)
    (hU : ∀ j, (ofFixedModel n X).IsThetaPSH θ (U j))
    (hUpos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (U j) (hU j) univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    Antitone (fun j => partialIEnvelope θ (U j) W.carrier W.erealWeight) ∧
      ∀ x, Tendsto (fun j => partialIEnvelope θ (U j) W.carrier W.erealWeight x) atTop
        (𝓝 (partialIEnvelope θ φ W.carrier W.erealWeight x)) := by
  have hu := isThetaPSH_sourceIEnvelope hφ
  have hupos := sourceIEnvelope_pos omega hφ hpos
  have hlim := tendsto_sourceIEnvelope_of_qea omega (sourcePositiveMass_isBig omega hu hupos)
    hφ hpos hQ hU
  obtain ⟨hanti, -, hx⟩ :=
    (partialEnvelopes_decreasing omega hU hUpos (antitone_of_sourceQEA hQ) hu hupos hlim W).2
  rw [partialIEnvelope_sourceIEnvelope hφ] at hx
  exact ⟨hanti, hx⟩

/-- Along a quasi-equisingular approximation in `PSH(X,θ)`, `vol(θ,φ_j) → vol(θ,φ)`
(`thm:contvolu` and `cor:quasi-equichar`). -/
theorem qea_sourceIVolume_tendsto (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {U : ℕ → X → EReal}
    (hQ : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) φ U)
    (hU : ∀ j, (ofFixedModel n X).IsThetaPSH θ (U j)) :
    Tendsto (fun j => sourceIVolume θ (U j) (hU j)) atTop (𝓝 (sourceIVolume θ φ hφ)) := by
  have hu := isThetaPSH_sourceIEnvelope hφ
  have hupos := sourceIEnvelope_pos omega hφ hpos
  have hbig := sourcePositiveMass_isBig omega hu hupos
  have hlim := tendsto_sourceIEnvelope_of_qea omega hbig hφ hpos hQ hU
  rw [← sourceIVolume_sourceIEnvelope hφ]
  exact (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology omega θ hbig atTop
    (fun j => ⟨U j, hU j⟩) ⟨sourceIEnvelope θ φ, hu⟩ hupos hlim).1

/-- **`eq:inproofeqmass`**: along a quasi-equisingular approximation,
`∫_X θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} → ∫_X θⁿ_{P_{θ,K}[φ]_𝓘(v)}` (both sides are `vol(θ,φ_j)` and
`vol(θ,φ)`, and `vol(θ,·)` is `d_S`-continuous, `thm:contvolu`). -/
theorem qea_partialIEnvelope_mass_tendsto (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {U : ℕ → X → EReal}
    (hQ : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) φ U)
    (hU : ∀ j, (ofFixedModel n X).IsThetaPSH θ (U j))
    (hUpos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (U j) (hU j) univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (hPj : ∀ j, (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ (U j) W.carrier W.erealWeight))
    (hP : (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ φ W.carrier W.erealWeight)) :
    Tendsto (fun j => sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ (U j) W.carrier W.erealWeight) (hPj j) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ W.carrier W.erealWeight) hP univ)) := by
  have hvol := qea_sourceIVolume_tendsto omega hφ hpos hQ hU
  have hmj : ∀ j, sourcePotentialNonPluripolarMeasure θ
      (partialIEnvelope θ (U j) W.carrier W.erealWeight) (hPj j) univ =
        sourceIVolume θ (U j) (hU j) := fun j =>
    SGPT.Bergman.Quant2.partialIEnvelope_mass_eq_sourceIVolume omega (hU j) (hUpos j)
      W.isClosed_carrier W.nonPluripolar_carrier W.weight (hPj j)
  have hm : sourcePotentialNonPluripolarMeasure θ
      (partialIEnvelope θ φ W.carrier W.erealWeight) hP univ = sourceIVolume θ φ hφ :=
    SGPT.Bergman.Quant2.partialIEnvelope_mass_eq_sourceIVolume omega hφ hpos
      W.isClosed_carrier W.nonPluripolar_carrier W.weight hP
  simp only [hmj, hm]
  exact hvol

/-- **`thm:semicon` along a quasi-equisingular approximation** (proof of `prop:mainKahcurr`):
`θⁿ_{P_{θ,K}[φ_j]_𝓘(v)} ⇀ θⁿ_{P_{θ,K}[φ]_𝓘(v)}`, i.e. the integrals of every continuous
function converge. -/
theorem qea_partialIEnvelope_weakTendsto (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {U : ℕ → X → EReal}
    (hQ : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) φ U)
    (hU : ∀ j, (ofFixedModel n X).IsThetaPSH θ (U j))
    (hUpos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (U j) (hU j) univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (hPj : ∀ j, (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ (U j) W.carrier W.erealWeight))
    (hP : (ofFixedModel n X).IsThetaPSH θ (partialIEnvelope θ φ W.carrier W.erealWeight))
    (g : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, g x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ (U j) W.carrier W.erealWeight) (hPj j)) atTop
      (𝓝 (∫ x, g x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ W.carrier W.erealWeight) hP)) := by
  obtain ⟨hanti, hx⟩ := qea_partialIEnvelope_decreasing omega hφ hpos hQ hU hUpos W
  have hmass := qea_partialIEnvelope_mass_tendsto omega hφ hpos hQ hU hUpos W hPj hP
  have hmono : SGPT.NPP.CapacityConvergence.SourceMonotoneLimit (n := n)
      (fun j => partialIEnvelope θ (U j) W.carrier W.erealWeight)
      (partialIEnvelope θ φ W.carrier W.erealWeight) :=
    Or.inl ⟨fun x _ _ hij => hanti hij x, hx⟩
  have hc : Continuous (fun _ : (⊤ : TopologicalSpace.Opens X) => (1 : ℝ)) := continuous_const
  have h := SGPT.NPP.CapacityConvergence.sourceSemicon_tendsto_integral omega θ
    (sourcePositiveMass_isBig omega hφ hpos) (fun _ : Fin n => θ)
    (φ := fun j _ => partialIEnvelope θ (U j) W.carrier W.erealWeight)
    (φ₀ := fun _ => partialIEnvelope θ φ W.carrier W.erealWeight)
    (fun j _ => hPj j) (fun _ => hP) (fun _ => hmono)
    (χ := fun _ _ => 1) (χ₀ := fun _ => 1) (C := 1)
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) (fun _ => ⟨zero_le_one, le_rfl⟩)
    (fun _ => sourceQuasiContinuousOn_of_continuous_real θ ⊤ hc)
    (sourceQuasiContinuousOn_of_continuous_real θ ⊤ hc)
    (SGPT.Envelopes.CapacityConsumers.sourceTendstoInCapacity_const_real θ measurable_const)
    (by simpa only [sourceMixedNonPluripolarMass_diagonal] using hmass) g
  simpa only [mul_one, sourceMixedNonPluripolarMeasure_diagonal] using h

end SGPT.Bergman.Quant3
