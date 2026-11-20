import SGPT.Trace.RestVolSections
import SGPT.Toric.NativeChernPullback
import SGPT.GAGA.H0LDXMain
import SGPT.Trace.TraceMultiplier
import SGPT.Trace.TraceMass
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

/-!
# Restricted multiplier sections and the trace: the lower bound of `thm:rest_volume`

Source: `chapter_trace.tex`, Section *Restricted volumes of line bundles*, `thm:rest_volume`.

Let `X` be a compact Kähler manifold, `(L, h₀)`, `(T, h_T)` holomorphic line bundles with smooth
Hermitian metrics, `θ = c₁(L, h₀)`, and `Y = W ⊆ X` a closed connected complex submanifold of
dimension `m`, with its induced complex structure and Kähler form.

* `restrictBundle L f` is the pullback `f^*L` along a holomorphic map `f : V → X` (for the
  inclusion of `W`, the restriction `L|_W`), with the restricted metric; its Chern form is
  geometrically the pullback `f^*θ` (`restrictBundle_chern_geometricallyEq`).
* `restrictedMultiplierIdeal hW k φ = Res_W 𝓘(kφ)` (`def:restidealsheaf`, `restrictIdeal` of the
  literal `𝓘(h^k) = 𝓘(kφ)`), and the book's
  `h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k))` is `idealH0 (L|_W) (T|_W) k (Res_W 𝓘(kφ))`.
* `sourceTraceMass_eq_sourceIVolume`: `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m = vol (Tr^θ_Y(φ))` for the
  Chern form of `L|_W`.
* `sourceDegreeMultiplierIdeal_trace_le_restrictIdeal`: `𝓘(k Tr^θ_Y(φ)) ⊆ Res_Y 𝓘(kφ)` (from
  `prop:OT2`, `SGPT.Trace.multiplierIdeal_trace_le_restrictIdeal`).
* **`sourceTraceMass_le_liminf_restrictedH0`** (the inequality `≤ liminf` of `thm:rest_volume`,
  for every `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` whose trace is defined): the book's
  `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m ≤ liminf_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

/-! ### Restriction of line bundles along holomorphic maps -/

section Bundle

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]

/-- The pullback `f^*L` of a Hermitian holomorphic line bundle along a holomorphic map
`f : V → X`, with the pulled-back metric (for the inclusion of a submanifold `Y`, the
restriction `L|_Y` of the book). -/
abbrev restrictBundle (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞) :
    HermitianHolomorphicLineBundle.{0, 0} m V :=
  SGPT.Toric.F1IntersectionDraft.nativeHolomorphicPullbackBundle L f

/-- The restricted metric is smooth. -/
theorem restrictBundle_smooth {L : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞) :
    IsSourceSmoothHermitianMetric (restrictBundle L f) :=
  SGPT.Toric.F1IntersectionDraft.nativeHolomorphicPullback_smooth L f hL

/-- `c₁(L|_V, h|_V) = f^* c₁(L, h)` (geometrically). -/
theorem restrictBundle_chern_geometricallyEq {L : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞) :
    (sourceNativeFirstChernForm (restrictBundle L f) (restrictBundle_smooth hL f)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback f.contMDiff (sourceNativeFirstChernForm L hL)).val :=
  SGPT.Toric.F1IntersectionDraft.nativeHolomorphicPullback_firstChern_geometrically L f hL _
    (sourceNativeFirstChernForm_isOwn L hL)

end Bundle

/-! ### Potentials and volumes for a Chern form geometrically equal to a given form -/

section Volume

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

/-- Potentials for the Chern form of `L` (atlas form) are the potentials of any form `η`
geometrically equal to it. -/
theorem isThetaPSH_chernForm_iff {L : HermitianHolomorphicLineBundle.{0, 0} m V}
    {hL : IsSourceSmoothHermitianMetric L} {η : ClosedRealOneOneForm m V}
    (hη : (sourceNativeFirstChernForm L hL).val.GeometricallyEq η.val) (u : V → EReal) :
    (ofFixedModel m V).IsThetaPSH (chernForm L hL) u ↔ IsThetaPshPotential η.val u := by
  rw [isThetaPSH_iff_nativeThetaPotential, sourceNativeAtlasForm_roundTrip]
  exact hη.thetaPshPotential_iff u

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [Nonempty V]

/-- `vol` for the Chern form of `L` is the native `𝓘`-volume for any geometrically equal form. -/
theorem sourceIVolume_chernForm_eq_iVolume {L : HermitianHolomorphicLineBundle.{0, 0} m V}
    {hL : IsSourceSmoothHermitianMetric L} {η : ClosedRealOneOneForm m V}
    (hη : (sourceNativeFirstChernForm L hL).val.GeometricallyEq η.val) {u : V → EReal}
    (hu : (ofFixedModel m V).IsThetaPSH (chernForm L hL) u) (hu' : IsThetaPshPotential η.val u) :
    sourceIVolume (chernForm L hL) u hu =
      iVolume η (LocalPotentials.closedRealOneOne_hasLocalPotentials η) u hu' := by
  rw [sourceIVolume_eq_native _ _ _ (LocalPotentials.closedRealOneOne_hasLocalPotentials _)]
  have hu₀ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val u :=
    (hη.thetaPshPotential_iff u).mpr hu'
  have key : ∀ (θ₁ : ClosedRealOneOneForm m V) (h₁ : θ₁ = sourceNativeFirstChernForm L hL)
      (hl : HasSmoothLocalPotentials θ₁.val) (hv : IsThetaPshPotential θ₁.val u),
      iVolume θ₁ hl u hv = iVolume (sourceNativeFirstChernForm L hL)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) u hu₀ := by
    rintro θ₁ rfl hl hv
    rfl
  rw [key _ (sourceNativeAtlasForm_roundTrip _)]
  exact SGPT.GAGA.H0L.iVolume_congr_geometricallyEq hη _ _ u hu₀ hu'

/-- The `𝓘`-volume of an `𝓘`-model potential is its mass. -/
theorem iVolume_eq_of_iModel {η : ClosedRealOneOneForm m V} {u : V → EReal}
    (hu : IsThetaPshPotential η.val u) (hI : u = iSingularityEnvelope η.val u) :
    iVolume η (LocalPotentials.closedRealOneOne_hasLocalPotentials η) u hu =
      diagonalPotentialMass η u hu := by
  have key : ∀ (a b : V → EReal) (_ : a = b) (ha : IsThetaPshPotential η.val a)
      (hb : IsThetaPshPotential η.val b),
      diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
    rintro a b rfl ha hb
    rfl
  exact key _ _ hI.symm _ _

end Volume

/-! ### The trace -/

section Trace

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- `Tr^θ_Y(φ)` is an `𝓘`-model potential of `θ|_Y`. -/
theorem sourceTraceEnvelope_eq_iSingularityEnvelope (hm : m ≤ n)
    (ωb : KahlerBackground n X) (ωV : KahlerBackground m V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ u) :
    SGPT.Trace.sourceTraceEnvelope ωb ωV hι θ u hdefined =
      iSingularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val
        (SGPT.Trace.sourceTraceEnvelope ωb ωV hι θ u hdefined) := by
  obtain ⟨hchosen, hσ, hσpos⟩ := Classical.choose_spec hdefined
  have h2 := (SGPT.Trace.sourceTraceEnvelope_eq_envelopes hm ωV ωV hι θ u hdefined hchosen hσ
    hσpos).2
  let η := ClosedRealOneOneForm.pullback hι θ
  rw [h2]
  exact (iSingularityEnvelope_idempotent η.val η.property.1 η.property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials η) _ hσ).symm

/-- The mass of `Tr^θ_Y(φ)` is the `𝓘`-volume of `Tr^θ_Y(φ)` for the Chern form of `L|_V`. -/
theorem sourceTraceMass_eq_sourceIVolume (hm : m ≤ n)
    (ωb : KahlerBackground n X) (ωV : KahlerBackground m V)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞) (u : X → EReal)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV f.contMDiff
      (sourceNativeFirstChernForm L hL) u) :
    ∃ hTr : (ofFixedModel m V).IsThetaPSH (chernForm (restrictBundle L f) (restrictBundle_smooth hL f))
        (SGPT.Trace.sourceTraceEnvelope ωb ωV f.contMDiff (sourceNativeFirstChernForm L hL) u
          hdefined),
      SGPT.Trace.sourceTraceMass ωb ωV f.contMDiff (sourceNativeFirstChernForm L hL) u =
        sourceIVolume (chernForm (restrictBundle L f) (restrictBundle_smooth hL f))
          (SGPT.Trace.sourceTraceEnvelope ωb ωV f.contMDiff (sourceNativeFirstChernForm L hL) u
            hdefined) hTr := by
  classical
  have hgeo := restrictBundle_chern_geometricallyEq hL f
  have hTr' := SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope ωb ωV f.contMDiff
    (sourceNativeFirstChernForm L hL) u hdefined
  have hTr := (isThetaPSH_chernForm_iff hgeo _).mpr hTr'
  refine ⟨hTr, ?_⟩
  rw [sourceIVolume_chernForm_eq_iVolume hgeo hTr hTr',
    iVolume_eq_of_iModel hTr' (sourceTraceEnvelope_eq_iSingularityEnvelope hm ωb ωV f.contMDiff
      (sourceNativeFirstChernForm L hL) u hdefined)]
  unfold SGPT.Trace.sourceTraceMass
  rw [dif_pos hdefined]

/-- **The lower bound, abstract form**: if `𝓘(k Tr^θ_Y(φ)) ⊆ 𝓡_k` for all `k ≥ 1` (whenever the
trace is defined), then `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m ≤ liminf_k m!/k^m h⁰(V, L|_V^k ⊗ T|_V ⊗ 𝓡_k)`
(the left side being `0` when the trace is not defined). -/
theorem sourceTraceMass_le_liminf_of_ideal (hm : m ≤ n)
    (ωb : KahlerBackground n X) (ωV : KahlerBackground m V)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞) (u : X → EReal)
    (R : ℕ → GermIdeal m V)
    (hR : ∀ hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV f.contMDiff
        (sourceNativeFirstChernForm L hL) u, ∀ k : ℕ, 0 < k →
      (sourceDegreeMultiplierIdeal (n := m) k (SGPT.Trace.sourceTraceEnvelope ωb ωV f.contMDiff
        (sourceNativeFirstChernForm L hL) u hdefined)).Le (R k)) :
    SGPT.Trace.sourceTraceMass ωb ωV f.contMDiff (sourceNativeFirstChernForm L hL) u ≤
      liminf (fun k => normalizedIdealH0 (restrictBundle L f) (restrictBundle T f) R k) atTop := by
  classical
  by_cases hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV f.contMDiff
      (sourceNativeFirstChernForm L hL) u
  · obtain ⟨hTr, heq⟩ := sourceTraceMass_eq_sourceIVolume hm ωb ωV hL f u hdefined
    rw [heq]
    exact le_liminf_normalizedIdealH0 ωV (restrictBundle_smooth hL f) (restrictBundle_smooth hT f)
      hTr (hR hdefined)
  · simp only [SGPT.Trace.sourceTraceMass, dif_neg hdefined, zero_le]

end Trace

/-! ### Submanifolds: the restricted multiplier ideals and `prop:OT2` -/

section Submanifold

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- The inclusion of a closed connected complex submanifold `W` of dimension `m`, as a
holomorphic map (for the induced complex structure). -/
def submanifoldInclusion {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
  ⟨Subtype.val, contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2⟩

/-- **`prop:OT2` for the normalized trace**: `𝓘(k Tr^θ_Y(φ)) ⊆ Res_Y 𝓘(kφ)` for every `k ≥ 1`. -/
theorem sourceDegreeMultiplierIdeal_trace_le_restrictIdeal (ωb : KahlerBackground n X)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (θ : ClosedRealOneOneForm n X) (u : X → EReal) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    ∀ hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2) θ u,
      ∀ k : ℕ, 0 < k →
        (sourceDegreeMultiplierIdeal (n := m) k (SGPT.Trace.sourceTraceEnvelope ωb
          (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2)
            θ u hdefined)).Le
          (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k u)) := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  intro hdefined k hk0
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb
  let η := ClosedRealOneOneForm.pullback (contMDiff_val hk hW.2.2) θ
  obtain ⟨htrace, hτ, -⟩ := Classical.choose_spec hdefined
  set τ := Classical.choose hdefined
  have hc : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  have hP := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ωW η hτ
  have hI := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP
  have h1 := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hI.2 hc
  have h2 := SGPT.Trace.multiplierIdeal_trace_le_restrictIdeal ωb hW htrace hc
  rw [sourceDegreeMultiplierIdeal_pos _ hk0, sourceDegreeMultiplierIdeal_pos _ hk0]
  intro p g hg
  exact h2 p g (h1 p g hg)

end Submanifold

end SGPT.Trace.RestVol
