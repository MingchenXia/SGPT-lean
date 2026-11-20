import SGPT.Trace.RestVolUpper
import SGPT.Trace.RestVolFrames
import SGPT.Trace.OTMarginGlobal
import SGPT.Trace.RestVolPoint

/-!
# Restricted volumes of line bundles: `thm:rest_volume` and `thm:rest_volume_2`

Source: `chapter_trace.tex`, Section *Restricted volumes of line bundles*.

Setting (the book's, analytically): `X` a compact Kähler manifold of dimension `n`, `(L, h₀)` and
`(T, h_T)` holomorphic line bundles with smooth Hermitian metrics, `θ = c₁(L, h₀)`, `Y = W ⊆ X` a
closed connected complex submanifold of dimension `m` with the induced complex structure and
Kähler form `ω|_W`; a (singular) psh metric `h = h₀ e^{-φ}` on `L` is a potential
`φ ∈ PSH(X, θ)`; `ν(dd^c h, Y) = ν(φ, Y)` is `sourceGenericLelongNumber Subtype.val φ`.

* `h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k))` is `idealH0 (L|_W) (T|_W) k (Res_W 𝓘(kφ))`
  (`restrictBundle`, `restrictIdeal`, `sourceDegreeMultiplierIdeal`), normalized in
  `normalizedIdealH0`;
* `∫_Y (Tr^{c₁(L|_Y)}_Y(c₁(L, h)))^m = ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m` is `sourceTraceMass`
  (`0` when the trace is not defined);
* `{s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))}` is `restrictedSectionImage` (the image of the
  restriction map `restrictSectionLinear`, a subspace of `H⁰(Y, (T ⊗ L^k)|_Y)`).

## Results

* `sourceTraceMass_le_liminf_restrictedH0` (**`thm:rest_volume`, the inequality `≤ liminf`**, for
  every `φ`);
* `tendsto_restrictedH0_of_kahlerCurrent` (**`thm:rest_volume` when `θ_φ` is a Kähler current**,
  `dim Y > 0`, Step 1 of the book's proof): `m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) → ∫_Y
  (θ|_Y + dd^c Tr^θ_Y(φ))^m`;
* `tendsto_restrictedSectionImage` (**`thm:rest_volume_2`**, `dim Y > 0`):
  `m!/k^m dim {s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))} → ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m` when `θ_φ`
  is a Kähler current, from `thm:DXmain1` on `Y`, `thm:OT_ext_global`
  (`SGPT.Trace.OTMargin.otExtGlobalStatement`) and the previous item.
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
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-! ### `dim Y = 0` -/

section PointBound

variable {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
  [IsComplexManifold 0 V] [CompactSpace V] [ConnectedSpace V]

theorem normalizedIdealH0_le_one_of_dim_zero (L' T' : HermitianHolomorphicLineBundle.{0, 0} 0 V)
    (R : ℕ → SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.GermIdeal 0 V) (k : ℕ) :
    normalizedIdealH0 L' T' R k ≤ 1 := by
  unfold normalizedIdealH0
  rw [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, one_mul, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have := twistedSections_finiteDimensional L' T' k
  rw [idealH0_eq_finrank]
  exact_mod_cast (Submodule.finrank_le _).trans (finrank_twistedSections_le_one_of_dim_zero L' T' k)

end PointBound

/-! ### `thm:rest_volume` -/

/-- **`thm:rest_volume`, the inequality `≤ liminf`** (from `thm:DXmain1` on `Y` and `prop:OT2`):
for every `φ` (no hypothesis is needed: the left side is `0` when `Tr^θ_Y(φ)` is not defined),
`∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m ≤ liminf_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ))`. -/
theorem sourceTraceMass_le_liminf_restrictedH0 (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) (φ : X → EReal) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    SGPT.Trace.sourceTraceMass ωb (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ ≤
      liminf (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
        atTop := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  exact sourceTraceMass_le_liminf_of_ideal hk ωb
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) hL hT (submanifoldInclusion hW) φ
    _ (sourceDegreeMultiplierIdeal_trace_le_restrictIdeal ωb hW _ φ)

/-- **`thm:rest_volume` when `θ_φ` is a Kähler current** (Step 1 of the book's proof), for
`dim Y > 0`: if `θ + dd^c φ ≥ κ` for a Kähler form `κ` and `ν(φ, Y) = 0`, then
`m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) → ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`. (The trace is
defined, `hasPositiveSourceTraceAlong_of_kahlerCurrent`, so the hypothesis
`eq:traceposmasscond2` of the book holds.) -/
theorem tendsto_restrictedH0_of_kahlerCurrent (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 (SGPT.Trace.sourceTraceMass ωb
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ)) := by
  intro hk
  obtain ⟨κ, hφκ⟩ := hφ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `Y` is a point
    let : ChartedSpace (ComplexModel 0) W := chartedSpace hk hW.2.2
    have : IsComplexManifold 0 W := isComplexManifold_chartedSpace hk hW.2.2
    have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    let : MeasurableSpace W := borel W
    have : BorelSpace W := ⟨rfl⟩
    have hval := contMDiff_val hk hW.2.2
    let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb
    have hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωW hval
        (sourceNativeFirstChernForm L hL) φ :=
      SGPT.Trace.hasPositiveSourceTraceAlong_of_kahlerCurrent hk ωb κ ωW hval
        (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 κ.form κ.isKahler) one_pos
        (by rwa [one_smul]) hν
    refine tendsto_of_le_liminf_of_limsup_le
      (sourceTraceMass_le_liminf_restrictedH0 ωb hL hT hW φ) ?_
    rw [sourceTraceMass_eq_one_of_dim_zero ωb ωW hval _ φ hdefined]
    exact limsup_le_of_le (by isBoundedDefault)
      (Eventually.of_forall fun k => normalizedIdealH0_le_one_of_dim_zero _ _ _ k)
  · have hn : n ≠ 0 := by omega
    exact tendsto_of_le_liminf_of_limsup_le
      (sourceTraceMass_le_liminf_restrictedH0 ωb hL hT hW φ)
      (limsup_restrictedH0_le_of_kahlerCurrent hn ωb hL hT hW hm hφκ hν)

/-! ### `thm:rest_volume_2` -/

section Image

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

/-- **`{s|_V : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))}`**, the image of the restriction map, a subspace of
`H⁰(V, (T ⊗ L^k)|_V)`. -/
def restrictedSectionImage (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (k : ℕ) (φ : X → EReal) :
    Submodule ℂ (twistedSections (restrictBundle L f) (restrictBundle T f) k) :=
  (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)).map (restrictSectionLinear f k)

/-- `m!/k^m dim {s|_V : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))}`. -/
def normalizedRestrictedImageDim
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (φ : X → EReal) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((m.factorial : ℝ) / (k : ℝ) ^ m *
    Module.finrank ℂ (restrictedSectionImage f L T k φ))

end Image

/-- The upper half of the comparison in `thm:rest_volume_2`:
`dim {s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))} ≤ h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ))`. -/
theorem normalizedRestrictedImageDim_le_restrictedH0
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) {φ : X → EReal}
    (hφq : IsGlobalQuasiPshPotential (n := n) φ) (k : ℕ) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    normalizedRestrictedImageDim (submanifoldInclusion hW) L T φ k ≤
      normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let f := submanifoldInclusion hW
  have := twistedSections_finiteDimensional (restrictBundle L f) (restrictBundle T f) k
  unfold normalizedRestrictedImageDim normalizedIdealH0
  apply ENNReal.ofReal_le_ofReal
  have h0 : (0 : ℝ) ≤ (m.factorial : ℝ) / (k : ℝ) ^ m := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h0
  rw [idealH0_eq_finrank]
  have hle : restrictedSectionImage f L T k φ ≤ fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L f) (restrictBundle T f) k).Fiber
      (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) := by
    rintro _ ⟨s, hs, rfl⟩
    exact restrictSection_mem_restrictIdeal hval hφq hs
  exact_mod_cast Submodule.finrank_mono hle

/-- The lower half of `thm:rest_volume_2` (from `thm:DXmain1` on `Y` and `thm:OT_ext_global`), for
every `dim Y`: if `θ_φ` is a Kähler current and `ν(φ, Y) = 0`, then
`∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m ≤ liminf_k m!/k^m dim {s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))}`. -/
theorem sourceTraceMass_le_liminf_restrictedImage [MeasurableSpace X] [BorelSpace X]
    (ωb : KahlerBackground n X) {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    SGPT.Trace.sourceTraceMass ωb (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ ≤
      liminf (fun k => normalizedRestrictedImageDim (submanifoldInclusion hW) L T φ k) atTop := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let f := submanifoldInclusion hW
  let θ := sourceNativeFirstChernForm L hL
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb
  obtain ⟨κ, hφκ⟩ := id hφ
  have hLW := restrictBundle_smooth hL f
  have hTW := restrictBundle_smooth hT f
  have := fun k => twistedSections_finiteDimensional (restrictBundle L f) (restrictBundle T f) k
  have hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωW hval θ φ :=
    SGPT.Trace.hasPositiveSourceTraceAlong_of_kahlerCurrent hk ωb κ ωW hval
      (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 κ.form κ.isKahler) one_pos
      (by rwa [one_smul]) hν
  obtain ⟨hTr, hmass⟩ := sourceTraceMass_eq_sourceIVolume hk ωb ωW hL f φ hdefined
  set Tr := SGPT.Trace.sourceTraceEnvelope ωb ωW hval θ φ hdefined with hTrdef
  have hTrq : IsGlobalQuasiPshPotential (n := m) Tr :=
    (SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope ωb ωW hval θ φ hdefined).quasiPshPotential
  have hOT := SGPT.Trace.OTMargin.otExtGlobalStatement n X ωb L T hL hT θ
    (sourceNativeFirstChernForm_isOwn L hL) φ hφ W m hW hν hdefined
  obtain ⟨k₀, hk₀⟩ := hOT
  obtain ⟨hTr', hDX⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωW hLW hTW hTr
  rw [hmass]
  refine (le_of_eq (sourceIVolume_proof_independent _ _ hTr hTr')).trans (hDX.trans ?_)
  refine liminf_le_liminf ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  unfold normalizedH0 normalizedRestrictedImageDim
  apply ENNReal.ofReal_le_ofReal
  have h0 : (0 : ℝ) ≤ (m.factorial : ℝ) / (k : ℝ) ^ m := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h0
  rw [finrank_literal_eq]
  have hle : fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L f) (restrictBundle T f) k).Fiber
      (sourceDegreeMultiplierIdeal (n := m) k Tr) ≤ restrictedSectionImage f L T k φ := by
    intro t ht
    have halong := isAlongMultiplierSection_of_mem (L := L) (T := T) hval hTrq ht
    obtain ⟨s', hs', hrestr⟩ := hk₀ k hk _ halong
    refine ⟨s', hs', ?_⟩
    ext y
    change (twistedFiberEquiv f L T y k).symm (s' (f y)) = t y
    rw [show s' (f y) = twistedFiberEquiv f L T y k (t y) from hrestr y,
      LinearEquiv.symm_apply_apply]
  exact_mod_cast Submodule.finrank_mono hle

/-- **`thm:rest_volume_2`**: if `θ_φ` is a Kähler current and `ν(φ, Y) = 0`, then for every
twist `T`,
`m!/k^m dim {s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))} → ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`. -/
theorem tendsto_restrictedSectionImage [MeasurableSpace X] [BorelSpace X]
    (ωb : KahlerBackground n X) {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    Tendsto (fun k => normalizedRestrictedImageDim (submanifoldInclusion hW) L T φ k)
      atTop (𝓝 (SGPT.Trace.sourceTraceMass ωb
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ)) := by
  intro hk
  have hφq : IsGlobalQuasiPshPotential (n := n) φ := by
    obtain ⟨κ, hφκ⟩ := hφ
    exact hφκ.quasiPshPotential
  refine tendsto_of_le_liminf_of_limsup_le
    (sourceTraceMass_le_liminf_restrictedImage ωb hL hT hW hφ hν) ?_
  refine le_trans (limsup_le_limsup (Eventually.of_forall fun k =>
    normalizedRestrictedImageDim_le_restrictedH0 hW hφq k)) ?_
  exact (tendsto_restrictedH0_of_kahlerCurrent ωb hL hT hW hφ hν).limsup_eq.le

end SGPT.Trace.RestVol
