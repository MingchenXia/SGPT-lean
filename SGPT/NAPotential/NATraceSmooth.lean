import SGPT.NAPotential.PLCurveNAPotential
import SGPT.NAPotential.ModificationPullback
import SGPT.Trace.TraceEnvelope
import SGPT.Trace.DecreasingNetTrace
import SGPT.Okounkov.SourceTraceOperations
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceIdealEquivalenceOperations

/-! # The trace operator of a non-Archimedean metric along a smooth subvariety

Source `def:NApotential:L623` (`chapter_NApotential.tex`), for `Y` smooth (so `Ỹ = Y`): for
`Γ ∈ PSH^NA(X, θ)` the trace of `Γ` along `Y` is *well-defined* if `ν(Γ^{θ+ω}_τ, Y) = 0` for all
sufficiently negative `τ` and every `ω ∈ Kah(X)`; then
`(Tr_Y Γ)_max := sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}` (independent of `ω`), and
`Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)` is the unique element whose component at `ω ∈ Kah(Y)` has cutoff
`(Tr_Y Γ)_max` and slices `P_{θ|_Y+ω}[Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)]_𝓘`; *the choice of the trace
operator is irrelevant since two different choices are `𝓘`-equivalent*.

## Formal setting

`Y` is given by a holomorphic map `ι : V → X` from a compact connected complex manifold `V`
whose pullbacks of Kähler forms are Kähler (e.g. the inclusion of a closed connected complex
submanifold); `θ|_Y` is the pullback `ι^*θ`.  Trace operators are the workspace's
`IsSourceTraceRepresentativeAlong` (`def:traceop`) and `ν(φ, Y)` its generic Lelong number
`sourceGenericLelongNumber`.

We fix an auxiliary Kähler form `ω_0` of `X` and a chosen trace operator `ψ_τ` of the slice
`Γ^{θ+ω_0}_τ` (`traceSlice`); the component of `Tr_Y(Γ)` at `κ ∈ Kah(Y)` has cutoff
`(Tr_Y Γ)_max` and slices `P_{ι^*θ+κ}[ψ_τ]_𝓘` (`traceComponentSlice`).  This agrees with the
book's `P_{θ|_Y+κ}[Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)]_𝓘` for every `ω̃` and every choice of trace operator,
because the slices of different components are `𝓘`-equivalent, trace operators of
`𝓘`-ordered functions are `P`-ordered (`prop:traceunique`, `prop:tracelinear`), and the
`𝓘`-envelope only depends on the `𝓘`-class.

## Main results

* `SliceTraceable`, `TraceWellDefined`, `traceCutoff`, `traceCutoff_independent`: the
  well-definedness condition and `(Tr_Y Γ)_max`, independent of `ω`.
* `exists_good_traceSlice`: up to `P`-equivalence the trace of a slice lies in
  `PSH(Y, θ|_Y + ½κ)` (via `Tr^{θ+ω̃+ω}_Y` with `ω̃, ω` small, `def:traceop2`).
* `traceComponentSlice_antitone`, `traceComponentSlice_chord`: the slices decrease and are
  concave in `τ` (trace of convex combinations, `prop:tracelinear`).
* `naTrace`: `Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)`; `naTrace_max`, `naTrace_potential`,
  `naTrace_potential_traceEnvelope`, `naTrace_unique`.
* `source_naTrace`, `source_naTrace_submanifold`: source `def:NApotential:L623` for smooth `Y`
  (a holomorphic map with Kähler pullbacks, resp. a closed connected complex submanifold).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NATrace

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas
open scoped Manifold ContDiff

universe u

variable {n k : ℕ} {X V : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-! ### Slices of different components -/

/-- For `κ ≤ ζ`, the slice of the component at `ζ` is the `𝓘`-envelope of that at `κ`. -/
theorem component_potential_of_le (Γ : SourceNAPotential θ) {κ ζ : SourceKahlerForm n X}
    (h : sourceKahlerFormLE κ ζ) (r : ℝ) (hr : r < (Γ.component κ).val.max)
    (hs : r < (Γ.component ζ).val.max) :
    (Γ.component ζ).val.potential ⟨r, hs⟩ =
      sourceIEnvelope (sourceNAComponentBackground θ ζ)
        ((Γ.component κ).val.potential ⟨r, hr⟩) := by
  have hc := Γ.compatible κ ζ h
  have ht : r < (sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference θ h) (Γ.component κ)).val.max := by
    rwa [sourceIModelTestCurveTransition_max]
  have key : ∀ (G H : SourcePositiveIModelTestCurve (sourceNAComponentBackground θ ζ)),
      G = H → ∀ (hG : r < G.val.max) (hH : r < H.val.max),
        G.val.potential ⟨r, hG⟩ = H.val.potential ⟨r, hH⟩ := by
    intro G H hGH hG hH
    subst hGH
    rfl
  rw [← key _ _ hc ht hs]
  exact sourceIModelTestCurveTransition_potential _ _ _ r hr ht

/-- Corresponding slices of any two components of `Γ` are `𝓘`-equivalent. -/
theorem component_potential_iEquivalent (Γ : SourceNAPotential θ)
    (κ ζ : SourceKahlerForm n X) (r : ℝ) (hr : r < (Γ.component κ).val.max)
    (hs : r < (Γ.component ζ).val.max) :
    sourceIEquivalent (ofFixedModel n X) ((Γ.component κ).val.potential ⟨r, hr⟩)
      ((Γ.component ζ).val.potential ⟨r, hs⟩) := by
  let ξ := sourceKahlerFormCommonUpper κ ζ
  have hξ : r < (Γ.component ξ).val.max := by rwa [Γ.component_max_eq ξ κ]
  have h1 : sourceIEquivalent (ofFixedModel n X) ((Γ.component κ).val.potential ⟨r, hr⟩)
      ((Γ.component ξ).val.potential ⟨r, hξ⟩) := by
    rw [component_potential_of_le Γ (sourceKahlerFormLE_commonUpper_left κ ζ) r hr hξ]
    exact sourceIEquivalent_iEnvelope (sourceThetaPSH_of_semipositive_difference
      (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_left κ ζ))
      ((Γ.component κ).val.thetaPSH ⟨r, hr⟩))
  have h2 : sourceIEquivalent (ofFixedModel n X) ((Γ.component ζ).val.potential ⟨r, hs⟩)
      ((Γ.component ξ).val.potential ⟨r, hξ⟩) := by
    rw [component_potential_of_le Γ (sourceKahlerFormLE_commonUpper_right κ ζ) r hs hξ]
    exact sourceIEquivalent_iEnvelope (sourceThetaPSH_of_semipositive_difference
      (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_right κ ζ))
      ((Γ.component ζ).val.thetaPSH ⟨r, hs⟩))
  exact sourceIEquivalent_trans h1 (sourceIEquivalent_symm h2)

/-! ### The generic Lelong condition and the cutoff `(Tr_Y Γ)_max` -/

/-- `ν(Γ^{θ+κ}_τ, Y) = 0` for a parameter `τ < Γ_max`. -/
def SliceTraceable (ι : V → X) (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X)
    (τ : ℝ) : Prop :=
  ∃ h : τ < (Γ.component κ).val.max,
    sourceGenericLelongNumber (n := n) ι ((Γ.component κ).val.potential ⟨τ, h⟩) = 0

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The condition does not depend on the Kähler index. -/
theorem sliceTraceable_index (ι : V → X) (Γ : SourceNAPotential θ)
    {κ ζ : SourceKahlerForm n X} {τ : ℝ} (h : SliceTraceable ι Γ κ τ) :
    SliceTraceable ι Γ ζ τ := by
  obtain ⟨hτ, h0⟩ := h
  have hτ' : τ < (Γ.component ζ).val.max := by rwa [Γ.component_max_eq ζ κ]
  have he := component_potential_iEquivalent Γ κ ζ τ hτ hτ'
  refine ⟨hτ', ?_⟩
  exact SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
    ((Γ.component κ).val.native_thetaPSH ⟨τ, hτ⟩)
    ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1) h0

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The condition descends to smaller parameters. -/
theorem sliceTraceable_of_le (ι : V → X) (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X)
    {τ τ' : ℝ} (h : SliceTraceable ι Γ κ τ') (hle : τ ≤ τ') : SliceTraceable ι Γ κ τ := by
  obtain ⟨hτ', h0⟩ := h
  have hτ : τ < (Γ.component κ).val.max := lt_of_le_of_lt hle hτ'
  refine ⟨hτ, ?_⟩
  have hmono : ∀ x, (Γ.component κ).val.potential ⟨τ', hτ'⟩ x ≤
      (Γ.component κ).val.potential ⟨τ, hτ⟩ x := fun x =>
    (Γ.component κ).val.antitone x (show (⟨τ, hτ⟩ : Iio _) ≤ ⟨τ', hτ'⟩ from hle)
  exact SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
    ((Γ.component κ).val.native_thetaPSH ⟨τ', hτ'⟩)
    (iOrderOnManifold_of_le_add (C := 0)
      ((Γ.component κ).val.native_thetaPSH ⟨τ, hτ⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hmono x)) h0

/-- Source `def:NApotential:L623`: the trace of `Γ` along `Y` is well-defined if
`ν(Γ^{θ+ω}_τ, Y) = 0` for all sufficiently negative `τ` and every Kähler form `ω`. -/
def TraceWellDefined (ι : V → X) (Γ : SourceNAPotential θ) : Prop :=
  ∀ κ : SourceKahlerForm n X, ∃ τ₀ : ℝ, ∀ τ < τ₀, SliceTraceable ι Γ κ τ

/-- Source `def:NApotential:L623`:
`(Tr_Y Γ)_max := sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}`, computed at the Kähler index `κ`. -/
def traceCutoff (ι : V → X) (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X) : ℝ :=
  sSup {τ | SliceTraceable ι Γ κ τ}

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- `(Tr_Y Γ)_max` does not depend on the Kähler index. -/
theorem traceCutoff_independent (ι : V → X) (Γ : SourceNAPotential θ)
    (κ ζ : SourceKahlerForm n X) : traceCutoff ι Γ κ = traceCutoff ι Γ ζ := by
  unfold traceCutoff
  congr 1
  ext τ
  exact ⟨sliceTraceable_index ι Γ, sliceTraceable_index ι Γ⟩

omit [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
theorem traceCutoff_set_nonempty {ι : V → X} {Γ : SourceNAPotential θ}
    (hwd : TraceWellDefined ι Γ) (κ : SourceKahlerForm n X) :
    {τ | SliceTraceable ι Γ κ τ}.Nonempty := by
  obtain ⟨τ₀, h⟩ := hwd κ
  exact ⟨τ₀ - 1, h _ (by linarith)⟩

omit [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
theorem traceCutoff_set_bddAbove (ι : V → X) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n X) : BddAbove {τ | SliceTraceable ι Γ κ τ} :=
  ⟨(Γ.component κ).val.max, fun _ h => h.1.le⟩

omit [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
/-- `(Tr_Y Γ)_max ≤ Γ_max`. -/
theorem traceCutoff_le_max {ι : V → X} {Γ : SourceNAPotential θ}
    (hwd : TraceWellDefined ι Γ) (κ : SourceKahlerForm n X) :
    traceCutoff ι Γ κ ≤ (Γ.component κ).val.max :=
  csSup_le (traceCutoff_set_nonempty hwd κ) fun _ h => h.1.le

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- Every parameter below `(Tr_Y Γ)_max` satisfies the generic Lelong condition. -/
theorem sliceTraceable_of_lt_traceCutoff {ι : V → X} {Γ : SourceNAPotential θ}
    (hwd : TraceWellDefined ι Γ) (κ : SourceKahlerForm n X) {τ : ℝ}
    (hτ : τ < traceCutoff ι Γ κ) : SliceTraceable ι Γ κ τ := by
  obtain ⟨s, hs, hτs⟩ := exists_lt_of_lt_csSup (traceCutoff_set_nonempty hwd κ) hτ
  exact sliceTraceable_of_le ι Γ κ hs hτs.le


/-! ### Trace operators of the slices -/

section Traces

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

omit [BorelSpace X] [ConnectedSpace X] in
theorem slice_globalQPSH {α : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (G : SourceTestCurve α) (r : Iio G.max) :
    IsGlobalQuasiPshPotential (n := n) (G.potential r) :=
  ⟨(G.native_thetaPSH r).1.quasiPlurisubharmonic, (G.native_thetaPSH r).2⟩

/-- A chosen trace operator `Tr_Y(Γ^{θ+ω_0}_τ)` of the slice of `Γ` at the reference Kähler
index `ω_0 = omegaX`, for a parameter satisfying the generic Lelong condition. -/
def traceSlice (Γ : SourceNAPotential θ) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) : V → EReal :=
  Classical.choose (SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (slice_globalQPSH (Γ.component (sourceKahlerFormOfBackground omegaX)).val ⟨τ, hτ.1⟩)
    hι hτ.2)

theorem traceSlice_spec (Γ : SourceNAPotential θ) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    IsSourceTraceRepresentativeAlong omegaX omegaV hι
      ((Γ.component (sourceKahlerFormOfBackground omegaX)).val.potential ⟨τ, hτ.1⟩)
      (traceSlice hk omegaX omegaV hι Γ τ hτ) :=
  Classical.choose_spec (SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk
    omegaX omegaV (slice_globalQPSH (Γ.component (sourceKahlerFormOfBackground omegaX)).val
      ⟨τ, hτ.1⟩) hι hτ.2)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- A trace operator is quasi-psh on `V`. -/
theorem isQPSH_of_sourceTrace {omega : KahlerBackground n X} {omegaW : KahlerBackground k V}
    {u : X → EReal} {ψ : V → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega omegaW hι u ψ) :
    (ofFixedModel k V).IsQPSH ψ := by
  obtain ⟨_h0, _θ', _ε, _uSeq, _hqea, β, _hβ, hψ, _hterms, _hlim⟩ := hT
  refine ⟨nativeClosedFormToAtlas β.form, (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_⟩
  rwa [sourceNativeAtlasForm_roundTrip]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_add' (a b : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (a + b) =
      ClosedRealOneOneForm.pullback hι a + ClosedRealOneOneForm.pullback hι b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_smul' (c : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (c • a) = c • ClosedRealOneOneForm.pullback hι a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- The trace operator of a slice has, up to `P`-equivalence, a representative in
`PSH(V, ι^*θ + ½ κ)` for every Kähler form `κ` on `V`. -/
theorem exists_good_traceSlice
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ φ : V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ ∧
      SingularGlobalPOrder.SourcePEquivalent (n := k) φ
        (traceSlice hk omegaX omegaV hι Γ τ hτ) := by
  obtain ⟨c, hc, hsemi⟩ := WholeClosureNA.exists_small_semipositive_difference
    (sourceKahlerFormRepresentative κV) (ClosedRealOneOneForm.pullback hι omegaX.form)
  have hε : (0 : ℝ) < c / 4 := by positivity
  let ωε := KahlerBackground.smul hε omegaX
  let κε := sourceKahlerFormOfBackground ωε
  have hτε : SliceTraceable ι Γ κε τ := sliceTraceable_index ι Γ hτ
  have hrmax : τ < (Γ.realizedComponent ωε).val.max := by
    rw [Γ.realizedComponent_max]
    exact hτε.1
  have hreal := Γ.realizedComponent_potential ωε τ hτε.1 hrmax
  have hu'nat : IsThetaPshPotential (atlasClosedFormToNative θ + ωε.form).val
      ((Γ.component κε).val.potential ⟨τ, hτε.1⟩) := by
    have h := (Γ.realizedComponent ωε).val.native_thetaPSH ⟨τ, hrmax⟩
    rw [hreal, sourceTestCurveEnlargedBackground_native] at h
    exact h
  obtain ⟨ψ', hT', hψ', _hpos⟩ := SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler hk omegaX ωε
    omegaV hι (hpull ωε) hu'nat hτε.2
  have hI := component_potential_iEquivalent Γ κε (sourceKahlerFormOfBackground omegaX) τ
    hτε.1 hτ.1
  have hspec := traceSlice_spec hk omegaX omegaV hι Γ τ hτ
  have h1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hT' hspec ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1)
  have h2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hspec hT' ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2)
  refine ⟨ψ', ?_, h1, h2⟩
  set P := ClosedRealOneOneForm.pullback hι omegaX.form
  set β := ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ)
  set K := (sourceKahlerFormRepresentative κV).form
  have hpb : ClosedRealOneOneForm.pullback hι ((atlasClosedFormToNative θ + ωε.form) + ωε.form) =
      β + (c / 4) • P + (c / 4) • P := by
    rw [pullback_add' hι, pullback_add' hι]
    simp only [ωε, KahlerBackground.smul_form, pullback_smul' hι]
    rfl
  rw [hpb] at hψ'
  have hsemi' : ((1 / 2 : ℝ) • (K - c • P)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul hsemi (by norm_num)
  have hadd := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ' hsemi'
  have heq : β + (c / 4) • P + (c / 4) • P + (1 / 2 : ℝ) • (K - c • P) =
      β + (1 / 2 : ℝ) • K := by
    rw [smul_sub, smul_smul]
    have : (c / 4) • P + (c / 4) • P = ((1 / 2 : ℝ) * c) • P := by
      rw [← add_smul]
      congr 1
      ring
    rw [add_assoc β, this]
    abel
  rw [heq] at hadd
  exact hadd

end Traces

/-! ### The components of `Tr_Y(Γ)` -/

section Components

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
/-- The background of the component of `Tr_Y(Γ)` at `κ`: `ι^*θ + κ`. -/
theorem traceBackground_native (κV : SourceKahlerForm k V) :
    atlasClosedFormToNative (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) =
      ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (sourceKahlerFormRepresentative κV).form := by
  rw [sourceNAComponentBackground_native]
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback, sourceNativeAtlasForm_roundTrip]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
theorem thetaPSH_traceBackground_of_half (κV : SourceKahlerForm k V) {φ : V → EReal}
    (hφ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ) :
    (ofFixedModel k V).IsThetaPSH (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
      φ := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [traceBackground_native hι κV]
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
    (KahlerDomination.isSemipositive_smul (sourceKahlerFormRepresentative κV).isSemipositive
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have heq : ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
      (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form +
      (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form =
      ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (sourceKahlerFormRepresentative κV).form := by
    rw [add_assoc, ← add_smul]
    norm_num
  rwa [heq] at h

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The `𝓘`-envelope in `ι^*θ + κ` of a `(ι^*θ + ½κ)`-psh function has mass at least
`2^{-k} ∫ κ^k > 0`. -/
theorem iEnvelope_traceBackground_mass_pos (κV : SourceKahlerForm k V) {φ : V → EReal}
    (hφ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ) :
    0 < sourcePotentialNonPluripolarMeasure
      (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
      (sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) φ)
      (isThetaPSH_sourceIEnvelope (thetaPSH_traceBackground_of_half hι κV hφ)) univ := by
  let K := sourceKahlerFormRepresentative κV
  let α := sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV
  have hφα := thetaPSH_traceBackground_of_half hι κV hφ
  have hform : atlasClosedFormToNative α =
      (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) + (1 / 2 : ℝ) • K.form) +
        (1 / 2 : ℝ) • K.form := by
    rw [traceBackground_native hι κV, add_assoc, ← add_smul]
    norm_num
    rfl
  have hnat : IsThetaPshPotential ((ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
      (1 / 2 : ℝ) • K.form) + (1 / 2 : ℝ) • K.form).val φ :=
    hform ▸ (isThetaPSH_iff_nativeThetaPotential _ _).mp hφα
  have hlow := sourceNA_diagonalMass_add_smul_lower_bound K hφ (by norm_num : (0 : ℝ) < 1 / 2) hnat
  have hK : 0 < ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (DiagonalMass.diagonalPotentialMass K.form
      (fun _ => 0) (PluripolarCapacityDichotomy.isThetaPshPotential_zero K)).toReal) := by
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by positivity)
    exact ENNReal.toReal_pos (KahlerVolumePositive.diagonalPotentialMass_zero_pos _).ne'
      (MixedMass.globalMixedMass_lt_top K
        (fun _ : Fin k => (PluripolarCapacityDichotomy.isThetaPshPotential_zero K).1)).ne
  have hm : DiagonalMass.diagonalPotentialMass ((ClosedRealOneOneForm.pullback hι
      (atlasClosedFormToNative θ) + (1 / 2 : ℝ) • K.form) + (1 / 2 : ℝ) • K.form) φ hnat =
      sourcePotentialNonPluripolarMeasure α φ hφα univ :=
    sourceNA_diagonalMass_congr_form hform.symm _ _
  exact (hK.trans_le hlow).trans_le (hm.trans_le
    (sourcePotentialNonPluripolarMass_mono K hφα _ (sourceSingularityLE_sourceIEnvelope hφα)))

/-- A good representative of the trace slice in the background `ι^*θ + κ`. -/
theorem exists_good_traceSlice'
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ φ : V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ ∧
      sourceIEquivalent (ofFixedModel k V) φ (traceSlice hk omegaX omegaV hι Γ τ hτ) := by
  obtain ⟨φ, hφ, hP⟩ := exists_good_traceSlice hk omegaX omegaV hι hpull Γ κV τ hτ
  have hq1 : (ofFixedModel k V).IsQPSH φ :=
    ⟨_, thetaPSH_traceBackground_of_half hι κV hφ⟩
  have hq2 := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ hτ)
  exact ⟨φ, hφ, sourceIOrder_of_sourcePOrder hq1 hq2 hP.1,
    sourceIOrder_of_sourcePOrder hq2 hq1 hP.2⟩

/-- The slice of the component of `Tr_Y(Γ)` at `κ`: `P_{ι^*θ+κ}[Tr_Y(Γ^{θ+ω_0}_τ)]_𝓘`. -/
def traceComponentSlice (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) : V → EReal :=
  sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
    (traceSlice hk omegaX omegaV hι Γ τ hτ)

theorem traceComponentSlice_eq (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) {φ : V → EReal}
    (hφ : sourceIEquivalent (ofFixedModel k V) φ (traceSlice hk omegaX omegaV hι Γ τ hτ)) :
    traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) φ :=
  sourceIEnvelope_eq_of_equivalent (sourceIEquivalent_symm hφ)

theorem traceComponentSlice_props
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V)
    (τ : ℝ) (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ hP : (ofFixedModel k V).IsThetaPSH
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ),
      sourceIModel (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ) ∧
      0 < sourcePotentialNonPluripolarMeasure
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ) hP univ := by
  obtain ⟨φ, hφ, hE⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV τ hτ
  have hφα := thetaPSH_traceBackground_of_half hι κV hφ
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ hτ hE]
  exact ⟨isThetaPSH_sourceIEnvelope hφα, sourceIEnvelope_isIModel hφα,
    iEnvelope_traceBackground_mass_pos hι κV hφ⟩

end Components

/-! ### Monotonicity and concavity of the trace slices -/

section Curve

open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem thetaPSH_convexComb' {α : AtlasClosedRealOneOneForm (ofFixedModel k V)}
    {u v : V → EReal}
    (hu : (ofFixedModel k V).IsThetaPSH α u) (hv : (ofFixedModel k V).IsThetaPSH α v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (ofFixedModel k V).IsThetaPSH α (convexComb t u v) :=
  (isThetaPSH_iff_nativeThetaPotential α _).mpr
    (isThetaPshPotential_convexComb ((isThetaPSH_iff_nativeThetaPotential α u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential α v).mp hv) ht0 ht1)

omit [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem convexComb_nonpos' {u v : V → EReal} (hu : u ≤ 0) (hv : v ≤ 0) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : convexComb t u v ≤ 0 := by
  intro x
  rw [convexComb_apply]
  have hux : u x ≤ 0 := hu x
  have hvx : v x ≤ 0 := hv x
  have h1 : (t : EReal) * u x ≤ 0 := by
    simpa only [mul_zero] using mul_le_mul_of_nonneg_left hux (EReal.coe_nonneg.mpr ht0.le)
  have h2 : ((1 - t : ℝ) : EReal) * v x ≤ 0 := by
    simpa only [mul_zero] using
      mul_le_mul_of_nonneg_left hvx (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le)
  simpa only [add_zero, Pi.zero_apply] using add_le_add h1 h2

private theorem ereal_convex_self' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : EReal) :
    (t : EReal) * a + ((1 - t : ℝ) : EReal) * a = a := by
  induction a with
  | bot => simp only [EReal.coe_mul_bot_of_pos ht0,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr ht1), EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos ht0,
      EReal.coe_mul_top_of_pos (sub_pos.mpr ht1), EReal.top_add_top]
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

omit [MeasurableSpace V] [BorelSpace V] [ConnectedSpace V] in
/-- The `𝓘`-order version of the chord lemma for `𝓘`-envelopes. -/
theorem convexComb_sourceIEnvelope_le_of_iOrder [Nonempty V]
    {α : AtlasClosedRealOneOneForm (ofFixedModel k V)} {φ ψ χ : V → EReal}
    (hφ : (ofFixedModel k V).IsThetaPSH α φ) (hψ : (ofFixedModel k V).IsThetaPSH α ψ)
    (hχ : (ofFixedModel k V).IsThetaPSH α χ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hI : sourceIOrder (ofFixedModel k V) (convexComb t φ ψ) χ) :
    convexComb t (sourceIEnvelope α φ) (sourceIEnvelope α ψ) ≤ sourceIEnvelope α χ := by
  have hu := isThetaPSH_sourceIEnvelope hφ
  have hv := isThetaPSH_sourceIEnvelope hψ
  have hw := thetaPSH_convexComb' hu hv ht0 ht1
  have hcomb := SGPT.NAPotential.Berkovich.PiecewiseLinearData.sourceIOrder_convexComb' hu hv hφ hψ
    (sourceIEquivalent_iEnvelope hφ).2 (sourceIEquivalent_iEnvelope hψ).2 ht0 ht1
  have h0 := convexComb_nonpos' (sourceIEnvelope_le_zero α φ) (sourceIEnvelope_le_zero α ψ) ht0 ht1
  exact (le_sourceIEnvelope hw h0 (sourceIEquivalent_refl ⟨α, hw⟩)).trans
    ((sourceIOrder_iff_sourceIEnvelope_le hw hχ).mp (sourceIOrder_trans hcomb hI))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
theorem globalQPSH_of_isQPSH {u : X → EReal} (h : (ofFixedModel n X).IsQPSH u) :
    IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ', h'⟩ := h
  exact ((isThetaPSH_iff_nativeThetaPotential θ' u).mp h').quasiPshPotential

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-- The trace slices decrease in `τ`. -/
theorem traceComponentSlice_antitone
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) {τ τ' : ℝ} (hle : τ ≤ τ')
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ)
    (hτ' : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ') :
    traceComponentSlice hk omegaX omegaV hι Γ κV τ' hτ' ≤
      traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ := by
  let G := (Γ.component (sourceKahlerFormOfBackground omegaX)).val
  have hmono : ∀ x, G.potential ⟨τ', hτ'.1⟩ x ≤ G.potential ⟨τ, hτ.1⟩ x := fun x =>
    G.antitone x (show (⟨τ, hτ.1⟩ : Iio G.max) ≤ ⟨τ', hτ'.1⟩ from hle)
  have hIX : IEnvelope.IOrderOnManifold (n := n) (G.potential ⟨τ', hτ'.1⟩)
      (G.potential ⟨τ, hτ.1⟩) :=
    iOrderOnManifold_of_le_add (C := 0) (G.native_thetaPSH ⟨τ, hτ.1⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hmono x)
  have hP := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι (traceSlice_spec hk omegaX omegaV hι Γ τ' hτ')
    (traceSlice_spec hk omegaX omegaV hι Γ τ hτ) hIX
  obtain ⟨φ, hφ, hE⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV τ hτ
  obtain ⟨φ', hφ', hE'⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV τ' hτ'
  have hq := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ hτ)
  have hq' := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ' hτ')
  have hI := sourceIOrder_trans hE'.1 (sourceIOrder_trans (sourceIOrder_of_sourcePOrder hq' hq hP)
    hE.2)
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ hτ hE,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ' hτ' hE']
  exact (sourceIOrder_iff_sourceIEnvelope_le (thetaPSH_traceBackground_of_half hι κV hφ')
    (thetaPSH_traceBackground_of_half hι κV hφ)).mp hI

/-- The trace slices are concave in `τ`. -/
theorem traceComponentSlice_chord
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) {p q : ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hp : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) p)
    (hq : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) q)
    (hm : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) (t * p + (1 - t) * q)) :
    convexComb t (traceComponentSlice hk omegaX omegaV hι Γ κV p hp)
        (traceComponentSlice hk omegaX omegaV hι Γ κV q hq) ≤
      traceComponentSlice hk omegaX omegaV hι Γ κV (t * p + (1 - t) * q) hm := by
  let G := (Γ.component (sourceKahlerFormOfBackground omegaX)).val
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  let up := G.potential ⟨p, hp.1⟩
  let uq := G.potential ⟨q, hq.1⟩
  let um := G.potential ⟨t * p + (1 - t) * q, hm.1⟩
  have hqp : (ofFixedModel n X).IsQPSH up := ⟨_, G.thetaPSH ⟨p, hp.1⟩⟩
  have hqq : (ofFixedModel n X).IsQPSH uq := ⟨_, G.thetaPSH ⟨q, hq.1⟩⟩
  have hqtp := hqp.pos_smul ht0
  have hqtq := hqq.pos_smul ht1'
  have hqs := hqtp.add hqtq
  -- generic Lelong numbers
  have h0p : sourceGenericLelongNumber (n := n) ι (fun x => (t : EReal) * up x) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul ι up ht0, hp.2, mul_zero]
  have h0q : sourceGenericLelongNumber (n := n) ι (fun x => ((1 - t : ℝ) : EReal) * uq x) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul ι uq ht1', hq.2, mul_zero]
  have hM : max p q < G.max := max_lt hp.1 hq.1
  let uM := G.potential ⟨max p q, hM⟩
  have hMs : ∀ x, uM x ≤ (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x := by
    intro x
    have h1 : uM x ≤ up x := G.antitone x
      (show (⟨p, hp.1⟩ : Iio G.max) ≤ ⟨max p q, hM⟩ from le_max_left p q)
    have h2 : uM x ≤ uq x := G.antitone x
      (show (⟨q, hq.1⟩ : Iio G.max) ≤ ⟨max p q, hM⟩ from le_max_right p q)
    calc uM x = (t : EReal) * uM x + ((1 - t : ℝ) : EReal) * uM x :=
          (ereal_convex_self' ht0 ht1 _).symm
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.mpr ht0.le))
          (mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.mpr ht1'.le))
  have hMtr : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) (max p q) :=
    sliceTraceable_of_le ι Γ _ (if h : p ≤ q then by rw [max_eq_right h]; exact hq
      else by rw [max_eq_left (le_of_not_ge h)]; exact hp) le_rfl
  have h0s : sourceGenericLelongNumber (n := n) ι
      (fun x => (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x) = 0 :=
    SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder (G.native_thetaPSH ⟨max p q, hM⟩)
      (iOrderOnManifold_of_le_add (C := 0) (globalQPSH_of_isQPSH hqs).1
        (fun x => by simpa only [EReal.coe_zero, add_zero] using hMs x)) hMtr.2
  -- the three auxiliary traces
  obtain ⟨τu, hTu⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqtp) hι h0p
  obtain ⟨τv, hTv⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqtq) hι h0q
  obtain ⟨τs, hTs⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqs) hι h0s
  have hspp := traceSlice_spec hk omegaX omegaV hι Γ p hp
  have hspq := traceSlice_spec hk omegaX omegaV hι Γ q hq
  have hspm := traceSlice_spec hk omegaX omegaV hι Γ _ hm
  let ψp := traceSlice hk omegaX omegaV hι Γ p hp
  let ψq := traceSlice hk omegaX omegaV hι Γ q hq
  let ψm := traceSlice hk omegaX omegaV hι Γ _ hm
  have A := SGPT.TraceOperations.sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives hk
    omegaV omegaV hι hspp ht0 hTu
  have B := SGPT.TraceOperations.sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives hk
    omegaV omegaV hι hspq ht1' hTv
  have C := SGPT.TraceOperations.sourcePEquivalent_add_of_sourceTraceRepresentatives hk
    omegaV omegaV omegaV hι hTu hTv hTs
  have hchordX : ∀ x, (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x ≤ um x := fun x =>
    G.toSourceTestCurvePredata.convexComb_le ⟨p, hp.1⟩ ⟨q, hq.1⟩ ht0 ht1 x
  have D := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hTs hspm (iOrderOnManifold_of_le_add (C := 0)
      (G.native_thetaPSH ⟨t * p + (1 - t) * q, hm.1⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hchordX x))
  -- good representatives
  obtain ⟨φp, hφp, hEp⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV p hp
  obtain ⟨φq, hφq, hEq⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV q hq
  obtain ⟨φm, hφm, hEm⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV _ hm
  have hαp := thetaPSH_traceBackground_of_half hι κV hφp
  have hαq := thetaPSH_traceBackground_of_half hι κV hφq
  have hαm := thetaPSH_traceBackground_of_half hι κV hφm
  have qφp : (ofFixedModel k V).IsQPSH φp := ⟨_, hαp⟩
  have qφq : (ofFixedModel k V).IsQPSH φq := ⟨_, hαq⟩
  have qψp := isQPSH_of_sourceTrace hι hspp
  have qψq := isQPSH_of_sourceTrace hι hspq
  have qψm := isQPSH_of_sourceTrace hι hspm
  have qτu := isQPSH_of_sourceTrace hι hTu
  have qτv := isQPSH_of_sourceTrace hι hTv
  have qτs := isQPSH_of_sourceTrace hι hTs
  -- the `𝓘`-order chain
  have I1 : sourceIOrder (ofFixedModel k V) (convexComb t φp φq) (convexComb t ψp ψq) :=
    SGPT.PSH.GlobalOrderAddition.sourceIOrder_add omegaV (qφp.pos_smul ht0) (qφq.pos_smul ht1')
      (qψp.pos_smul ht0) (qψq.pos_smul ht1')
      (sourceIEquivalent_pos_smul qφp qψp hEp ht0).1
      (sourceIEquivalent_pos_smul qφq qψq hEq ht1').1
  have I2 : sourceIOrder (ofFixedModel k V) (convexComb t ψp ψq) (fun y => τu y + τv y) :=
    SGPT.PSH.GlobalOrderAddition.sourceIOrder_add omegaV (qψp.pos_smul ht0) (qψq.pos_smul ht1')
      qτu qτv (sourceIOrder_of_sourcePOrder (qψp.pos_smul ht0) qτu A.2)
      (sourceIOrder_of_sourcePOrder (qψq.pos_smul ht1') qτv B.2)
  have I3 : sourceIOrder (ofFixedModel k V) (fun y => τu y + τv y) τs :=
    sourceIOrder_of_sourcePOrder (qτu.add qτv) qτs C.2
  have I4 : sourceIOrder (ofFixedModel k V) τs ψm := sourceIOrder_of_sourcePOrder qτs qψm D
  have hI := sourceIOrder_trans I1 (sourceIOrder_trans I2 (sourceIOrder_trans I3
    (sourceIOrder_trans I4 hEm.2)))
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV p hp hEp,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV q hq hEq,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV _ hm hEm]
  exact convexComb_sourceIEnvelope_le_of_iOrder hαp hαq hαm ht0 ht1 hI

end Curve

/-! ### The trace `Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)` -/

section TraceMetric

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)

/-- The preliminary test-curve data of the component of `Tr_Y(Γ)` at the Kähler index `κ` of
`V`: cutoff `(Tr_Y Γ)_max` and slices `P_{ι^*θ+κ}[Tr_Y(Γ_τ)]_𝓘`. -/
def traceComponentPredata (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourceTestCurvePredata (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) where
  max := traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX)
  potential τ := traceComponentSlice hk omegaX omegaV hι Γ κV τ.1
    (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)
  thetaPSH τ := (traceComponentSlice_props hk omegaX omegaV hι hpull Γ κV τ.1
    (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)).choose
  antitone x := fun a b hab =>
    traceComponentSlice_antitone hk omegaX omegaV hι hpull Γ κV hab _ _ x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords _ _ x
    intro p q t ht0 ht1
    exact traceComponentSlice_chord hk omegaX omegaV hι hpull Γ κV ht0 ht1 _ _ _
  fixedPoint τ := by
    obtain ⟨_hP, hI, hpos⟩ := traceComponentSlice_props hk omegaX omegaV hι hpull Γ κV τ.1
      (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)
    have hg := (sourceIModel_positive_iGood _ _ hI hpos).2
    rw [(sourceIGood_iff_PI_eq (sourceKahlerFormRepresentative κV) hI.1 hpos).mp hg]
    exact hI.2.symm

/-- The component of `Tr_Y(Γ)` at `κ`, as an actual test curve (its limit has positive mass
since it dominates a slice of positive mass). -/
def traceComponentCurve (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourceTestCurve (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) where
  toSourceTestCurvePredata := traceComponentPredata hk omegaX omegaV hι hpull Γ hwd κV
  positiveLimitMass := by
    let D := traceComponentPredata hk omegaX omegaV hι hpull Γ hwd κV
    let p : Iio D.max := ⟨D.max - 1, by change D.max - 1 < D.max; linarith⟩
    obtain ⟨_hP, _hI, hpos⟩ := traceComponentSlice_props hk omegaX omegaV hι hpull Γ κV p.1
      (sliceTraceable_of_lt_traceCutoff hwd _ p.2)
    refine hpos.trans_le (sourcePotentialNonPluripolarMass_mono
      (sourceKahlerFormRepresentative κV) _ _
      ((SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun y => ?_⟩))
    rw [EReal.coe_zero, add_zero]
    exact (le_iSup (fun j => D.potential j y) p).trans
      (le_uscRegularization (fun z => ⨆ j, D.potential j z) y)

theorem traceComponentCurve_mem (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    traceComponentCurve hk omegaX omegaV hι hpull Γ hwd κV ∈
      SourceIModelTestCurvesPositive
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) :=
  (sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κV) _).mpr
    fun τ => (sourceIModel_iff_native _ _).mp (traceComponentSlice_props hk omegaX omegaV hι hpull
      Γ κV τ.1 (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)).2.1

/-- The component of `Tr_Y(Γ)` at `κ`, a positive `𝓘`-model test curve in `ι^*θ + κ`. -/
def traceComponent (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourcePositiveIModelTestCurve
      (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) :=
  ⟨traceComponentCurve hk omegaX omegaV hι hpull Γ hwd κV,
    traceComponentCurve_mem hk omegaX omegaV hι hpull Γ hwd κV⟩

/-- Source `def:NApotential:L623` (smooth `Y`): the trace `Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)` of a
non-Archimedean metric whose trace along `Y` is well-defined. -/
def naTrace (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    SourceNAPotential (θ.nativeHolomorphicPullback hι) where
  component κV := traceComponent hk omegaX omegaV hι hpull Γ hwd κV
  compatible κ ζ h := by
    apply Subtype.ext
    apply SourceTestCurve.ext_of_max_potential
    · rw [sourceIModelTestCurveTransition_max]
      rfl
    · intro r hr hs
      have hr' : r < (traceComponent hk omegaX omegaV hι hpull Γ hwd κ).val.max := by
        rw [sourceIModelTestCurveTransition_max] at hr
        exact hr
      rw [sourceIModelTestCurveTransition_potential _ _ _ r hr' hr]
      have hτ := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hr'
      change sourceIEnvelope _ (traceComponentSlice hk omegaX omegaV hι Γ κ r hτ) =
        traceComponentSlice hk omegaX omegaV hι Γ ζ r hτ
      obtain ⟨φ, hφ, hE⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κ r hτ
      rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κ r hτ hE]
      unfold traceComponentSlice
      apply sourceIEnvelope_eq_of_equivalent
      exact sourceIEquivalent_trans
        (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope
          (thetaPSH_traceBackground_of_half hι κ hφ))) hE

/-- Source `def:NApotential:L623`, eq:tracemax: every component of `Tr_Y(Γ)` has the cutoff
`(Tr_Y Γ)_max = sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}`, for any Kähler form `ω` of `X`. -/
theorem naTrace_max (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) :
    ((naTrace hk omegaX omegaV hι hpull Γ hwd).component κV).val.max = traceCutoff ι Γ κ :=
  traceCutoff_independent ι Γ _ κ

/-- Source `def:NApotential:L623`, item 2: for `τ < (Tr_Y Γ)_max`, every Kähler form `ω̃` of `X`
and every trace operator `ψ` of `Γ^{θ+ω̃}_τ` along `Y` (with arbitrary auxiliary choices),
`Tr_Y(Γ)^{θ|_Y+κ}_τ = P_{θ|_Y+κ}[ψ]_𝓘`; in particular the choice of the trace operator and of
`ω̃` is irrelevant. -/
theorem naTrace_potential (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
    (hτ : τ < ((naTrace hk omegaX omegaV hι hpull Γ hwd).component κV).val.max)
    (hτκ : τ < (Γ.component κ).val.max) (omega' : KahlerBackground n X)
    (omegaV' : KahlerBackground k V) {ψ : V → EReal}
    (hψ : IsSourceTraceRepresentativeAlong omega' omegaV' hι
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ) :
    ((naTrace hk omegaX omegaV hι hpull Γ hwd).component κV).val.potential ⟨τ, hτ⟩ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ := by
  have hτ0 := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hτ
  change traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ0 = _
  have hspec := traceSlice_spec hk omegaX omegaV hι Γ τ hτ0
  have hI := component_potential_iEquivalent Γ κ (sourceKahlerFormOfBackground omegaX) τ hτκ hτ0.1
  have h1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV'
    omegaV hι hψ hspec ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1)
  have h2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV' hι hspec hψ ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2)
  have hq1 := isQPSH_of_sourceTrace hι hψ
  have hq2 := isQPSH_of_sourceTrace hι hspec
  exact sourceIEnvelope_eq_of_equivalent
    ⟨sourceIOrder_of_sourcePOrder hq2 hq1 h2, sourceIOrder_of_sourcePOrder hq1 hq2 h1⟩

/-- Source `def:NApotential:L623`, item 2 with the normalized trace of `def:traceop2`: whenever
`Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)` is defined,
`Tr_Y(Γ)^{θ|_Y+κ}_τ = P_{θ|_Y+κ}[Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)]_𝓘`. -/
theorem naTrace_potential_traceEnvelope (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
    (hτ : τ < ((naTrace hk omegaX omegaV hι hpull Γ hwd).component κV).val.max)
    (hτκ : τ < (Γ.component κ).val.max) (omega' : KahlerBackground n X)
    (omegaV' : KahlerBackground k V)
    (hdef : SGPT.Trace.HasPositiveSourceTraceAlong omega' omegaV' hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩)) :
    ((naTrace hk omegaX omegaV hι hpull Γ hwd).component κV).val.potential ⟨τ, hτ⟩ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (SGPT.Trace.sourceTraceEnvelope omega' omegaV' hι
          (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) hdef) := by
  obtain ⟨hT, hψ, hpos⟩ := Classical.choose_spec hdef
  rw [naTrace_potential hk omegaX omegaV hι hpull Γ hwd κV κ τ hτ hτκ omega' omegaV' hT]
  have hP := SGPT.PSH.GlobalPComparison.sourcePEquivalent_singularityEnvelope omegaV'
    (ClosedRealOneOneForm.pullback hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)) hψ hpos
  have hq1 : (ofFixedModel k V).IsQPSH (Classical.choose hdef) :=
    isQPSH_of_sourceTrace hι hT
  have hq2 : (ofFixedModel k V).IsQPSH (SGPT.Trace.sourceTraceEnvelope omega' omegaV' hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩) hdef) := by
    refine ⟨nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)),
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_⟩
    rw [sourceNativeAtlasForm_roundTrip]
    exact FirstPass.singularityEnvelope_isThetaPshPotential _
      (ClosedRealOneOneForm.pullback hι _).property.1
      (ClosedRealOneOneForm.pullback hι _).property.2 hψ.1.hasSmoothLocalPotentials _ hψ
  exact sourceIEnvelope_eq_of_equivalent
    ⟨sourceIOrder_of_sourcePOrder hq1 hq2 hP.1, sourceIOrder_of_sourcePOrder hq2 hq1 hP.2⟩

/-- `Tr_Y(Γ)` is the unique element of `PSH^NA(Y, θ|_Y)` with the cutoff and slices of
`def:NApotential:L623`. -/
theorem naTrace_unique (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hι))
    (hmax : ∀ κV : SourceKahlerForm k V,
      (Δ.component κV).val.max = traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX))
    (hpot : ∀ (κV : SourceKahlerForm k V) (τ : ℝ) (hτ : τ < (Δ.component κV).val.max)
      (hτκ : τ < (Γ.component (sourceKahlerFormOfBackground omegaX)).val.max) {ψ : V → EReal},
      IsSourceTraceRepresentativeAlong omegaX omegaV hι
        ((Γ.component (sourceKahlerFormOfBackground omegaX)).val.potential ⟨τ, hτκ⟩) ψ →
      (Δ.component κV).val.potential ⟨τ, hτ⟩ =
        sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ) :
    Δ = naTrace hk omegaX omegaV hι hpull Γ hwd := by
  apply SourceNAPotential.ext
  intro κV
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact hmax κV
  · intro r hr hs
    have hτ0 := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs
    rw [hpot κV r hr hτ0.1 (traceSlice_spec hk omegaX omegaV hι Γ r hτ0)]
    rfl

end TraceMetric

/-! ### The source-facing statement -/

section Source

/-- The restriction of a Kähler form of `X` to `Y`. -/
def restrictedKahler {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (omegaX : KahlerBackground n X) : KahlerBackground k V :=
  ⟨ClosedRealOneOneForm.pullback hι omegaX.form, hpull omegaX⟩

/-- Source `def:NApotential:L623` for smooth `Y` (given by `ι`, with `Ỹ = Y`): if the trace of
`Γ ∈ PSH^NA(X, θ)` along `Y` is well-defined, there is a unique `Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)` such
that every component has the cutoff `(Tr_Y Γ)_max = sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}` and,
for `τ < (Tr_Y Γ)_max`, the slices `Tr_Y(Γ)^{θ|_Y+κ}_τ = P_{θ|_Y+κ}[ψ]_𝓘` for every Kähler form
`ω̃` of `X` and every trace operator `ψ` of `Γ^{θ+ω̃}_τ` along `Y`. -/
theorem source_naTrace (hk : k ≤ n) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    ∃! Δ : SourceNAPotential (θ.nativeHolomorphicPullback hι),
      (∀ (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X),
        (Δ.component κV).val.max = traceCutoff ι Γ κ) ∧
      ∀ (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
        (hτ : τ < (Δ.component κV).val.max) (hτκ : τ < (Γ.component κ).val.max)
        (omega' : KahlerBackground n X) (omegaV' : KahlerBackground k V) (ψ : V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' hι
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ →
        (Δ.component κV).val.potential ⟨τ, hτ⟩ =
          sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ := by
  let omegaV := restrictedKahler hι hpull omegaX
  refine ⟨naTrace hk omegaX omegaV hι hpull Γ hwd,
    ⟨fun κV κ => naTrace_max hk omegaX omegaV hι hpull Γ hwd κV κ,
      fun κV κ τ hτ hτκ omega' omegaV' ψ hψ =>
        naTrace_potential hk omegaX omegaV hι hpull Γ hwd κV κ τ hτ hτκ omega' omegaV' hψ⟩, ?_⟩
  rintro Δ ⟨hmax, hpot⟩
  exact naTrace_unique hk omegaX omegaV hι hpull Γ hwd Δ
    (fun κV => hmax κV _) (fun κV τ hτ hτκ ψ hψ => hpot κV _ τ hτ hτκ omegaX omegaV ψ hψ)

end Source

section Submanifold

open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-- Source `def:NApotential:L623` for `Y ⊆ X` a closed connected complex submanifold of
dimension `k` (with its induced complex structure; `Ỹ = Y`): if the trace of `Γ` along `Y` is
well-defined, `Tr_Y(Γ) ∈ PSH^NA(Y, θ|_Y)` exists and is unique, with the cutoff and slices of the
definition. -/
theorem source_naTrace_submanifold {W : Set X} (hW : IsClosedConnectedSubmanifold n W k)
    (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ) :
    letI : ChartedSpace (ComplexModel k) W :=
      chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI : IsComplexManifold k W :=
      isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    TraceWellDefined (Subtype.val : W → X) Γ →
    ∃! Δ : SourceNAPotential (θ.nativeHolomorphicPullback
        (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)),
      (∀ (κV : SourceKahlerForm k W) (κ : SourceKahlerForm n X),
        (Δ.component κV).val.max = traceCutoff (Subtype.val : W → X) Γ κ) ∧
      ∀ (κV : SourceKahlerForm k W) (κ : SourceKahlerForm n X) (τ : ℝ)
        (hτ : τ < (Δ.component κV).val.max) (hτκ : τ < (Γ.component κ).val.max)
        (omega' : KahlerBackground n X) (omegaV' : KahlerBackground k W) (ψ : W → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV'
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ →
        (Δ.component κV).val.potential ⟨τ, hτ⟩ =
          sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)) κV) ψ := by
  let : ChartedSpace (ComplexModel k) W :=
    chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
  have : IsComplexManifold k W :=
    isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  intro hwd
  exact source_naTrace (le_of_isClosedConnectedSubmanifold hW)
    (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
    (fun w => SubmanifoldKahlerRestriction.isKahler_pullback
      (le_of_isClosedConnectedSubmanifold hW) hW.2.2 w.form w.isKahler) omegaX Γ hwd

end Submanifold

end SGPT.NAPotential.NATrace

end
