import SGPT.NAPotential.RIsoBTraceRepresentative
import SGPT.NAPotential.BimeroModification
import SGPT.NAPotential.BimeroRepresentative
import SGPT.Trace.ModificationTrace
import SGPT.PSH.SourceModificationEquivalence
import SGPT.Okounkov.TranscendentalVolIdLinear
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison

/-! # The non-Archimedean trace and modification pullback (smooth `Z`, `W`)

Source `prop:NApotential:L655` (`chapter_NApotential.tex`), the case of the trace operator (the
case proved in the book): let `π : Y → X` be a proper bimeromorphic morphism of compact Kähler
manifolds, `Z ⊆ X` an analytic subset such that `Γ ∈ PSH^NA(X, θ)` has non-trivial restriction to
`Z`, `W` the strict transform of `Z`, `Π : W → Z` the restriction of `π` and `Π̃ : W̃ → Z̃` its
strict transform. Then `Π̃^* Tr_Z(Γ) = Tr_W(π^*Γ)`.

Here `Z` and `W` are smooth (`Z̃ = Z`, `W̃ = W`, `Π̃ = Π`), given as in `NATraceSmooth` by
holomorphic maps `ι_Z : V_Z → X`, `ι_W : V_W → Y` from compact connected complex manifolds of
dimension `k` pulling Kähler forms back to Kähler forms (e.g. inclusions of closed connected
submanifolds), and `Π̃ : V_W → V_Z` is a modification with `π ∘ ι_W = ι_Z ∘ Π̃`. The NA pullbacks
are `WholeClosureNA.sourceNAPullback` (`cor:PSHNAbimero`) along `π` and along `Π̃`.

The two sides live over the forms `Π̃^*(ι_Z^*θ)` and `ι_W^*(π^*θ)`, which are equal as forms
(both are the pullback of `θ` along `π ∘ ι_W = ι_Z ∘ Π̃`); in the formalization they are equal up
to the chart presentation (geometric equality), so the identification is the canonical bijection
of `rmk:NApotential:L47`.

## Main results

* `sourceGenericLelongNumber_eq_zero_of_comp`: `ν(π^*φ, W) = 0` implies `ν(φ, Z) = 0` (Lelong
  numbers do not decrease under pullback); the converse is `lma:rescommpullback`'s first step
  (`SGPT.Trace.sourceGenericLelongNumber_comp_modification_eq_zero`).
* `traceWellDefined_pullback_iff`, `traceCutoff_pullback`: the trace of `π^*Γ` along `W` is
  well-defined iff that of `Γ` along `Z` is, with the same cutoff (the first display of the
  book's proof).
* `naTrace_pullback`: `Π̃^* Tr_Z(Γ) = Tr_W(π^*Γ)`; `naTrace_pullback_POrder_equivalent`: the two
  sides are mutually `≤` in the order `def:NApotential:L274` (equality of intrinsic type).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.RIsoB

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.NAPotential.NATrace
open scoped Manifold ContDiff

universe u

variable {n k : ℕ} {X Y VZ VW : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  [TopologicalSpace VZ] [ChartedSpace (ComplexModel k) VZ] [IsComplexManifold k VZ]
  [MeasurableSpace VZ] [BorelSpace VZ] [CompactSpace VZ] [ConnectedSpace VZ]
  [TopologicalSpace VW] [ChartedSpace (ComplexModel k) VW] [IsComplexManifold k VW]
  [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] [ConnectedSpace VW]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-! ### Generic Lelong numbers -/

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace Y]
  [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace (ComplexModel k) VZ]
  [IsComplexManifold k VZ] [MeasurableSpace VZ] [BorelSpace VZ] [CompactSpace VZ]
  [TopologicalSpace VW] [ChartedSpace (ComplexModel k) VW] [IsComplexManifold k VW]
  [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] [ConnectedSpace VW] in
/-- If `π ∘ ι_W = ι_Z ∘ Π̃` then `ν(π^*φ, W) = 0` implies `ν(φ, Z) = 0`, because Lelong numbers do
not decrease under holomorphic pullback. -/
theorem sourceGenericLelongNumber_eq_zero_of_comp {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {pt : VW → VZ} {ιZ : VZ → X} {ιW : VW → Y} (hcomm : ∀ w, π (ιW w) = ιZ (pt w))
    {β : SmoothRealForm n X 2} {u : X → EReal} (hu : IsThetaPshPotential β u)
    (h : sourceGenericLelongNumber (n := n) ιW (u ∘ π) = 0) :
    sourceGenericLelongNumber (n := n) ιZ u = 0 := by
  by_cases hn : n = 0
  · subst hn
    exact sourceGenericLelongNumber_zero_dimension rfl ιZ u
  apply (nativeGeneric_zero_iff_source hn ιZ u).mp
  have h' := (nativeGeneric_zero_iff_source hn ιW (u ∘ π)).mpr h
  refine le_antisymm ?_ bot_le
  rw [← h']
  refine le_iInf fun w => ?_
  calc (⨅ v, lelongNumber (n := n) u (ιZ v)) ≤ lelongNumber (n := n) u (ιZ (pt w)) :=
        iInf_le _ _
    _ = lelongNumber (n := n) u (π (ιW w)) := by rw [hcomm]
    _ ≤ lelongNumber (n := n) (fun z => u (π z)) (ιW w) :=
      LelongNumberComparison.lelongNumber_le_comp (hπ.mdifferentiableAt (by simp))
        fun hpos => eq_bot_of_lelongNumber_pos (Nat.pos_of_ne_zero hn) hu.1 hpos
    _ = lelongNumber (n := n) (u ∘ π) (ιW w) := rfl

/-! ### Slices of the NA pullback -/

/-- The components of `π^*Γ` have the cutoff of `Γ`. -/
theorem pullback_component_max (omegaX : KahlerBackground n X) {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n Y) (κX : SourceKahlerForm n X) :
    ((sourceNAPullback omegaX hπ Γ).component κ).val.max = (Γ.component κX).val.max := by
  rw [← sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative κ),
    sourceNAPotentialCutoff_pullback omegaX (sourceKahlerFormRepresentative κ) hπ Γ,
    sourceNAPotentialCutoff_eq_component]

/-- A slice of `π^*Γ` is `𝓘`-equivalent to the pullback `Γ^{θ+ω}_τ ∘ π` of the corresponding slice
of `Γ`, for every Kähler form `ω` of `X`. -/
theorem pullback_slice_iEquivalent (omegaX : KahlerBackground n X) {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n Y) (w0 : KahlerBackground n X) (τ : ℝ)
    (h : τ < ((sourceNAPullback omegaX hπ Γ).component κ).val.max)
    (h' : τ < (Γ.component (sourceKahlerFormOfBackground w0)).val.max) :
    sourceIEquivalent (ofFixedModel n Y)
      (((sourceNAPullback omegaX hπ Γ).component κ).val.potential ⟨τ, h⟩)
      ((Γ.component (sourceKahlerFormOfBackground w0)).val.potential ⟨τ, h'⟩ ∘ π) := by
  obtain ⟨h1, h2⟩ := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Γ κ w0
  have hr : τ < (Γ.realizedComponent w0).val.max := by
    rw [Γ.realizedComponent_max]
    exact h'
  have e : ((Γ.realizedComponent w0).val.modificationPullback hπ).potential ⟨τ, hr⟩ =
      (Γ.component (sourceKahlerFormOfBackground w0)).val.potential ⟨τ, h'⟩ ∘ π := by
    change (Γ.realizedComponent w0).val.potential ⟨τ, hr⟩ ∘ π = _
    rw [Γ.realizedComponent_potential w0 τ h' hr]
  have hq : (ofFixedModel n Y).IsQPSH
      (((sourceNAPullback omegaX hπ Γ).component κ).val.potential ⟨τ, h⟩) :=
    ⟨_, ((sourceNAPullback omegaX hπ Γ).component κ).val.thetaPSH ⟨τ, h⟩⟩
  have hq' : (ofFixedModel n Y).IsQPSH
      ((Γ.component (sourceKahlerFormOfBackground w0)).val.potential ⟨τ, h'⟩ ∘ π) :=
    ⟨_, ((Γ.component (sourceKahlerFormOfBackground w0)).val.thetaPSH
      ⟨τ, h'⟩).comp_native_analyticModification hπ⟩
  have s1 := h1.slice_le τ h
  have s2 := h2.slice_le τ hr
  change SGPT.PSH.GlobalPComparison.sourcePOrder (n := n) _
    (((Γ.realizedComponent w0).val.modificationPullback hπ).potential ⟨τ, hr⟩) at s1
  rw [e] at s1 s2
  exact ⟨sourceIOrder_of_sourcePOrder hq hq' s1, sourceIOrder_of_sourcePOrder hq' hq s2⟩

/-! ### Well-definedness and cutoff -/

omit [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] in
/-- The generic Lelong condition for `π^*Γ` along `W` is that of `Γ` along `Z`. -/
theorem sliceTraceable_pullback_iff (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ) {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    {ιW : VW → Y} (hcomm : ∀ w, π (ιW w) = ιZ (pt w))
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n Y) (κX : SourceKahlerForm n X) (τ : ℝ) :
    SliceTraceable ιW (sourceNAPullback omegaX hπ Γ) κ τ ↔ SliceTraceable ιZ Γ κX τ := by
  rw [show SliceTraceable ιZ Γ κX τ ↔ SliceTraceable ιZ Γ (sourceKahlerFormOfBackground omegaX) τ
    from ⟨sliceTraceable_index ιZ Γ, sliceTraceable_index ιZ Γ⟩]
  have hmax := pullback_component_max omegaX hπ Γ κ (sourceKahlerFormOfBackground omegaX)
  constructor
  · rintro ⟨h, h0⟩
    have h' : τ < (Γ.component (sourceKahlerFormOfBackground omegaX)).val.max := hmax ▸ h
    have he := pullback_slice_iEquivalent omegaX hπ Γ κ omegaX τ h h'
    have h1 := SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
      (((sourceNAPullback omegaX hπ Γ).component κ).val.native_thetaPSH ⟨τ, h⟩)
      ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1) h0
    exact ⟨h', sourceGenericLelongNumber_eq_zero_of_comp hπ.1 hcomm
      ((Γ.component (sourceKahlerFormOfBackground omegaX)).val.native_thetaPSH ⟨τ, h'⟩) h1⟩
  · rintro ⟨h', h0⟩
    have h : τ < ((sourceNAPullback omegaX hπ Γ).component κ).val.max := hmax ▸ h'
    have he := pullback_slice_iEquivalent omegaX hπ Γ κ omegaX τ h h'
    obtain ⟨ψ, hψ⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
      omegaVZ
      (slice_globalQPSH (Γ.component (sourceKahlerFormOfBackground omegaX)).val ⟨τ, h'⟩) hιZ h0
    have h1 := SGPT.Trace.sourceGenericLelongNumber_comp_modification_eq_zero hπ
      (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hpt) omegaX omegaY
      omegaVZ hcomm hψ
    have hpsh := (isThetaPSH_iff_nativeThetaPotential _ _).mp
      (((Γ.component (sourceKahlerFormOfBackground omegaX)).val.thetaPSH
        ⟨τ, h'⟩).comp_native_analyticModification hπ)
    exact ⟨h, SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder hpsh
      ((sourceIOrder_iff_native he.2.1 he.2.2.1).mp he.2) h1⟩

omit [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] in
/-- The trace of `π^*Γ` along `W` is well-defined iff the trace of `Γ` along `Z` is. -/
theorem traceWellDefined_pullback_iff (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ) {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    {ιW : VW → Y} (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (Γ : SourceNAPotential θ) :
    TraceWellDefined ιW (sourceNAPullback omegaX hπ Γ) ↔ TraceWellDefined ιZ Γ := by
  constructor
  · intro h κX
    obtain ⟨τ₀, h0⟩ := h (sourceKahlerFormOfBackground omegaY)
    exact ⟨τ₀, fun τ hτ => (sliceTraceable_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm
      Γ _ κX τ).mp (h0 τ hτ)⟩
  · intro h κ
    obtain ⟨τ₀, h0⟩ := h (sourceKahlerFormOfBackground omegaX)
    exact ⟨τ₀, fun τ hτ => (sliceTraceable_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm
      Γ κ _ τ).mpr (h0 τ hτ)⟩

omit [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW] in
/-- First display of the proof of `prop:NApotential:L655`:
`(Tr_W(π^*Γ))_max = (Tr_Z Γ)_max`. -/
theorem traceCutoff_pullback (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ) {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    {ιW : VW → Y} (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n Y) (κX : SourceKahlerForm n X) :
    traceCutoff ιW (sourceNAPullback omegaX hπ Γ) κ = traceCutoff ιZ Γ κX := by
  unfold traceCutoff
  congr 1
  ext τ
  exact sliceTraceable_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ κ κX τ

/-! ### The two backgrounds -/

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace Y]
  [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace VZ] [BorelSpace VZ]
  [CompactSpace VZ] [ConnectedSpace VZ] [MeasurableSpace VW] [BorelSpace VW] [CompactSpace VW]
  [ConnectedSpace VW] in
/-- The forms `Π̃^*(ι_Z^*θ)` and `ι_W^*(π^*θ)` (both the pullback of `θ` along
`π ∘ ι_W = ι_Z ∘ Π̃`) are cohomologous; they are even geometrically equal. -/
theorem pullback_comm_class_eq {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {pt : VW → VZ} (hpt : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    {ιW : VW → Y} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative
        ((θ.nativeHolomorphicPullback hιZ).nativeHolomorphicPullback hpt)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative
        ((θ.nativeHolomorphicPullback hπ).nativeHolomorphicPullback hιW)) := by
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback, sourceNativeAtlasForm_roundTrip]
  apply RealBottChern.ofRepresentative_eq_of_geometricallyEq
  have h₁ := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' hιZ hpt
    (atlasClosedFormToNative θ).val
  have h₂ := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' hπ hιW
    (atlasClosedFormToNative θ).val
  have hf : ιZ ∘ pt = π ∘ ιW := funext fun w => (hcomm w).symm
  have h₃ : ∀ (f g : VW → X), f = g →
      ∀ (hf' : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
        (hg' : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g),
      (SmoothRealForm.pullback hf' (atlasClosedFormToNative θ).val).GeometricallyEq
        (SmoothRealForm.pullback hg' (atlasClosedFormToNative θ).val) := by
    rintro f g rfl hf' hg'
    exact SmoothRealForm.GeometricallyEq.refl _
  exact h₁.symm.trans ((h₃ _ _ hf _ _).trans h₂)

/-! ### The trace commutes with the pullback -/

/-- Source `prop:NApotential:L655`, the trace operator, for smooth `Z` and `W`:
`Π̃^* Tr_Z(Γ) = Tr_W(π^*Γ)`. Here `π : Y → X` is a modification, `Z`, `W` are given by
`ι_Z : V_Z → X`, `ι_W : V_W → Y` (pulling Kähler forms back to Kähler forms), `Π̃ : V_W → V_Z` is
a modification with `π ∘ ι_W = ι_Z ∘ Π̃`, and the trace of `Γ` along `Z` is well-defined (then so
is that of `π^*Γ` along `W`, `traceWellDefined_pullback_iff`). The left-hand side
`Π̃^* Tr_Z(Γ) ∈ PSH^NA(V_W, Π̃^*ι_Z^*θ)` is read in `PSH^NA(V_W, ι_W^*π^*θ)` through the canonical
bijection of `rmk:NApotential:L47` (the two forms are geometrically equal). -/
theorem naTrace_pullback (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ)
    (omegaVW : KahlerBackground k VW) {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    (hpullZ : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hιZ w.form).val.IsKahler)
    {ιW : VW → Y} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hpullW : ∀ w : KahlerBackground n Y, (ClosedRealOneOneForm.pullback hιW w.form).val.IsKahler)
    (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ιZ Γ) :
    (sourceNAPullback omegaVZ hpt (naTrace hk omegaX omegaVZ hιZ hpullZ Γ hwd)).changeRepresentative
        (pullback_comm_class_eq hπ.1 hpt.1 hιZ hιW hcomm θ) =
      naTrace hk omegaY omegaVW hιW hpullW (sourceNAPullback omegaX hπ Γ)
        ((traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd) := by
  set TZ := naTrace hk omegaX omegaVZ hιZ hpullZ Γ hwd with hTZ
  set PΓ := sourceNAPullback omegaX hπ Γ with hPΓ
  have hwdW := (traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd
  set A := sourceNAPullback omegaVZ hpt TZ with hA
  set hcl := pullback_comm_class_eq hπ.1 hpt.1 hιZ hιW hcomm θ
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · change (A.component κ).val.max =
      traceCutoff ιW PΓ (sourceKahlerFormOfBackground omegaY)
    rw [pullback_component_max omegaVZ hpt TZ κ (sourceKahlerFormOfBackground omegaVZ),
      traceCutoff_pullback hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ _
        (sourceKahlerFormOfBackground omegaX)]
    rfl
  · intro r hr hs
    have hτW := sliceTraceable_of_lt_traceCutoff hwdW (sourceKahlerFormOfBackground omegaY)
      (show r < traceCutoff ιW PΓ (sourceKahlerFormOfBackground omegaY) from hs)
    have hτZ : SliceTraceable ιZ Γ (sourceKahlerFormOfBackground omegaX) r :=
      (sliceTraceable_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ _ _ r).mp hτW
    -- the left-hand side slice is `𝓘`-model
    have hL := component_slice_sourceIModel (A.changeRepresentative hcl) κ r hr
    -- traces of the two slices
    have hspecW := traceSlice_spec hk omegaY omegaVW hιW PΓ r hτW
    have hspecZ := traceSlice_spec hk omegaX omegaVZ hιZ Γ r hτZ
    obtain ⟨-, ⟨κ', hρ⟩, -⟩ := SGPT.Trace.sourceTrace_modification_of_commuting hk hπ hpt omegaX
      omegaY omegaVZ omegaVW hιZ hιW hcomm hspecZ
    have he := pullback_slice_iEquivalent omegaX hπ Γ (sourceKahlerFormOfBackground omegaY) omegaX r
      hτW.1 hτZ.1
    have p1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaVW
      omegaVW hιW hspecW hρ ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1)
    have p2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaVW
      omegaVW hιW hρ hspecW ((sourceIOrder_iff_native he.2.1 he.2.2.1).mp he.2)
    have hqW := isQPSH_of_sourceTrace hιW hspecW
    have hqρ := isQPSH_of_sourceTrace hιW hρ
    have hWZ : sourceIEquivalent (ofFixedModel k VW) (traceSlice hk omegaY omegaVW hιW PΓ r hτW)
        (traceSlice hk omegaX omegaVZ hιZ Γ r hτZ ∘ pt) :=
      ⟨sourceIOrder_of_sourcePOrder hqW hqρ p1, sourceIOrder_of_sourcePOrder hqρ hqW p2⟩
    -- the slice of `Tr_Z(Γ)` is `𝓘`-equivalent to the chosen trace `ψ_Z`
    have hrZ : r < (TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.max := by
      have h0 : r < (A.component κ).val.max := hr
      exact h0.trans_eq (pullback_component_max omegaVZ hpt TZ κ _)
    obtain ⟨φ, hφ, hφE⟩ := exists_good_traceSlice' hk omegaX omegaVZ hιZ hpullZ Γ
      (sourceKahlerFormOfBackground omegaVZ) r hτZ
    have hTZslice : (TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.potential ⟨r, hrZ⟩ =
        sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hιZ)
          (sourceKahlerFormOfBackground omegaVZ)) φ := by
      change traceComponentSlice hk omegaX omegaVZ hιZ Γ _ r _ = _
      exact traceComponentSlice_eq hk omegaX omegaVZ hιZ Γ _ r _ hφE
    have hZ : sourceIEquivalent (ofFixedModel k VZ) (traceSlice hk omegaX omegaVZ hιZ Γ r hτZ)
        ((TZ.component (sourceKahlerFormOfBackground omegaVZ)).val.potential ⟨r, hrZ⟩) := by
      rw [hTZslice]
      exact sourceIEquivalent_trans (sourceIEquivalent_symm hφE)
        (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half hιZ _ hφ))
    have hZpt := (SGPT.PSH.ModificationOrders.sourceIEquivalent_modification_pullback_iff hpt
      hZ.1.1 hZ.1.2.1).mp hZ
    -- the slice of `Π̃^* Tr_Z(Γ)`
    have hA0 : r < (A.component κ).val.max := hr
    have hAZ := pullback_slice_iEquivalent omegaVZ hpt TZ κ omegaVZ r hA0 hrZ
    have hAA := changeRepresentative_slice_iEquivalent hcl A κ r hA0 hr
    have hchain : sourceIEquivalent (ofFixedModel k VW)
        (traceSlice hk omegaY omegaVW hιW PΓ r hτW)
        (((A.changeRepresentative hcl).component κ).val.potential ⟨r, hr⟩) :=
      sourceIEquivalent_trans hWZ (sourceIEquivalent_trans hZpt
        (sourceIEquivalent_trans (sourceIEquivalent_symm hAZ) hAA))
    change _ = traceComponentSlice hk omegaY omegaVW hιW PΓ κ r hτW
    unfold traceComponentSlice
    rw [sourceIEnvelope_eq_of_equivalent hchain]
    exact hL.2

/-- `prop:NApotential:L655` for the trace, as an equality of intrinsic type: `Π̃^* Tr_Z(Γ)` and
`Tr_W(π^*Γ)` are mutually `≤` in the order `def:NApotential:L274` (which compares
non-Archimedean metrics over different representatives). -/
theorem naTrace_pullback_POrder_equivalent (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (omegaVZ : KahlerBackground k VZ)
    (omegaVW : KahlerBackground k VW) {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {pt : VW → VZ} (hpt : IsAnalyticModification (n := k) pt)
    {ιZ : VZ → X} (hιZ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιZ)
    (hpullZ : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hιZ w.form).val.IsKahler)
    {ιW : VW → Y} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hpullW : ∀ w : KahlerBackground n Y, (ClosedRealOneOneForm.pullback hιW w.form).val.IsKahler)
    (hcomm : ∀ w, π (ιW w) = ιZ (pt w)) (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ιZ Γ) :
    SourceNAPOrder (sourceNAPullback omegaVZ hpt (naTrace hk omegaX omegaVZ hιZ hpullZ Γ hwd))
        (naTrace hk omegaY omegaVW hιW hpullW (sourceNAPullback omegaX hπ Γ)
          ((traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd)) ∧
      SourceNAPOrder (naTrace hk omegaY omegaVW hιW hpullW (sourceNAPullback omegaX hπ Γ)
          ((traceWellDefined_pullback_iff hk omegaX omegaY omegaVZ hπ hpt hιZ hcomm Γ).mpr hwd))
        (sourceNAPullback omegaVZ hpt (naTrace hk omegaX omegaVZ hιZ hpullZ Γ hwd)) := by
  rw [← naTrace_pullback hk omegaX omegaY omegaVZ omegaVW hπ hpt hιZ hpullZ hιW hpullW hcomm Γ hwd]
  have h := SourceNAPotential.changeRepresentative_POrder_equivalent omegaVW
    (pullback_comm_class_eq hπ.1 hpt.1 hιZ hιW hcomm θ)
    (sourceNAPullback omegaVZ hpt (naTrace hk omegaX omegaVZ hιZ hpullZ Γ hwd))
  exact ⟨h.1, h.2⟩

end SGPT.NAPotential.RIsoB

end
