import SGPT.NAPotential.NATraceSmooth
import SGPT.NAPotential.RepresentativeChange
import SGPT.Okounkov.TranscendentalSliceClasses

/-! # The non-Archimedean trace and the change of representative

Source `rmk:NApotential:L47` (`chapter_NApotential.tex`): for `θ'` representing `{θ}` there is a
canonical bijection `PSH^NA(X, θ) ≃ PSH^NA(X, θ')`, and *the constructions below are independent
of the choice of `θ` within its cohomology class*. This file treats the trace operator
`def:NApotential:L623` along a smooth `Y` (`Ỹ = Y`, given as in `NATraceSmooth` by a holomorphic
map `ι : V → X` from a compact connected complex manifold whose pullbacks of Kähler forms are
Kähler, e.g. the inclusion of a closed connected complex submanifold).

## Main results

* `nativeHolomorphicPullback_class_eq`: `{ι^*θ} = {ι^*θ'}` when `{θ} = {θ'}`, so the change of
  representative `PSH^NA(Y, θ|_Y) ≃ PSH^NA(Y, θ'|_Y)` is defined.
* `changeRepresentative_slice_iEquivalent`: corresponding slices of `Γ` and of its change of
  representative are `𝓘`-equivalent.
* `traceWellDefined_changeRepresentative_iff`, `traceCutoff_changeRepresentative`: the trace of
  `Γ` along `Y` is well-defined iff that of its image is, with the same `(Tr_Y Γ)_max`.
* `naTrace_changeRepresentative`: `Tr_Y` commutes with the change of representative:
  `Tr_Y(Γ') = (Tr_Y Γ)'`, where `'` is the canonical bijection of `rmk:NApotential:L47` on `X`,
  resp. on `Y`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.RIsoB

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open scoped Manifold ContDiff

universe u

section General

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
  [IsComplexManifold m M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β : AtlasClosedRealOneOneForm (ofFixedModel m M)}

/-- Corresponding slices of a non-Archimedean metric and of its change of representative
(`rmk:NApotential:L47`) are `𝓘`-equivalent. -/
theorem changeRepresentative_slice_iEquivalent
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative α) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative β))
    (Γ : SourceNAPotential α) (κ : SourceKahlerForm m M) (τ : ℝ)
    (h : τ < (Γ.component κ).val.max)
    (h' : τ < ((Γ.changeRepresentative hc).component κ).val.max) :
    sourceIEquivalent (ofFixedModel m M) ((Γ.component κ).val.potential ⟨τ, h⟩)
      (((Γ.changeRepresentative hc).component κ).val.potential ⟨τ, h'⟩) := by
  have hP := (Γ.component κ).val.changeRepresentative_POrder_equivalent
    (sourceKahlerFormRepresentative κ) (sourceNAComponentBackground_class hc κ)
  have hq : (ofFixedModel m M).IsQPSH ((Γ.component κ).val.potential ⟨τ, h⟩) :=
    ⟨_, (Γ.component κ).val.thetaPSH ⟨τ, h⟩⟩
  have hq' : (ofFixedModel m M).IsQPSH
      (((Γ.changeRepresentative hc).component κ).val.potential ⟨τ, h'⟩) :=
    ⟨_, ((Γ.changeRepresentative hc).component κ).val.thetaPSH ⟨τ, h'⟩⟩
  exact ⟨sourceIOrder_of_sourcePOrder hq hq' (hP.1.slice_le τ h),
    sourceIOrder_of_sourcePOrder hq' hq (hP.2.slice_le τ h')⟩

/-- A slice of a component of a non-Archimedean metric is `𝓘`-model. -/
theorem component_slice_sourceIModel (Γ : SourceNAPotential α) (κ : SourceKahlerForm m M)
    (τ : ℝ) (h : τ < (Γ.component κ).val.max) :
    sourceIModel (sourceNAComponentBackground α κ) ((Γ.component κ).val.potential ⟨τ, h⟩) :=
  (sourceIModel_iff_native _ _).mpr
    ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κ) _).mp
      (Γ.component κ).property ⟨τ, h⟩)

end General

variable {n k : ℕ} {X V : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n X)}

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
/-- `{θ} = {θ'}` implies `{θ|_Y} = {θ'|_Y}`: the restrictions `ι^*θ` and `ι^*θ'` are
cohomologous (`θ' = θ + dd^c g` gives `ι^*θ' = ι^*θ + dd^c (g ∘ ι)`). -/
theorem nativeHolomorphicPullback_class_eq {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ')) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative (θ.nativeHolomorphicPullback hι)) =
      RealBottChern.ofRepresentative
        (atlasClosedFormToNative (θ'.nativeHolomorphicPullback hι)) := by
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback, sourceNativeAtlasForm_roundTrip]
  exact (SGPT.Okounkov.TranscendentalSlice.ofRepresentative_pullback_congr' hι hc.symm).symm

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The generic Lelong condition `ν(Γ^{θ+ω}_τ, Y) = 0` is unchanged by the change of
representative. -/
theorem sliceTraceable_changeRepresentative_iff (ι : V → X)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X) (τ : ℝ) :
    SliceTraceable ι (Γ.changeRepresentative hc) κ τ ↔ SliceTraceable ι Γ κ τ := by
  constructor
  · rintro ⟨h', h0⟩
    have h : τ < (Γ.component κ).val.max := h'
    have he := changeRepresentative_slice_iEquivalent hc Γ κ τ h h'
    exact ⟨h, SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
      (((Γ.changeRepresentative hc).component κ).val.native_thetaPSH ⟨τ, h'⟩)
      ((sourceIOrder_iff_native he.2.1 he.2.2.1).mp he.2) h0⟩
  · rintro ⟨h, h0⟩
    have h' : τ < ((Γ.changeRepresentative hc).component κ).val.max := h
    have he := changeRepresentative_slice_iEquivalent hc Γ κ τ h h'
    exact ⟨h', SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
      ((Γ.component κ).val.native_thetaPSH ⟨τ, h⟩)
      ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1) h0⟩

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The trace of `Γ` along `Y` is well-defined iff that of its change of representative is. -/
theorem traceWellDefined_changeRepresentative_iff (ι : V → X)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) :
    TraceWellDefined ι (Γ.changeRepresentative hc) ↔ TraceWellDefined ι Γ := by
  unfold TraceWellDefined
  simp_rw [sliceTraceable_changeRepresentative_iff]

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- `(Tr_Y Γ)_max` is unchanged by the change of representative. -/
theorem traceCutoff_changeRepresentative (ι : V → X)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X) :
    traceCutoff ι (Γ.changeRepresentative hc) κ = traceCutoff ι Γ κ := by
  unfold traceCutoff
  simp_rw [sliceTraceable_changeRepresentative_iff]

/-- The chosen trace operators of corresponding slices of `Γ` and of its change of representative
are `𝓘`-equivalent on `V`. -/
theorem traceSlice_changeRepresentative_iEquivalent (hk : k ≤ n)
    (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ)
    (hτ' : SliceTraceable ι (Γ.changeRepresentative hc) (sourceKahlerFormOfBackground omegaX) τ) :
    sourceIEquivalent (ofFixedModel k V)
      (traceSlice hk omegaX omegaV hι (Γ.changeRepresentative hc) τ hτ')
      (traceSlice hk omegaX omegaV hι Γ τ hτ) := by
  have hs := traceSlice_spec hk omegaX omegaV hι Γ τ hτ
  have hs' := traceSlice_spec hk omegaX omegaV hι (Γ.changeRepresentative hc) τ hτ'
  have he := changeRepresentative_slice_iEquivalent hc Γ _ τ hτ.1 hτ'.1
  have h1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hs hs' ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1)
  have h2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hs' hs ((sourceIOrder_iff_native he.2.1 he.2.2.1).mp he.2)
  have hq1 := isQPSH_of_sourceTrace hι hs
  have hq2 := isQPSH_of_sourceTrace hι hs'
  exact ⟨sourceIOrder_of_sourcePOrder hq2 hq1 h2, sourceIOrder_of_sourcePOrder hq1 hq2 h1⟩

/-- Source `rmk:NApotential:L47` for the trace operator `def:NApotential:L623` along a smooth `Y`:
the trace commutes with the canonical bijection `PSH^NA(X, θ) ≃ PSH^NA(X, θ')` of a change of
representative, i.e. `Tr_Y(Γ') = (Tr_Y Γ)'` in `PSH^NA(Y, θ'|_Y)`, the right-hand side being the
change of representative `PSH^NA(Y, θ|_Y) ≃ PSH^NA(Y, θ'|_Y)` (`{θ|_Y} = {θ'|_Y}` by
`nativeHolomorphicPullback_class_eq`). -/
theorem naTrace_changeRepresentative (hk : k ≤ n) (omegaX : KahlerBackground n X)
    (omegaV : KahlerBackground k V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    naTrace hk omegaX omegaV hι hpull (Γ.changeRepresentative hc)
        ((traceWellDefined_changeRepresentative_iff ι hc Γ).mpr hwd) =
      (naTrace hk omegaX omegaV hι hpull Γ hwd).changeRepresentative
        (nativeHolomorphicPullback_class_eq hι hc) := by
  set Δ := naTrace hk omegaX omegaV hι hpull Γ hwd with hΔ
  have hwd' := (traceWellDefined_changeRepresentative_iff ι hc Γ).mpr hwd
  apply SourceNAPotential.ext
  intro κV
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · change traceCutoff ι (Γ.changeRepresentative hc) (sourceKahlerFormOfBackground omegaX) =
      traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX)
    exact traceCutoff_changeRepresentative ι hc Γ _
  · intro r hr hs
    have hτ' := sliceTraceable_of_lt_traceCutoff hwd' (sourceKahlerFormOfBackground omegaX) hr
    have hτ := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX)
      (show r < traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX) from hs)
    have hs0 : r < (Δ.component κV).val.max := hs
    -- the right-hand side slice is `𝓘`-model in the new background
    have hB := component_slice_sourceIModel (Δ.changeRepresentative
      (nativeHolomorphicPullback_class_eq hι hc)) κV r hs
    -- it is `𝓘`-equivalent to the old slice
    have hBD := changeRepresentative_slice_iEquivalent (nativeHolomorphicPullback_class_eq hι hc)
      Δ κV r hs0 hs
    -- the old slice is `P_{ι^*θ+κ}[ψ]_𝓘` for a good representative `φ ∼_𝓘 ψ`
    obtain ⟨φ, hφ, hφE⟩ := exists_good_traceSlice' hk omegaX omegaV hι hpull Γ κV r hτ
    have hD : (Δ.component κV).val.potential ⟨r, hs0⟩ =
        sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) φ := by
      change traceComponentSlice hk omegaX omegaV hι Γ κV r _ = _
      exact traceComponentSlice_eq hk omegaX omegaV hι Γ κV r _ hφE
    have hDφ : sourceIEquivalent (ofFixedModel k V) ((Δ.component κV).val.potential ⟨r, hs0⟩)
        φ := by
      rw [hD]
      exact sourceIEquivalent_symm
        (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half hι κV hφ))
    have hψ := traceSlice_changeRepresentative_iEquivalent hk omegaX omegaV hι hc Γ r hτ hτ'
    -- chain: ψ' ∼ ψ ∼ φ ∼ old slice ∼ new slice
    have hchain : sourceIEquivalent (ofFixedModel k V)
        (traceSlice hk omegaX omegaV hι (Γ.changeRepresentative hc) r hτ')
        (((Δ.changeRepresentative (nativeHolomorphicPullback_class_eq hι hc)).component
          κV).val.potential ⟨r, hs⟩) :=
      sourceIEquivalent_trans hψ (sourceIEquivalent_trans (sourceIEquivalent_symm hφE)
        (sourceIEquivalent_trans (sourceIEquivalent_symm hDφ) hBD))
    change traceComponentSlice hk omegaX omegaV hι (Γ.changeRepresentative hc) κV r hτ' = _
    unfold traceComponentSlice
    rw [sourceIEnvelope_eq_of_equivalent hchain]
    exact hB.2.symm

end SGPT.NAPotential.RIsoB

end
