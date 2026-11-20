import SGPT.NAPotential.TraceResNATrace
import SGPT.NAPotential.RIsoBTraceModification

/-! # The non-Archimedean trace read on two resolutions, one dominating the other

Source `def:NApotential:L623` (`chapter_NApotential.tex`), closing sentence: *when `Ỹ` is not
smooth, we understand `PSH^NA(Ỹ, θ|_Ỹ)` as the set of non-Archimedean metrics on a resolution of
`Ỹ`, which is independent of the choice of the resolution*.

For two resolution targets `R₁ = (Y'₁, ι₁)`, `R₂ = (Y'₂, ι₂)` of the irreducible analytic subset
`Y` and a modification `p : Y'₂ → Y'₁` with `ι₂ = ι₁ ∘ p`, the trace `Tr_Y(Γ)` read on `Y'₂` is the
pullback `p^* Tr_Y(Γ)` (`cor:PSHNAbimero`, `WholeClosureNA.sourceNAPullback`) of the trace read on
`Y'₁`, the two forms `p^*ι₁^*θ` and `ι₂^*θ` being identified by the canonical bijection of
`rmk:NApotential:L47` (`naTraceResolution_dominates`). This is the non-Archimedean counterpart of
`SGPT.Trace.Trace2Resolution.trace_comp_of_dominates`. Comparing two arbitrary resolutions needs
a resolution dominating both (the `P5` common resolution of the unibranch appendix, not wired to
`ResolutionTarget` here).

We also record that `naTraceResolution` does not depend on the auxiliary Kähler form of `X` used
in its construction (`naTraceResolution_eq_of_omega`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.TraceRes

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.NAPotential.NATrace SGPT.NAPotential.RIsoB
open SGPT.Trace.Trace2Resolution
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- `naTraceResolution` does not depend on the auxiliary Kähler form of `X` used to build it. -/
theorem naTraceResolution_eq_of_omega (R : ResolutionTarget Y)
    (omegaX omegaX' : KahlerBackground n X) (Γ : SourceNAPotential θ)
    (hwd : TraceWellDefined R.ι Γ) :
    naTraceResolution R omegaX Γ hwd = naTraceResolution R omegaX' Γ hwd :=
  (source_naTrace_resolution R omegaX Γ hwd).unique (naTraceResolution_spec R omegaX Γ hwd)
    (naTraceResolution_spec R omegaX' Γ hwd)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The forms `p^*ι₁^*θ` and `ι₂^*θ` on `Y'₂` are cohomologous (geometrically equal) when
`ι₂ = ι₁ ∘ p`. -/
theorem resolution_comm_class_eq (R₁ R₂ : ResolutionTarget Y) {p : R₂.V → R₁.V}
    (hp : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) ∞ p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative
        ((θ.nativeHolomorphicPullback R₁.contMDiff).nativeHolomorphicPullback hp)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative
        (θ.nativeHolomorphicPullback R₂.contMDiff)) := by
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback, sourceNativeAtlasForm_roundTrip]
  apply RealBottChern.ofRepresentative_eq_of_geometricallyEq
  have h₁ := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' R₁.contMDiff hp
    (atlasClosedFormToNative θ).val
  have hf : R₁.ι ∘ p = R₂.ι := funext fun w => (hcomm w).symm
  have h₃ : ∀ (f g : R₂.V → X), f = g →
      ∀ (hf' : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ f)
        (hg' : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ g),
      (SmoothRealForm.pullback hf' (atlasClosedFormToNative θ).val).GeometricallyEq
        (SmoothRealForm.pullback hg' (atlasClosedFormToNative θ).val) := by
    rintro f g rfl hf' hg'
    exact SmoothRealForm.GeometricallyEq.refl _
  exact h₁.symm.trans (h₃ _ _ hf _ R₂.contMDiff)

/-- The trace of `Γ` along `Y` is well-defined on one resolution target iff on another. -/
theorem traceWellDefined_resolution_transfer (R₁ R₂ : ResolutionTarget Y)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R₁.ι Γ) : TraceWellDefined R₂.ι Γ := by
  intro κ
  obtain ⟨τ₀, h⟩ := hwd κ
  exact ⟨τ₀, fun τ hτ => (sliceTraceable_resolution_iff R₂ Γ κ τ).mpr
    ((sliceTraceable_resolution_iff R₁ Γ κ τ).mp (h τ hτ))⟩

/-- **The trace read on a dominating resolution** (source `def:NApotential:L623`, independence of
the resolution, for two resolutions one of which dominates the other): if `p : Y'₂ → Y'₁` is a
modification between two resolution targets of `Y` with `ι₂ = ι₁ ∘ p`, then
`p^* Tr_Y(Γ)|_{Y'₁} = Tr_Y(Γ)|_{Y'₂}`, the left side being read over `ι₂^*θ` through the canonical
bijection of `rmk:NApotential:L47` (`p^*ι₁^*θ` and `ι₂^*θ` are geometrically equal). -/
theorem naTraceResolution_dominates (R₁ R₂ : ResolutionTarget Y) {p : R₂.V → R₁.V}
    (hp : IsAnalyticModification (n := Y.dim) p) (hcomm : ∀ w, R₂.ι w = R₁.ι (p w))
    (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R₁.ι Γ) :
    (sourceNAPullback R₁.kahler hp (naTraceResolution R₁ omegaX Γ hwd)).changeRepresentative
        (resolution_comm_class_eq R₁ R₂ hp.1 hcomm θ) =
      naTraceResolution R₂ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd) := by
  set TZ := naTraceResolution R₁ omegaX Γ hwd with hTZ
  have hwdW := traceWellDefined_resolution_transfer R₁ R₂ Γ hwd
  set A := sourceNAPullback R₁.kahler hp TZ with hA
  set hcl := resolution_comm_class_eq R₁ R₂ hp.1 hcomm θ
  have hvol₁ := SGPT.Trace.RIsoB.pullbackKahlerVolumePos R₁
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · change (A.component κ).val.max = traceCutoff R₂.ι Γ (sourceKahlerFormOfBackground omegaX)
    rw [pullback_component_max R₁.kahler hp TZ κ (sourceKahlerFormOfBackground R₁.kahler)]
    exact (traceCutoff_resolution_independent R₁ R₂ Γ _).2
  · intro r hr hs
    have hτW := sliceTraceable_of_lt_traceCutoff hwdW (sourceKahlerFormOfBackground omegaX)
      (show r < traceCutoff R₂.ι Γ (sourceKahlerFormOfBackground omegaX) from hs)
    have hτZ : SliceTraceable R₁.ι Γ (sourceKahlerFormOfBackground omegaX) r :=
      (sliceTraceable_resolution_iff R₁ Γ _ r).mpr ((sliceTraceable_resolution_iff R₂ Γ _ r).mp hτW)
    -- the left-hand side slice is `𝓘`-model
    have hL := component_slice_sourceIModel (A.changeRepresentative hcl) κ r hr
    -- traces of the slice along the two resolutions
    have hspecW := traceSlice_spec Y.dim_le omegaX R₂.kahler R₂.contMDiff Γ r hτW
    have hspecZ := traceSlice_spec Y.dim_le omegaX R₁.kahler R₁.contMDiff Γ r hτZ
    obtain ⟨-, ⟨κ', hρ⟩, hP⟩ := SGPT.Trace.sourceTrace_modification_of_commuting Y.dim_le
      (π := (id : X → X)) HironakaChowLemma.isAnalyticModification_id hp omegaX omegaX R₁.kahler
      R₂.kahler R₁.contMDiff R₂.contMDiff (fun w => hcomm w) hspecZ
    have hPW := hP omegaX R₂.kahler _ hspecW
    have hqW := isQPSH_of_sourceTrace R₂.contMDiff hspecW
    have hqρ := isQPSH_of_sourceTrace R₂.contMDiff hρ
    have hWZ : sourceIEquivalent (ofFixedModel Y.dim R₂.V)
        (traceSlice Y.dim_le omegaX R₂.kahler R₂.contMDiff Γ r hτW)
        (traceSlice Y.dim_le omegaX R₁.kahler R₁.contMDiff Γ r hτZ ∘ p) :=
      ⟨sourceIOrder_of_sourcePOrder hqW hqρ hPW.2, sourceIOrder_of_sourcePOrder hqρ hqW hPW.1⟩
    -- the slice of `Tr_Y(Γ)|_{Y'₁}` is `𝓘`-equivalent to the chosen trace
    have hrZ : r < (TZ.component (sourceKahlerFormOfBackground R₁.kahler)).val.max := by
      have h0 : r < (A.component κ).val.max := hr
      exact h0.trans_eq (pullback_component_max R₁.kahler hp TZ κ _)
    obtain ⟨φ, hφ, hφE⟩ := exists_goodTraceSlice' Y.dim_le omegaX R₁.kahler R₁.contMDiff hvol₁ Γ
      (sourceKahlerFormOfBackground R₁.kahler) r hτZ
    have hTZslice : (TZ.component (sourceKahlerFormOfBackground R₁.kahler)).val.potential
        ⟨r, hrZ⟩ = sourceIEnvelope (sourceNAComponentBackground
          (θ.nativeHolomorphicPullback R₁.contMDiff) (sourceKahlerFormOfBackground R₁.kahler))
          φ := by
      change traceComponentSlice Y.dim_le omegaX R₁.kahler R₁.contMDiff Γ _ r _ = _
      exact traceComponentSlice_eq Y.dim_le omegaX R₁.kahler R₁.contMDiff Γ _ r _ hφE
    have hZ : sourceIEquivalent (ofFixedModel Y.dim R₁.V)
        (traceSlice Y.dim_le omegaX R₁.kahler R₁.contMDiff Γ r hτZ)
        ((TZ.component (sourceKahlerFormOfBackground R₁.kahler)).val.potential ⟨r, hrZ⟩) := by
      rw [hTZslice]
      exact sourceIEquivalent_trans (sourceIEquivalent_symm hφE)
        (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half R₁.contMDiff _ hφ))
    have hZpt := (SGPT.PSH.ModificationOrders.sourceIEquivalent_modification_pullback_iff hp
      hZ.1.1 hZ.1.2.1).mp hZ
    -- the slice of `p^* Tr_Y(Γ)|_{Y'₁}`
    have hA0 : r < (A.component κ).val.max := hr
    have hAZ := pullback_slice_iEquivalent R₁.kahler hp TZ κ R₁.kahler r hA0 hrZ
    have hAA := changeRepresentative_slice_iEquivalent hcl A κ r hA0 hr
    have hchain : sourceIEquivalent (ofFixedModel Y.dim R₂.V)
        (traceSlice Y.dim_le omegaX R₂.kahler R₂.contMDiff Γ r hτW)
        (((A.changeRepresentative hcl).component κ).val.potential ⟨r, hr⟩) :=
      sourceIEquivalent_trans hWZ (sourceIEquivalent_trans hZpt
        (sourceIEquivalent_trans (sourceIEquivalent_symm hAZ) hAA))
    change _ = traceComponentSlice Y.dim_le omegaX R₂.kahler R₂.contMDiff Γ κ r hτW
    unfold traceComponentSlice
    rw [sourceIEnvelope_eq_of_equivalent hchain]
    exact hL.2

end SGPT.NAPotential.TraceRes

end
