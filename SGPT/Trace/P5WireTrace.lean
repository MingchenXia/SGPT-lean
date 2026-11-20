import SGPT.Trace.P5WireCommonResolution
import SGPT.Trace.TraceResMovingSeshadri

/-!
# Traces read on two arbitrary resolutions of `Y`

Source: `chapter_trace.tex` (`def:traceop`, `prop:traceunique`, `def:traceop2` and the trace
chapter, where the trace along a singular irreducible `Y` lives on the normalization `Ỹ`, i.e. is
read on any resolution of `Y`), and `rmk:movingSes` (same chapter): the trace volume
`vol Tr_V^{θ|_V} T` of the moving Seshadri constant.

The trace chapter compared the readings of the trace on two resolution targets only when one
dominates the other (`Trace2Resolution.trace_comp_of_dominates`,
`TraceRes.resolutionTraceVolume_dominates`). With a resolution target dominating two given ones
(`P5Wire.exists_common_resolutionTarget`, TN goal P5) the comparison holds for two **arbitrary**
resolution targets:

* `trace_comparison`: trace operators of `φ` read on `Y'₁` and on `Y'₂` pull back to trace
  operators on a common dominating resolution target `Y'₃`, and these pullbacks are
  `P`-equivalent (the trace is well defined up to `P`-equivalence, `prop:traceunique`,
  independently of the resolution);
* `hasPositiveSourceTraceAlong_resolution_iff`: whether `Tr^θ_Y(φ)` is defined
  (`def:traceop2`) does not depend on the resolution target;
* `resolutionTraceVolume_independent`: the volume `∫ (θ|_{Y'} + dd^c Tr^θ_Y φ)^{dim Y}` of the
  normalized trace does not depend on the resolution target;
* `movingSeshadri_independent`: the moving Seshadri constant `ε(T, x)` of `rmk:movingSes` does not
  depend on the resolution targets used to read the trace volumes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.P5Wire

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
open SGPT.Trace.Trace2Resolution SGPT.Trace.TraceRes
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- **Traces read on two arbitrary resolutions of `Y`.** Let `τ₁`, `τ₂` be trace operators of
`φ` along `Y` read on two resolution targets `Y'₁`, `Y'₂` (arbitrary auxiliary choices). There is
a resolution target `Y'₃` dominating both (`p_i : Y'₃ → Y'_i` modifications, `ι₃ = ι₁ ∘ p₁ =
ι₂ ∘ p₂`) on which `τ₁ ∘ p₁` and `τ₂ ∘ p₂` are trace operators of `φ` along `Y`, and
`τ₁ ∘ p₁ ∼_P τ₂ ∘ p₂`. -/
theorem trace_comparison [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (R₁ R₂ : ResolutionTarget Y) (omega₁ omega₂ : KahlerBackground n X)
    {omegaV₁ : KahlerBackground Y.dim R₁.V} {omegaV₂ : KahlerBackground Y.dim R₂.V}
    {u : X → EReal} {τ₁ : R₁.V → EReal} {τ₂ : R₂.V → EReal}
    (h₁ : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ R₁.contMDiff u τ₁)
    (h₂ : IsSourceTraceRepresentativeAlong omega₂ omegaV₂ R₂.contMDiff u τ₂) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V),
      IsAnalyticModification (n := Y.dim) p₁ ∧ IsAnalyticModification (n := Y.dim) p₂ ∧
      (∀ w, R₃.ι w = R₁.ι (p₁ w)) ∧ (∀ w, R₃.ι w = R₂.ι (p₂ w)) ∧
      (∃ κ : KahlerBackground n X,
        IsSourceTraceRepresentativeAlong κ R₃.kahler R₃.contMDiff u (τ₁ ∘ p₁)) ∧
      (∃ κ : KahlerBackground n X,
        IsSourceTraceRepresentativeAlong κ R₃.kahler R₃.contMDiff u (τ₂ ∘ p₂)) ∧
      SourcePEquivalent (n := Y.dim) (τ₁ ∘ p₁) (τ₂ ∘ p₂) := by
  obtain ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂⟩ := exists_common_resolutionTarget R₁ R₂
  have d₁ := trace_comp_of_dominates R₁ R₃ hp₁ hc₁ omega₁ h₁
  have d₂ := trace_comp_of_dominates R₂ R₃ hp₂ hc₂ omega₂ h₂
  obtain ⟨κ₂, hκ₂⟩ := d₂.1
  exact ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂, d₁.1, d₂.1, d₁.2 κ₂ R₃.kahler (τ₂ ∘ p₂) hκ₂⟩

section Volume

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- **The trace volume does not depend on the resolution** (`rmk:movingSes`; `def:traceop2`): for
`φ ∈ PSH(X, θ)` and two arbitrary resolution targets of `Y`, the volumes
`∫ (θ|_{Y'} + dd^c Tr^θ_Y φ)^{dim Y}` (`0` when `Tr^θ_Y φ` is undefined) agree. -/
theorem resolutionTraceVolume_independent (omega₀ : KahlerBackground n X)
    (R₁ R₂ : ResolutionTarget Y) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    resolutionTraceVolume omega₀ R₁ θ φ = resolutionTraceVolume omega₀ R₂ θ φ := by
  obtain ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂⟩ := exists_common_resolutionTarget R₁ R₂
  rw [← resolutionTraceVolume_dominates omega₀ R₁ R₃ hp₁ hc₁ θ hφ,
    resolutionTraceVolume_dominates omega₀ R₂ R₃ hp₂ hc₂ θ hφ]

/-- **The domain of `Tr^θ_Y` does not depend on the resolution** (`def:traceop2`): for
`φ ∈ PSH(X, θ)`, `Tr^θ_Y(φ)` is defined on one resolution target of `Y` iff on any other. -/
theorem hasPositiveSourceTraceAlong_resolution_iff (omega₀ : KahlerBackground n X)
    (R₁ R₂ : ResolutionTarget Y) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    HasPositiveSourceTraceAlong omega₀ R₁.kahler R₁.contMDiff θ φ ↔
      HasPositiveSourceTraceAlong omega₀ R₂.kahler R₂.contMDiff θ φ := by
  rw [hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos Y.dim_le,
    hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos Y.dim_le]
  have h := resolutionTraceVolume_independent omega₀ R₁ R₂ θ hφ
  unfold resolutionTraceVolume at h
  rw [h]

/-- **The moving Seshadri constant does not depend on the resolutions** (`rmk:movingSes`): for
`T = θ + dd^c φ` with `φ ∈ PSH(X, θ)`, `ε(T, x)` computed with two arbitrary families of
resolution targets agree. -/
theorem movingSeshadri_independent (omega₀ : KahlerBackground n X)
    (R R' : ∀ W : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget W)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (x : X) :
    movingSeshadri omega₀ R θ φ x = movingSeshadri omega₀ R' θ φ x := by
  unfold movingSeshadri
  refine iInf_congr fun W => ?_
  rw [resolutionTraceVolume_independent omega₀ (R W) (R' W) θ hφ]

end Volume

end SGPT.Trace.P5Wire
