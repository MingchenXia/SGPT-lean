import SGPT.NAPotential.TraceResDominates
import SGPT.Trace.P5WireCommonResolution

/-! # The non-Archimedean trace does not depend on the resolution

Source `def:NApotential:L623` (`chapter_NApotential.tex`), closing sentence: *when `Ỹ` is not
smooth, we understand `PSH^NA(Ỹ, θ|_Ỹ)` as the set of non-Archimedean metrics on a resolution of
`Ỹ`, which is independent of the choice of the resolution*.

`TraceRes.naTraceResolution_dominates` compares the trace `Tr_Y(Γ)` read on two resolution targets
one of which dominates the other. With a resolution target dominating two arbitrary ones
(`SGPT.Trace.P5Wire.exists_common_resolutionTarget`, TN goal P5), the readings on two **arbitrary**
resolution targets `Y'₁`, `Y'₂` are identified: their pullbacks to a common dominating resolution
target `Y'₃` both equal the trace read on `Y'₃` (`naTraceResolution_common`), each identified with
`PSH^NA(Y'₃, ι₃^*θ)` through the canonical bijection of `rmk:NApotential:L47`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.P5Wire

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.NAPotential.NATrace SGPT.NAPotential.TraceRes
open SGPT.Trace.Trace2Resolution
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- **The non-Archimedean trace read on two arbitrary resolutions** (source
`def:NApotential:L623`, independence of the resolution). For two resolution targets `Y'₁`, `Y'₂`
of `Y` there is a resolution target `Y'₃` with modifications `pᵢ : Y'₃ → Y'ᵢ`,
`ι₃ = ι₁ ∘ p₁ = ι₂ ∘ p₂`, such that `p₁^* Tr_Y(Γ)|_{Y'₁} = Tr_Y(Γ)|_{Y'₃} = p₂^* Tr_Y(Γ)|_{Y'₂}`
(pullbacks `cor:PSHNAbimero`, read over `ι₃^*θ` through the canonical bijection of
`rmk:NApotential:L47`). The well-definedness of the trace does not depend on the resolution
(`traceWellDefined_resolution_transfer`). -/
theorem naTraceResolution_common (R₁ R₂ : ResolutionTarget Y) (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R₁.ι Γ) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V)
      (hp₁ : IsAnalyticModification (n := Y.dim) p₁) (hp₂ : IsAnalyticModification (n := Y.dim) p₂)
      (hc₁ : ∀ w, R₃.ι w = R₁.ι (p₁ w)) (hc₂ : ∀ w, R₃.ι w = R₂.ι (p₂ w)),
      (sourceNAPullback R₁.kahler hp₁ (naTraceResolution R₁ omegaX Γ hwd)).changeRepresentative
          (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ) =
        naTraceResolution R₃ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₃ Γ hwd) ∧
      (sourceNAPullback R₂.kahler hp₂ (naTraceResolution R₂ omegaX Γ
          (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd))).changeRepresentative
          (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ) =
        naTraceResolution R₃ omegaX Γ (traceWellDefined_resolution_transfer R₁ R₃ Γ hwd) := by
  obtain ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂⟩ :=
    SGPT.Trace.P5Wire.exists_common_resolutionTarget R₁ R₂
  exact ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂,
    naTraceResolution_dominates R₁ R₃ hp₁ hc₁ omegaX Γ hwd,
    naTraceResolution_dominates R₂ R₃ hp₂ hc₂ omegaX Γ
      (traceWellDefined_resolution_transfer R₁ R₂ Γ hwd)⟩

end SGPT.NAPotential.P5Wire
