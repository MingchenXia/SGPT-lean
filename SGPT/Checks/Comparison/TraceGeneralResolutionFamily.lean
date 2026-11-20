import SGPT.Checks.Comparison.TraceResolutionDivisorialCoherence

/-! Concrete GENERAL KAHLER original trace family on ALL actual original
ResolutionTargets. Exact printed def:NApotential:L623 resolution convention.
No rational line/metric/Chern inputs; no normalization-space construction.
Blueprint: trace-general-resolution-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.VariableComplexAtlas.WholeClosureNA
open SGPT.PSH.CompactPrimeOver SGPT.Trace.Trace2Resolution
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition AnalyticModificationLocalDiscrepancy
open SGPT.NAPotential.NATrace SGPT.NAPotential.TraceRes
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
  (Y : ClosedIrreducibleAnalyticSubvariety n X)

/-- The original BOOK carrier-wise hwd, with no resolution input. -/
def carrierTraceWellDefined (Γ : SourceNAPotential θ) : Prop :=
  ∀ κ : SourceKahlerForm n X, ∃ s₀ : ℝ, ∀ s < s₀,
    ∃ h : s < (Γ.component κ).val.max,
      (ofFixedModel n X).sourceGenericLelong ((Γ.component κ).val.potential ⟨s,h⟩) Y.carrier = 0

/-- The original BOOK cutoff on the actual carrier, not on a chosen map. -/
def carrierTraceCutoff (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X) : ℝ :=
  sSup {s | ∃ h : s < (Γ.component κ).val.max,
    (ofFixedModel n X).sourceGenericLelong ((Γ.component κ).val.potential ⟨s,h⟩) Y.carrier = 0}

/-- The actual original carrier condition yields every actual target hwd. -/
theorem carrierTraceWellDefined_on (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) (R : ResolutionTarget Y) : TraceWellDefined R.ι Γ :=
  (traceWellDefined_resolution_iff R Γ).mpr hwd

/-- The concrete family uses the SAME original NA trace construction for
EVERY actual target. Its hk/hvol/target Kahler background are INTERNAL. -/
def resolutionTraceFamily (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) (R : ResolutionTarget Y) :
    SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff) :=
  naTraceResolution R omegaX Γ (carrierTraceWellDefined_on Y Γ hwd R)

/-- The actual positive I-model component at the target's OWN internally
produced Kahler index. No κR or hvol certificate is supplied. -/
def resolutionTraceFamily_chosenComponent (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ) (R : ResolutionTarget Y) :
    SourcePositiveIModelTestCurve (sourceNAComponentBackground
      (θ.nativeHolomorphicPullback R.contMDiff) (sourceKahlerFormOfBackground R.kahler)) :=
  (resolutionTraceFamily Y omegaX Γ hwd R).component (sourceKahlerFormOfBackground R.kahler)

/-- Exact original carrier cutoff and every original trace-representative
slice formula, on a given actual resolution. -/
def ResolutionTraceSpec (Γ : SourceNAPotential θ) (R : ResolutionTarget Y)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff)) : Prop :=
  (∀ (κR : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X),
    (Δ.component κR).val.max = carrierTraceCutoff Y Γ κ) ∧
  ∀ (κR : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X) (s : ℝ)
    (hsR : s < (Δ.component κR).val.max) (hs : s < (Γ.component κ).val.max)
    (omega' : KahlerBackground n X) (omegaR' : KahlerBackground Y.dim R.V) (ψ : R.V → EReal),
    IsSourceTraceRepresentativeAlong omega' omegaR' R.contMDiff
      ((Γ.component κ).val.potential ⟨s,hs⟩) ψ →
    (Δ.component κR).val.potential ⟨s,hsR⟩ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback R.contMDiff) κR) ψ

/-- Every value of the ACTUAL concrete family has the original cutoff and
source slice formulas; all actual backgrounds/representatives quantified. -/
theorem resolutionTraceFamily_spec (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) (R : ResolutionTarget Y) :
    ResolutionTraceSpec Y Γ R (resolutionTraceFamily Y omegaX Γ hwd R) := by
  have h := naTraceResolution_spec R omegaX Γ (carrierTraceWellDefined_on Y Γ hwd R)
  exact ⟨fun κR κ => (h.1 κR κ).trans (traceCutoff_resolution_eq R Γ κ),h.2⟩

/-- UNIQUE entire original resolution-indexed family. This is an actual
produced family, not a caller-supplied trace/normalization certificate. -/
theorem existsUnique_resolutionTraceFamily (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ) :
    ∃! F : (R : ResolutionTarget Y) → SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff),
      ∀ R, ResolutionTraceSpec Y Γ R (F R) := by
  refine ⟨resolutionTraceFamily Y omegaX Γ hwd, resolutionTraceFamily_spec Y omegaX Γ hwd, ?_⟩
  intro F hF
  funext R
  have hFR := hF R
  have hFspec : (∀ (κR : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X),
      ((F R).component κR).val.max = traceCutoff R.ι Γ κ) ∧ _ :=
    ⟨fun κR κ => (hFR.1 κR κ).trans (traceCutoff_resolution_eq R Γ κ).symm,hFR.2⟩
  exact (source_naTrace_resolution R omegaX Γ (carrierTraceWellDefined_on Y Γ hwd R)).unique
    hFspec (naTraceResolution_spec R omegaX Γ (carrierTraceWellDefined_on Y Γ hwd R))

/-- Literal ORIGINAL common-pullback equality for the entire actual
family, with the common target/maps constructed internally by accepted P5. -/
theorem resolutionTraceFamily_common (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ) (R₁ R₂ : ResolutionTarget Y) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V)
      (hp₁ : IsAnalyticModification (n := Y.dim) p₁) (hp₂ : IsAnalyticModification (n := Y.dim) p₂)
      (hc₁ : ∀ w, R₃.ι w = R₁.ι (p₁ w)) (hc₂ : ∀ w, R₃.ι w = R₂.ι (p₂ w)),
      (sourceNAPullback R₁.kahler hp₁ (resolutionTraceFamily Y omegaX Γ hwd R₁)).changeRepresentative
        (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ) = resolutionTraceFamily Y omegaX Γ hwd R₃ ∧
      (sourceNAPullback R₂.kahler hp₂ (resolutionTraceFamily Y omegaX Γ hwd R₂)).changeRepresentative
        (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ) = resolutionTraceFamily Y omegaX Γ hwd R₃ := by
  exact SGPT.NAPotential.P5Wire.naTraceResolution_common R₁ R₂ omegaX Γ
    (carrierTraceWellDefined_on Y Γ hwd R₁)

/-- An ACTUAL resolving target is internally obtained from accepted
resolution existence; the indexed family is not a vacuous empty family. -/
def resolutionTraceTarget (omegaX : KahlerBackground n X) : ResolutionTarget Y :=
  Classical.choice (SGPT.Trace.Trace2Resolution.exists_resolutionTarget omegaX Y)

/-- The entire concrete family is independent of the auxiliary ambient
Kahler background, as an actual dependent FUNCTION. -/
theorem resolutionTraceFamily_independent (omegaX omegaX' : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ) :
    resolutionTraceFamily Y omegaX Γ hwd = resolutionTraceFamily Y omegaX' Γ hwd := by
  funext R
  exact naTraceResolution_eq_of_omega R omegaX omegaX' Γ (carrierTraceWellDefined_on Y Γ hwd R)

/-- Actual original divisorial function coherence for the concrete entire
family. The common target and both modifications are INTERNAL; all actual
indices/positive real weights/trivial point/dimension zero are retained. -/
theorem resolutionTraceFamily_divisorial_common (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ) (R₁ R₂ : ResolutionTarget Y) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V)
      (hp₁ : IsAnalyticModification (n := Y.dim) p₁)
      (hp₂ : IsAnalyticModification (n := Y.dim) p₂),
      (∀ w, R₃.ι w = R₁.ι (p₁ w)) ∧ (∀ w, R₃.ι w = R₂.ι (p₂ w)) ∧
      ∀ (κ₁ : SourceKahlerForm Y.dim R₁.V) (κ₂ : SourceKahlerForm Y.dim R₂.V)
        (κ₃ : SourceKahlerForm Y.dim R₃.V),
      (nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
        fun v => nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₁
          (nativeDivisorialPush hp₁ v)) ∧
      (nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
        fun v => nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₂
          (nativeDivisorialPush hp₂ v)) :=
  exists_nativeDivisorial_commonResolution R₁ R₂ omegaX Γ (carrierTraceWellDefined_on Y Γ hwd R₁)

end SGPT.NAPotential.TraceComparison
