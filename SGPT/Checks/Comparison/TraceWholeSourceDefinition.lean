import SGPT.Checks.Comparison.TraceResolutionDivisorEquivalence

/-! Closed WHOLE def:NApotential:L623 in the PRINTED line657 resolution
convention. GENERAL KAHLER; actual unique all-resolution family; exact
source formulas and SAME-model NA/coherent faithful divisor equivalence.
No supplied approximation/resolution/dictionary premise.
Blueprint: trace-whole-source-endpoints.tex. -/
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
open AnalyticModificationLocalDiscrepancy SGPT.NAPotential.RIsoB
open SGPT.NAPotential.NATrace SGPT.NAPotential.TraceRes
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
  (Y : ClosedIrreducibleAnalyticSubvariety n X)

/-- The exact source formulas and resolution convention, with ACTUAL
same-common-model object pullbacks and faithful native divisor equivalence.
This is an OUTPUT predicate; no family or dictionary certificate is input
in either closed source producer below. -/
def IsOriginalResolutionTraceFamily (Γ : SourceNAPotential θ)
    (F : (R : ResolutionTarget Y) → SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff)) : Prop :=
  (∀ R, ResolutionTraceSpec Y Γ R (F R)) ∧
  ∀ R₁ R₂, ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V)
    (hp₁ : IsAnalyticModification (n := Y.dim) p₁) (hp₂ : IsAnalyticModification (n := Y.dim) p₂)
    (hc₁ : ∀ w, R₃.ι w = R₁.ι (p₁ w)) (hc₂ : ∀ w, R₃.ι w = R₂.ι (p₂ w)),
    (sourceNAPullback R₁.kahler hp₁ (F R₁)).changeRepresentative
        (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ) = F R₃ ∧
    (sourceNAPullback R₂.kahler hp₂ (F R₂)).changeRepresentative
        (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ) = F R₃ ∧
    ∀ (κ₁ : SourceKahlerForm Y.dim R₁.V) (κ₂ : SourceKahlerForm Y.dim R₂.V),
      nativeDivisorialFunction (F R₁) κ₁ = fun v => nativeDivisorialFunction (F R₂) κ₂
        (((nativeDivisorialEquiv hp₁).symm.trans (nativeDivisorialEquiv hp₂)) v)

/-- Closed actual whole-definition producer, GENERAL KAHLER and no
rational-line/metric/Chern/resolution/approximation/dictionary inputs. -/
theorem source_naTrace_family (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) :
    IsOriginalResolutionTraceFamily Y Γ (resolutionTraceFamily Y omegaX Γ hwd) := by
  refine ⟨resolutionTraceFamily_spec Y omegaX Γ hwd,?_⟩
  intro R₁ R₂
  obtain ⟨R₃,p₁,p₂,hp₁,hp₂,hc₁,hc₂,he₁,he₂⟩ := resolutionTraceFamily_common Y omegaX Γ hwd R₁ R₂
  refine ⟨R₃,p₁,p₂,hp₁,hp₂,hc₁,hc₂,he₁,he₂,?_⟩
  intro κ₁ κ₂
  let κ₃ := sourceKahlerFormOfBackground R₃.kahler
  have h₁ : nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
      fun v => nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₁
        (nativeDivisorialPush hp₁ v) := by
    have h := nativeDivisorialFunction_changeRepresentative
      (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ)
      (sourceNAPullback R₁.kahler hp₁ (resolutionTraceFamily Y omegaX Γ hwd R₁)) κ₃
    rw [he₁] at h
    exact h.trans (nativeDivisorialFunction_pullback R₁.kahler hp₁
      (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₃ κ₁)
  have h₂ : nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
      fun v => nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₂
        (nativeDivisorialPush hp₂ v) := by
    have h := nativeDivisorialFunction_changeRepresentative
      (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ)
      (sourceNAPullback R₂.kahler hp₂ (resolutionTraceFamily Y omegaX Γ hwd R₂)) κ₃
    rw [he₂] at h
    exact h.trans (nativeDivisorialFunction_pullback R₂.kahler hp₂
      (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₃ κ₂)
  funext v
  have h := (congrFun h₁ ((nativeDivisorialEquiv hp₁).symm v)).symm.trans
    (congrFun h₂ ((nativeDivisorialEquiv hp₁).symm v))
  have hpv : nativeDivisorialPush hp₁ ((nativeDivisorialEquiv hp₁).symm v) = v :=
    (nativeDivisorialEquiv hp₁).apply_symm_apply v
  rw [hpv] at h
  exact h

/-- WHOLE original def:NApotential:L623 under its explicit resolution
convention: UNIQUE ACTUAL family, exact original component formulas and
faithful SAME-common-model object/divisor coherence. -/
theorem source_naTrace_definition (omegaX : KahlerBackground n X) (Γ : SourceNAPotential θ)
    (hwd : carrierTraceWellDefined Y Γ) :
    ∃! F : (R : ResolutionTarget Y) → SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff),
      IsOriginalResolutionTraceFamily Y Γ F := by
  refine ⟨resolutionTraceFamily Y omegaX Γ hwd,source_naTrace_family Y omegaX Γ hwd,?_⟩
  intro F hF
  exact (existsUnique_resolutionTraceFamily Y omegaX Γ hwd).unique hF.1
    (resolutionTraceFamily_spec Y omegaX Γ hwd)

end SGPT.NAPotential.TraceComparison
