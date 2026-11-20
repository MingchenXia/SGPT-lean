import SGPT.Checks.Comparison.TracePrimeBirationalDictionary
import SGPT.Checks.Comparison.TraceGeneralResolutionFamily

/-! Genuine original native-divisor equivalence of ANY two actual resolution
targets, chosen from geometry BEFORE theta/Gamma/background. It identifies
ALL actual original trace-family reader functions. No new resolution proof.
Blueprint: trace-prime-birational-dictionary.tex. -/
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
  {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- The actual native divisor category is identified by a genuine geometric
EQUIVALENCE. The equivalence precedes ALL original theta/Gamma/background
choices, fixes trivial, and identifies every actual trace-family function.
No rational line/metric/Chern hypotheses or supplied dictionary witness. -/
theorem exists_nativeDivisorial_resolutionEquiv (R₁ R₂ : ResolutionTarget Y) :
    ∃ e : NativeDivisorialPoint Y.dim R₁.V ≃ NativeDivisorialPoint Y.dim R₂.V,
      e none = none ∧
      ∀ (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (Γ : SourceNAPotential θ)
        (hwd : carrierTraceWellDefined Y Γ) (omegaX : KahlerBackground n X)
        (κ₁ : SourceKahlerForm Y.dim R₁.V) (κ₂ : SourceKahlerForm Y.dim R₂.V),
      nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₁ =
        fun v => nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₂ (e v) := by
  obtain ⟨R₃,p₁,p₂,hp₁,hp₂,hc₁,hc₂⟩ := SGPT.Trace.P5Wire.exists_common_resolutionTarget R₁ R₂
  let e₁ := nativeDivisorialEquiv hp₁
  let e₂ := nativeDivisorialEquiv hp₂
  let e := e₁.symm.trans e₂
  refine ⟨e,?_,?_⟩
  · change nativeDivisorialEquiv hp₂ ((nativeDivisorialEquiv hp₁).symm none) = none
    rw [nativeDivisorialEquiv_symm_trivial,nativeDivisorialEquiv_apply,nativeDivisorialPush_trivial]
  · intro θ Γ hwd omegaX κ₁ κ₂
    let κ₃ := sourceKahlerFormOfBackground R₃.kahler
    let F₁ := nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₁
    let F₂ := nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₂
    have h₁ : nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
        fun v => F₁ (nativeDivisorialPush hp₁ v) := by
      have he := nativeDivisorialFunction_changeRepresentative
        (resolution_comm_class_eq R₁ R₃ hp₁.1 hc₁ θ)
        (sourceNAPullback R₁.kahler hp₁ (resolutionTraceFamily Y omegaX Γ hwd R₁)) κ₃
      dsimp only [resolutionTraceFamily] at he
      rw [naTraceResolution_dominates R₁ R₃ hp₁ hc₁ omegaX Γ
        (carrierTraceWellDefined_on Y Γ hwd R₁)] at he
      exact he.trans (nativeDivisorialFunction_pullback R₁.kahler hp₁
        (resolutionTraceFamily Y omegaX Γ hwd R₁) κ₃ κ₁)
    have h₂ : nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R₃) κ₃ =
        fun v => F₂ (nativeDivisorialPush hp₂ v) := by
      have he := nativeDivisorialFunction_changeRepresentative
        (resolution_comm_class_eq R₂ R₃ hp₂.1 hc₂ θ)
        (sourceNAPullback R₂.kahler hp₂ (resolutionTraceFamily Y omegaX Γ hwd R₂)) κ₃
      dsimp only [resolutionTraceFamily] at he
      rw [naTraceResolution_dominates R₂ R₃ hp₂ hc₂ omegaX Γ
        (carrierTraceWellDefined_on Y Γ hwd R₂)] at he
      exact he.trans (nativeDivisorialFunction_pullback R₂.kahler hp₂
        (resolutionTraceFamily Y omegaX Γ hwd R₂) κ₃ κ₂)
    funext v
    have hv := (congrFun h₁ (e₁.symm v)).symm.trans (congrFun h₂ (e₁.symm v))
    have hpush : nativeDivisorialPush hp₁ (e₁.symm v) = v := e₁.apply_symm_apply v
    change F₁ v = F₂ (nativeDivisorialPush hp₂ (e₁.symm v))
    rw [hpush] at hv
    exact hv

end SGPT.NAPotential.TraceComparison
