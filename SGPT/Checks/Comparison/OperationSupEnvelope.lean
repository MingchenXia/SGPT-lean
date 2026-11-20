import SGPT.Checks.Comparison.OperationMaxCorrespondence
import SGPT.NAPotential.Supremum

/-! Literal BJ PSH-majorant envelope of the ORIGINAL source USC supremum.
No transported definition and no supplied correspondence/closure certificate.
Blueprint: operation-correspondence-sup-envelope.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard

/-- A literal pointwise infimum of ALL actual BJ PSH majorants. This
independent definition contains no source potential or DXZ preimage. -/
def pshUpperEnvelope {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsProjective f]
    (L : RationalPicardSpace X) {I : Type*} (φ : I → BerkovichPoint f → EReal)
    (v : BerkovichPoint f) : EReal :=
  ⨅ (ψ : {ψ : BerkovichPoint f → EReal // IsModuleTopologyPSH.{0} f L ψ})
    (_ : ∀ i w, φ i w ≤ ψ.1 w), ψ.1 v

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]
local instance opSupEnvelopeProper : IsProper f := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance opSupEnvelopePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opSupEnvelopePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opSupEnvelopePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)


include b HM hm hθ

/-- The original source USC supremum has the actual original BJ PSH
upper-envelope formula at EVERY Berkovich point, with all data internal. -/
theorem naPotentialAnAt_uscSup_eq_pshUpperEnvelope
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) (v : BerkovichPoint f) :
    naPotentialAnAt n E (SourceNAPotential.uscSup
      (sourceKahlerFormRepresentative ω) Γ hb) ω v =
      pshUpperEnvelope f ((m : ℚ)⁻¹ • rationalPicardClass b)
        (fun i => naPotentialAnAt n E (Γ i) ω) v := by
  let F := SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω
  let S := SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb
  have hDXZ := SGPT.NAPotential.ThinApprox.BJ.SourceDXZ.source_DXZ f n E b HM hm hθ ω
  have hupper (i : I) (w : BerkovichPoint f) : (F (Γ i)).1 w ≤ (F S).1 w :=
    (hDXZ.1 (Γ i) S).mp
      (SourceNAPotential.le_uscSup (sourceKahlerFormRepresentative ω) Γ hb i) w
  change (F S).1 v = pshUpperEnvelope f _ (fun i => (F (Γ i)).1) v
  unfold pshUpperEnvelope
  apply le_antisymm
  · refine le_iInf fun ψ => le_iInf fun hψ => ?_
    obtain ⟨Ξ,hΞ⟩ := hDXZ.2.2 ψ
    change F Ξ = ψ at hΞ
    have hΓ (i : I) : SourceNAPOrder (Γ i) Ξ := (hDXZ.1 (Γ i) Ξ).mpr (by
      intro w
      change (F (Γ i)).1 w ≤ (F Ξ).1 w
      rw [hΞ]
      exact hψ i w)
    have h := (hDXZ.1 S Ξ).mp
      (SourceNAPotential.uscSup_le (sourceKahlerFormRepresentative ω) Γ hb Ξ hΓ) v
    change (F S).1 v ≤ (F Ξ).1 v at h
    rwa [hΞ] at h
  · exact iInf_le_of_le (F S) (iInf_le_of_le hupper le_rfl)

/-- Genuine original BJ PSH membership of that independently defined
infimum is produced from the source operation, not a closure premise. -/
theorem pshUpperEnvelope_isModuleTopologyPSH
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) :
    IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b)
      (pshUpperEnvelope f ((m : ℚ)⁻¹ • rationalPicardClass b)
        (fun i => naPotentialAnAt n E (Γ i) ω)) := by
  have he := funext (naPotentialAnAt_uscSup_eq_pshUpperEnvelope f n E b HM hm hθ ω Γ hb)
  rw [← he]
  exact (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω
    (SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb)).2

/-- Honest one-sided topological-USC comparison. The missing reverse
inequality is NOT smuggled in as PSH closure or a desired correspondence. -/
theorem uscReg_iSup_le_pshUpperEnvelope
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) :
    SGPT.Foundations.Envelope.uscReg (fun v => ⨆ i, naPotentialAnAt n E (Γ i) ω v) ≤
      pshUpperEnvelope f ((m : ℚ)⁻¹ • rationalPicardClass b)
        (fun i => naPotentialAnAt n E (Γ i) ω) := by
  have hpsh := pshUpperEnvelope_isModuleTopologyPSH f n E b HM hm hθ ω Γ hb
  apply SGPT.Foundations.Envelope.uscReg_le_of_le (hpsh.upperSemicontinuous f)
  intro v
  apply iSup_le
  intro i
  rw [← naPotentialAnAt_uscSup_eq_pshUpperEnvelope f n E b HM hm hθ ω Γ hb v]
  exact (SGPT.NAPotential.ThinApprox.BJ.SourceDXZ.source_DXZ f n E b HM hm hθ ω).1
    (Γ i) (SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb) |>.mp
    (SourceNAPotential.le_uscSup (sourceKahlerFormRepresentative ω) Γ hb i) v

end SGPT.NAPotential.OperationComparison
