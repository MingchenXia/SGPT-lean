import SGPT.Checks.Comparison.OperationUSCSupDivisorial
import SGPT.Checks.Comparison.OperationSupEnvelope
import SGPT.Checks.Comparison.OperationNativeDivisorialComparison
import SGPT.Checks.Comparison.ThinApprox.BJNativePSHAdmission

/-! The literal original USC operation corresponds to genuine topological uscReg.
No envelope-property/nef/output-PSH/regularization certificate assumption.
Blueprint: operation-usc-supremum.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]
local instance uscComparisonProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance uscComparisonPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance uscComparisonPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance uscComparisonPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)
  {m : ℕ} (hm : 0 < m)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
include b HM hm hθ

/-- The SAME original map sends the actual USC supremum to genuine
TOPOLOGICAL upper regularization on ALL points, including n0/trivial/poles.
Original primitive rational Chern data and cutoff bound only. -/
theorem naPotentialAnAt_uscSup_eq_uscReg
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) :
    naPotentialAnAt n E (SourceNAPotential.uscSup
      (sourceKahlerFormRepresentative ω) Γ hb) ω =
      SGPT.Foundations.Envelope.uscReg (fun v => ⨆ i, naPotentialAnAt n E (Γ i) ω v) := by
  let S := SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb
  have hS := (SourceNet.naAnalytification f n E b HM hm hθ ω S).2
  change IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b)
    (naPotentialAnAt n E S ω) at hS
  have hSnative := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH f hS
  have henv := funext (naPotentialAnAt_uscSup_eq_pshUpperEnvelope f n E b HM hm hθ ω Γ hb)
  have hforward := uscReg_iSup_le_pshUpperEnvelope f n E b HM hm hθ ω Γ hb
  rw [← henv] at hforward
  obtain ⟨B,hB⟩ := hS.trivial_finite f
  have hbound (v : BerkovichPoint f) : naPotentialAnAt n E S ω v ≤ (B : EReal) := by
    have h := hS.le_trivial f v
    rwa [hB] at h
  have hregtop (v : BerkovichPoint f) :
      SGPT.Foundations.Envelope.uscReg (fun v => ⨆ i, naPotentialAnAt n E (Γ i) ω v) v ≠ ⊤ :=
    ne_of_lt (((hforward v).trans (hbound v)).trans_lt (EReal.coe_lt_top B))
  have hreverse := nativePSH_le_of_sourceDivisorial_le f hSnative
    (SGPT.Foundations.Envelope.upperSemicontinuous_uscReg _) hregtop (by
      intro v hv
      rw [naPotentialAnAt_uscSup_on_sourceDivisorialSet f n E b HM hm hθ ω Γ hb v hv]
      exact SGPT.Foundations.Envelope.le_uscReg
        (fun w : BerkovichPoint f => ⨆ i, naPotentialAnAt n E (Γ i) ω w) v)
  exact le_antisymm hreverse hforward

/-- Genuine ORIGINAL rational-class module-topology PSH of the literal
upper regularization is produced, without any such closure premise. -/
theorem uscReg_iSup_isModuleTopologyPSH
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) :
    IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b)
      (SGPT.Foundations.Envelope.uscReg (fun v => ⨆ i, naPotentialAnAt n E (Γ i) ω v)) := by
  rw [← naPotentialAnAt_uscSup_eq_uscReg f n E b HM hm hθ ω Γ hb]
  exact (SourceNet.naAnalytification f n E b HM hm hθ ω
    (SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb)).2

/-- CLOSED source USC operation clause as equality in the SAME ORIGINAL
BJ PSH subtype, with literal topological regularization and actual produced
original membership. No transported operation definition. -/
theorem source_uscSup_correspondence
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (Set.range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i))) :
    SourceNet.naAnalytification f n E b HM hm hθ ω
      (SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb) =
      ⟨SGPT.Foundations.Envelope.uscReg (fun v => ⨆ i,
        (SourceNet.naAnalytification f n E b HM hm hθ ω (Γ i)).1 v),
        uscReg_iSup_isModuleTopologyPSH f n E b HM hm hθ ω Γ hb⟩ := by
  apply Subtype.ext
  exact naPotentialAnAt_uscSup_eq_uscReg f n E b HM hm hθ ω Γ hb

end SGPT.NAPotential.OperationComparison
