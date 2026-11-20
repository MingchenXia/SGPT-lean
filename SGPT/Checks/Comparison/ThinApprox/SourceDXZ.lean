import SGPT.Checks.Comparison.ThinApprox.SourceDXZPositive
import SGPT.Checks.Comparison.ThinApprox.SourceDXZZero

/-! The actual original comparison, including zero dimension and the trivial valuation.
Blueprint: thin-source-dxz-all.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZ
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]
local instance : IsProper f := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

theorem source_DXZ (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).1 v ≤
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (SGPT.NAPotential.BJ.SourceNet.naAnalytification (θ := θ) f n E b HM hm hθ ω) := by
  cases n with
  | zero => exact SGPT.NAPotential.ThinApprox.BJ.SourceDXZZero.source_DXZ f E b HM hm hθ ω
  | succ k => exact SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive.source_DXZ f k E b HM hm hθ ω
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZ
