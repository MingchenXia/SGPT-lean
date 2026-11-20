import SGPT.Checks.Comparison.BJExistCurve

/-! Same original analytification and original numerical-topology PSH codomain.
Blueprint: source-comparison-slices.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.SourceNet

open SGPT.NAPotential.BJ.Exist

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance sourceMapProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance sourceMapPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sourceMapPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance sourceMapPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include HM hm hθ in
/-- The original analytification function, equipped with its original PSH membership. -/
def naAnalytification (ω : SourceKahlerForm n (SchemeComplexPoint f)) (Γ : SourceNAPotential θ) :
    {ψ : BerkovichPoint f → EReal //
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ} :=
  ⟨naPotentialAnAt n E Γ ω, naPotentialAnAt_isModuleTopologyPSH.{0} f n E b HM hm hθ Γ ω⟩

theorem naAnalytification_apply (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (Γ : SourceNAPotential θ) (v : BerkovichPoint f) :
    (naAnalytification f n E b HM hm hθ ω Γ).1 v = naPotentialAnAt n E Γ ω v := rfl

end SGPT.NAPotential.BJ.SourceNet
