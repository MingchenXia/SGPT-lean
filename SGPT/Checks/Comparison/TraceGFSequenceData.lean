import SGPT.Checks.Comparison.TraceGFTwists
import SGPT.NAPotential.BerkovichNAPotential

/-! The actual original rational GF curves lifted from the original BJ
approximation, with the given curve's actual full analytification as limit.
Blueprint: trace-na-general-family.tex. The original approximation theorem
is explicit pending its independent parent-owned narrow verification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.TraceComparison.GFTwist
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (r : ℕ)
  [SmoothOfRelativeDimension (r+1) f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance gfSequenceDataProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance gfSequenceDataTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance gfSequenceDataCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance gfSequenceDataManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- Actual curves in the actual perturbation classes. This intermediate
record is MANUFACTURED by the original approximation and GF hull theorems;
the general trace endpoint does not take it as a certificate. -/
structure NativeGFSequence
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f)))
    (LQ : RationalPicardSpace X) (φ : BerkovichPoint f → EReal)
    (κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)) where
  line : X.Modules
  atlas : LineBundleAtlas line
  metric : SchemeLineBundleMetric f (r+1) EX line
  kahler : (metric.curvature atlas).val.IsKahler
  epsilon : ℕ → ℚ
  positive : ∀ i, 0 < epsilon i
  strictAnti : StrictAnti epsilon
  epsilon_tendsto : Tendsto (fun i => (epsilon i : ℝ)) atTop (𝓝 0)
  member : ∀ i, SourceNAPotential (twistForm f (r+1) EX atlas metric θ (epsilon i : ℝ))
  member_GF : ∀ i, IsRationalGF f (LQ + epsilon i • rationalPicardClass atlas)
    (naPotentialAnAt (r+1) EX (member i) κX)
  antitone : ∀ v, Antitone fun i => naPotentialAnAt (r+1) EX (member i) κX v
  tendsto : ∀ v, Tendsto (fun i => naPotentialAnAt (r+1) EX (member i) κX v) atTop (𝓝 (φ v))

end SGPT.NAPotential.TraceComparison
