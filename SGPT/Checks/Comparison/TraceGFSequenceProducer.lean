import SGPT.Checks.Comparison.TraceGFSequenceData
import SGPT.Checks.Comparison.TraceGFTwistLift
import SGPT.Checks.Comparison.DXZSurjAmple
import SGPT.Checks.Comparison.SourceNetTools
import SGPT.Checks.Comparison.SourceApproximationData

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
local instance gfSequenceProducerProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance gfSequenceProducerTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance gfSequenceProducerCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance gfSequenceProducerManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- The original primitive line bundle/metric/Chern compatibility and the
actual original BJ approximation manufacture EVERY rational GF curve and
its full ambient decreasing limit internally. The original approximation
assertion is the sole temporary external theorem boundary. -/
theorem exists_nativeGFSequence
    (happrox : SGPT.NAPotential.BJ.SourceApproximationData.Statement.{0} f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (r+1) EX L)
    {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)) :
    Nonempty (NativeGFSequence f r EX θ ((d : ℚ)⁻¹ • rationalPicardClass a)
      (naPotentialAnAt (r+1) EX Γ κX) κX) := by
  classical
  obtain ⟨S,hS,aS,HS,hK⟩ := BJ.DXZSurj.exists_isAmple_isKahler f (r+1) EX
  have hPSH := BJ.Exist.naPotentialAnAt_isModuleTopologyPSH.{0} f (r+1) EX a H hd hθ Γ κX
  obtain ⟨ε,ψ,hpos,hstrict,hε,hGF,hanti,hlim⟩ :=
    happrox S hS ((d : ℚ)⁻¹ • rationalPicardClass a) (naPotentialAnAt (r+1) EX Γ κX) hPSH
  have hGF' : ∀ i, IsRationalGF f ((d : ℚ)⁻¹ • rationalPicardClass a +
      ε i • rationalPicardClass aS) (ψ i) := by
    intro i
    rw [rationalPicardClass_atlas_independent aS (atlasOfInvertible hS.isInvertible)]
    exact hGF i
  choose G hG using fun i => exists_originalGF_twist_lift
    f r EX a H aS HS hd hθ κX (ε i) (hpos i).le (hGF' i)
  refine ⟨⟨S,aS,HS,hK,ε,hpos,hstrict,hε,G,?_,?_,?_⟩⟩
  · intro i
    rw [hG i]
    exact hGF' i
  · intro v i j hij
    simpa only [hG] using hanti v hij
  · intro v
    simpa only [hG] using hlim v

end SGPT.NAPotential.TraceComparison
