import SGPT.Checks.Comparison.OperationCurveScaling

/-! Arbitrary positive REAL scaling of the SAME actual original NA map.
No rationality/nef/scaled-line-presentation premise.
Blueprint: operation-correspondence-scaling.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]
local instance opNAScalePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opNAScalePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opNAScalePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}


/-- The original NA operation from def:NApotential:L572 has the literal
all-point formula for EVERY positive REAL scalar and EVERY actual component.
This function theorem does not assume a rational line presenting cθ. -/
theorem naPotentialAnAt_positiveScale
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt n E (Γ.positiveScale hc) ω v =
      (c : EReal) * naPotentialAnAt n E Γ ω v := by
  let B := sourceKahlerFormRepresentative ω
  have hs := Γ.positiveScaleComponent_POrder_equivalent_reader hc ω B
  have hr := Γ.realizedComponent_component_POrder_equivalent
    (sourceNADividedKahlerBackground hc B) ω
  have h1 := SourceTestCurvePOrder.trans B hs.1 (hr.1.positiveScale hc)
  have h2 := SourceTestCurvePOrder.trans B (hr.2.positiveScale hc) hs.2
  change openCurveAnAt n E (Γ.positiveScaleComponent hc ω).val v =
    (c : EReal) * openCurveAnAt n E (Γ.component ω).val v
  rw [openCurveAnAt_eq_of_POrder_equivalent n E h1 h2,
    openCurveAnAt_positiveScale n E (Γ.component ω).val hc v]

end SGPT.NAPotential.OperationComparison
