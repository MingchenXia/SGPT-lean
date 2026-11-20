import SGPT.Checks.Comparison.OperationCurveTransformSum
import SGPT.PSH.SourceNASum
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations

/-! SAME original NA sum components have literal addition on every
actual original prime. Blueprint: operation-na-sum-divisorial.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open Set SGPT.NAPotential.BJPrep
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

omit [BorelSpace X] in
/-- Actual original mutual intrinsic type gives exact complete transform
invariance, across different backgrounds and at the SAME genuine prime. -/
theorem curveDivisorialTransform_eq_of_POrder_equivalent
    {C : SourceTestCurve θ} {D : SourceTestCurve σ}
    (hCD : SourceTestCurvePOrder C D) (hDC : SourceTestCurvePOrder D C)
    (p : PrimePresentation n X) (t : ℝ) :
    curveDivisorialTransform C.toSourceTestCurvePredata p t =
      curveDivisorialTransform D.toSourceTestCurvePredata p t := by
  apply curveDivisorialTransform_congr _ _ p (le_antisymm hCD.cutoff_le hDC.cutoff_le)
  intro r hr hs
  have hCQ : (ofFixedModel n X).IsQPSH (C.potential ⟨r,hr⟩) := ⟨θ,C.thetaPSH _⟩
  have hDQ : (ofFixedModel n X).IsQPSH (D.potential ⟨r,hs⟩) := ⟨σ,D.thetaPSH _⟩
  have hI1 := sourceIOrder_of_sourcePOrder hCQ hDQ (hCD.slice_le r hr)
  have hI2 := sourceIOrder_of_sourcePOrder hDQ hCQ (hDC.slice_le r hs)
  exact le_antisymm ((sourceIOrder_iff_presentationComparison hDQ hCQ).mp hI2 p)
    ((sourceIOrder_iff_presentationComparison hCQ hDQ).mp hI1 p)

/-- The ACTUAL ORIGINAL NA sum has literal added values on every
actual source prime and positive REAL weight. Actual component and all
background transports are produced, no desired correspondence input. -/
theorem naDivisorialTransform_sum (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n X) (p : PrimePresentation n X) {t : ℝ} (ht : 0 < t) :
    naDivisorialTransform (Γ.sum Δ) ω p t =
      naDivisorialTransform Γ ω p t + naDivisorialTransform Δ ω p t := by
  let B := sourceKahlerFormRepresentative ω
  have hsum := Γ.sumComponent_POrder_equivalent_sum Δ ω B B
  have hΓ := Γ.realizedComponent_component_POrder_equivalent B ω
  have hΔ := Δ.realizedComponent_component_POrder_equivalent B ω
  change curveDivisorialTransform (Γ.sumComponent Δ ω).val.toSourceTestCurvePredata p t =
    curveDivisorialTransform (Γ.component ω).val.toSourceTestCurvePredata p t +
      curveDivisorialTransform (Δ.component ω).val.toSourceTestCurvePredata p t
  rw [curveDivisorialTransform_eq_of_POrder_equivalent hsum.1 hsum.2 p t,
    curveDivisorialTransform_sum B (Γ.realizedComponent B).val (Δ.realizedComponent B).val p ht,
    curveDivisorialTransform_eq_of_POrder_equivalent hΓ.1 hΓ.2 p t,
    curveDivisorialTransform_eq_of_POrder_equivalent hΔ.1 hΔ.2 p t]

end SGPT.NAPotential.OperationComparison
