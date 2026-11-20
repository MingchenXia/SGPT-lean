import SGPT.Checks.Comparison.OperationPrimeReaderSum
import SGPT.PSH.SourcePIComparison

/-! Literal original ordinary-envelope convolution reader.
Blueprint: operation-sum-slice-readers.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open Set SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.PSH.CompactPrimeNumerical

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Actual source ordinary envelope leaves every SAME original prime
reader unchanged. Actual I-equivalence and genuine envelope PSH are internal. -/
theorem presentationReader_pEnvelope {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) (p : PrimePresentation n X) :
    presentationReader (sourceSingularityEnvelope θ u) p = presentationReader u p := by
  obtain ⟨z,hz⟩ := p.smooth.2.1.nonempty
  let : Nonempty X := ⟨p.projection z⟩
  have hI := sourceIEquivalent_pEnvelope hu
  have huq : (ofFixedModel n X).IsQPSH u := ⟨θ,hu⟩
  have hEq : (ofFixedModel n X).IsQPSH (sourceSingularityEnvelope θ u) :=
    ⟨θ,isThetaPSH_sourceSingularityEnvelope hu⟩
  exact le_antisymm ((sourceIOrder_iff_presentationComparison huq hEq).mp hI.1 p)
    ((sourceIOrder_iff_presentationComparison hEq huq).mp hI.2 p)

/-- The SAME actual ordinary test-curve sum's slice has exactly the
closed-interval infimal convolution of the SAME original endpoint-inclusive readers. -/
theorem presentationReader_sum_potential
    (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n X)
    (C : SourceTestCurve θ) (D : SourceTestCurve σ)
    (τ : Iio (SourceTestCurve.sum omega C D).max) (p : PrimePresentation n X) :
    presentationReader ((SourceTestCurve.sum omega C D).potential τ) p =
      ⨅ r : Icc ((τ : ℝ)-D.max) C.max,
        presentationReader (sourceTestCurveAt C.toSourceTestCurvePredata r.1) p +
          presentationReader (sourceTestCurveAt D.toSourceTestCurvePredata ((τ : ℝ)-r.1)) p := by
  have hτ : (τ : ℝ) ≤ C.max+D.max := τ.2.le
  rw [SourceTestCurve.sum_potential,
    presentationReader_pEnvelope (sourceTestCurveRawSum_thetaPSH
      C.toSourceTestCurvePredata D.toSourceTestCurvePredata hτ) p]
  exact presentationReader_rawSum C D hτ p

end SGPT.NAPotential.OperationComparison
