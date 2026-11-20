import SGPT.Trace.TwistedL2MainStatement

/-!
# The finite-family functional bound in complex dimension zero

In dimension zero every (0,1) coordinate sum is empty. This proves the
actual functional bound without assuming the estimate, including arbitrary
(nonmeasurable or negative) data densities.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]

omit [BorelSpace X] in
/-- In dimension zero the actual finite-family functional estimate holds:
the data pairing is an empty coordinate sum for every test piece. -/
theorem twistedFunctionalBound_dim_zero : TwistedFunctionalBoundStatement 0 X := by
  intro T hfinite ι s c e ρ h hρ hh
  have hpair : ∀ i, T.localDataPairing (c i) (e i) (ρ i) (h i) = 0 := by
    intro i
    simp [TwistedDatum.localDataPairing, dbarPairing]
  simp [hpair]

end SGPT.Trace.TwistedL2
