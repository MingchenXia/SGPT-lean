import SGPT.Trace.TwistedL2FunctionalDimZeroMain
import SGPT.Trace.TwistedL2SingularCompact

/-!
# Zero-dimensional compact singular twisted correction

The original zero-dimensional main correction theorem, together with the
existing compact complement/removal argument, gives the compact singular
weight statement in dimension zero. Positive dimension remains open.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open SGPT.Foundations.Analysis.FirstPass

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]

/-- The original compact singular-weight twisted correction statement holds
without an added main-estimate hypothesis in complex dimension zero. -/
theorem compactTwistedL2CorrectionStatement_dim_zero :
    CompactTwistedL2CorrectionStatement 0 X :=
  compactTwistedL2CorrectionStatement_of_main 0 X twistedL2CorrectionStatement_dim_zero

end SGPT.Trace.TwistedL2
