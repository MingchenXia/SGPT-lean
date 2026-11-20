import SGPT.Trace.TwistedL2FunctionalDimZeroMain
import SGPT.Trace.TwistedL2SingularWeaklyPseudoconvex

/-!
# Zero-dimensional weakly pseudoconvex twisted correction

The original zero-dimensional main correction theorem, together with the
existing exhaustion/removal argument, gives the weakly pseudoconvex singular
weight statement in dimension zero. Positive dimension remains open.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open SGPT.Foundations.Analysis.FirstPass

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]

/-- The original weakly pseudoconvex singular-weight twisted correction
statement holds without an added main-estimate hypothesis in complex
dimension zero. -/
theorem weaklyPseudoconvexTwistedL2CorrectionStatement_dim_zero :
    WeaklyPseudoconvexTwistedL2CorrectionStatement 0 X :=
  weaklyPseudoconvexTwistedL2CorrectionStatement_of_main 0 X
    twistedL2CorrectionStatement_dim_zero

end SGPT.Trace.TwistedL2
