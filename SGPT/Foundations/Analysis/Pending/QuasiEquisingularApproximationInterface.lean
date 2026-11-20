import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-!
# Quasi-equisingular approximation: Xia, Theorem 1.6.2

This file states the global approximation theorem of Xia, *Singularities of
the plurisubharmonic envelope*, Theorem 1.6.2
(`xia-sgpt:page-0049`), which invokes Demailly's Bergman regularization: one
sequence simultaneously satisfying decreasing convergence, analytic singularity
type, and eventual multiplier-ideal inclusions.

It is no longer an input: the theorem is proved in
`Pending.QuasiEquisingularApproximationDemailly` from the proved Demailly
approximation theorem (`DemaillyApproximationSequence`,
`DemaillyApproximationAnalyticType`), with the multiplier-ideal clause by the
pointwise Young inequality.  The statement and name are kept here for its
consumers.
-/

open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximation

open FirstPass FirstPass.PositiveClasses
open FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **Xia, SGPT, Theorem 1.6.2** (`xia-sgpt:page-0049`), using Demailly's
regularization theorem; proved in
`QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation`. -/
theorem xiaTheorem162_exists_quasiEquisingularApproximation
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ ε : ℕ → ℝ, ∃ uSeq : ℕ → M → EReal,
      IsQuasiEquisingularApproximation omega θ u ε uSeq :=
  QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hu

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximation
