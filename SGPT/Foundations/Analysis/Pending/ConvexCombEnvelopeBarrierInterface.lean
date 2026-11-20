import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

set_option autoImplicit false

/-!
# Xia's admissible interval (2.28)

The weight condition of Xia, *Singularities of the plurisubharmonic envelope*,
Lemma 2.4.4 (`xia-sgpt:page-0083`): the interval (2.28), written in mass form
without division.  Step 1 of that lemma (`xia-sgpt:page-0084`--`page-0086`) is
assembled in `Pending.RooftopConvexCombBarrierStepOneAssembly` and used in
`Pending.ConvexCombEnvelopeMass`.

This module used to also carry Step 1 itself as a named external interface,
`xiaLemma244_step1_exists_thetaPsh_convexCombBarrier`.  Once Step 1 was
assembled from its own parts that interface had no consumer, and it was
retired by the human's decision I-0661.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- **Xia's interval (2.28), in mass form.** The weight `a` is admissible for
the masses `mphi ≤ mpsi` in dimension `n` when `a > 1` and
`aⁿ (mpsi - mphi) < mpsi`. This is the source interval written without
division, including its degenerate conventions automatically. -/
def IsAdmissibleWeight (n : ℕ) (mphi mpsi : ℝ≥0∞) (a : ℝ) : Prop :=
  1 < a ∧ ENNReal.ofReal (a ^ n) * (mpsi - mphi) < mpsi

theorem IsAdmissibleWeight.one_lt {mphi mpsi : ℝ≥0∞} {a : ℝ}
    (ha : IsAdmissibleWeight n mphi mpsi a) : 1 < a := ha.1

/-- In the equal-positive-mass case, every `a > 1` satisfies (2.28). -/
theorem isAdmissibleWeight_of_eq {m : ℝ≥0∞} (hm : 0 < m) {a : ℝ} (ha : 1 < a) :
    IsAdmissibleWeight n m m a := by
  refine ⟨ha, ?_⟩
  rw [tsub_self, mul_zero]
  exact hm

end

end SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
