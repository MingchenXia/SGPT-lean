import SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Regular

set_option autoImplicit false

/-!
# Finiteness, regularity and constant-translation invariance of the diagonal measure

Three elementary properties of `diagonalPotentialMeasure` that the measure-level
statements of Xia's Chapter 3 need and that are not recorded elsewhere.

* **Finiteness.**  On a compact Kähler manifold the global mixed non-pluripolar
  measure is finite on every set (`globalMixedMeasure_apply_lt_top`), so the
  diagonal measure of a `theta`-PSH potential is a finite measure.
* **Outer regularity.**  A compact Hausdorff second-countable complex manifold is
  metrizable (mathlib's `Manifold.metrizableSpace`, applied through the *real*
  model with corners of the same model space), and a finite Borel measure on a
  pseudometrizable space is weakly regular.  Consequently an inequality between
  two diagonal measures which is known on all open sets holds on all sets.
* **Translation invariance.**  `theta^n_{v + C} = theta^n_v` for a real constant
  `C`, the diagonal case of `globalMixedMeasure_sub_const`.  This is the step
  that lets the `C -> infinity` limit of Xia's Corollary 3.1.1
  (`xia-sgpt:page-0101`) be taken against one fixed measure.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The diagonal non-pluripolar measure of any `theta`-PSH potential is finite
on every set, in the presence of a Kähler background. -/
theorem diagonalPotentialMeasure_lt_top (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (S : Set M) :
    diagonalPotentialMeasure theta u hu S < ⊤ :=
  globalMixedMeasure_apply_lt_top omega (fun _ => hu.1) S

/-- The diagonal non-pluripolar measure is a finite measure. -/
theorem isFiniteMeasure_diagonalPotentialMeasure (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) :
    IsFiniteMeasure (diagonalPotentialMeasure theta u hu) :=
  ⟨diagonalPotentialMeasure_lt_top omega theta hu univ⟩

/-- The canonical finite-measure packaging of a diagonal non-pluripolar
measure.  The Kähler finiteness theorem supplies the subtype witness, so weak
convergence statements can refer directly to the diagonal measures rather
than carrying an auxiliary sequence together with pointwise identifications. -/
def finiteDiagonalPotentialMeasure (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential theta.val u) : FiniteMeasure M :=
  ⟨diagonalPotentialMeasure theta u hu,
    isFiniteMeasure_diagonalPotentialMeasure omega theta hu⟩

/-- A compact complex manifold is metrizable: it is Hausdorff and σ-compact, and
its model space is a finite-dimensional real normed space. -/
theorem metrizableSpace_of_isComplexManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] : TopologicalSpace.MetrizableSpace M :=
  Manifold.metrizableSpace (modelWithCornersSelf ℝ (ComplexModel n)) M

theorem pseudoMetrizableSpace_of_isComplexManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] : TopologicalSpace.PseudoMetrizableSpace M :=
  letI := metrizableSpace_of_isComplexManifold n M
  inferInstance

/-- Every diagonal non-pluripolar measure is outer regular. -/
theorem outerRegular_diagonalPotentialMeasure (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) :
    (diagonalPotentialMeasure theta u hu).OuterRegular :=
  letI := pseudoMetrizableSpace_of_isComplexManifold n M
  letI := isFiniteMeasure_diagonalPotentialMeasure omega theta hu
  inferInstance


/-- **Constant translation invariance of the diagonal measure.**  Adding a real
constant to the potential does not change its diagonal non-pluripolar measure;
this is the diagonal case of `globalMixedMeasure_sub_const`. -/
theorem diagonalPotentialMeasure_add_const (theta : ClosedRealOneOneForm n M)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v) (C : ℝ)
    (hvC : IsThetaPshPotential theta.val (fun x => v x + (C : EReal))) :
    diagonalPotentialMeasure theta (fun x => v x + (C : EReal)) hvC =
      diagonalPotentialMeasure theta v hv := by
  have hsub := GlobalMeasureInvariance.globalMixedMeasure_sub_const
    (θ := fun _ : Fin n => theta) (u := fun _ => fun x => v x + (C : EReal))
    (fun _ => hvC.1) (fun _ => C)
  have hfun : (fun (_ : Fin n) (x : M) => (v x + (C : EReal)) - (C : EReal)) =
      fun (_ : Fin n) => v := by
    funext i x
    exact EReal.add_sub_cancel_right
  rw [diagonalPotentialMeasure, diagonalPotentialMeasure, ← hsub]
  exact GlobalDiagonalScaling.globalMixedMeasure_congr rfl hfun _ _

end

end SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
