import SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
import SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

set_option autoImplicit false

/-!
# The obstacle truncated against the reference (Xia's Step 1.2, definitions)

The reference truncation `f \/ (V_theta - C)` of an obstacle and the quasi-continuity hypothesis
`RefTruncationsQuasiContinuous` used by Xia's Step 1.2 (`xia-sgpt:page-0080`--`page-0081`), together
with an elementary `ENNReal` squeeze.  They were stated in `Pending.RooftopTruncationConcentration`
and are moved here, under the same names and in the same namespace, so that the measurable form of
the Step 1.2 core (`Pending.RooftopTruncationConcentrationMeasurable`) can sit upstream of the upper
semicontinuous form, which is now its corollary.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### The obstacle truncated against the reference -/

/-- `f \/ (V_theta - C)`, Xia's truncation of the obstacle against the reference
rather than against a constant.  Truncating against the reference is what keeps
the capacity sandwich `V_theta - C <= P_theta(-) <= V_theta` with a **single**
constant, and it is the truncation whose quasi-continuity is available for the
Section 3.1 obstacles. -/
def refTrunc (theta : ClosedRealOneOneForm n M) (f : M → EReal) (C : ℝ) : M → EReal :=
  fun y => max (f y) (thetaPshSupremum theta.val y + ((-C : ℝ) : EReal))

theorem le_refTrunc (theta : ClosedRealOneOneForm n M) (f : M → EReal) (C : ℝ) (y : M) :
    f y ≤ refTrunc theta f C y := le_max_left _ _

theorem refShift_le_refTrunc (theta : ClosedRealOneOneForm n M) (f : M → EReal)
    (C : ℝ) (y : M) :
    thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) ≤ refTrunc theta f C y :=
  le_max_right _ _

/-- The reference truncations decrease to the obstacle: `V_theta <= 0`, so they
are squeezed between the obstacle and the constant truncations, whose infimum is
the obstacle. -/
theorem iInf_refTrunc (theta : ClosedRealOneOneForm n M) (f : M → EReal) (y : M) :
    (⨅ k : ℕ, refTrunc theta f (k : ℝ) y) = f y := by
  refine le_antisymm ?_ (le_iInf fun k => le_max_left _ _)
  refine le_of_le_of_eq (iInf_mono fun k => ?_)
    (RooftopUscDecreasingLimit.iInf_max_neg_natCast (f y))
  refine max_le_max (le_refl _) ?_
  calc thetaPshSupremum theta.val y + ((-(k : ℝ) : ℝ) : EReal)
      ≤ 0 + ((-(k : ℝ) : ℝ) : EReal) :=
        add_le_add (by simpa using thetaPshSupremum_le_zero theta.val y) (le_refl _)
    _ = ((-(k : ℝ) : ℝ) : EReal) := zero_add _

/-- **Quasi-continuity of every reference truncation of the obstacle.**  Xia's
hypothesis on the obstacle of Theorem 2.4.4, in the only form the proof uses it:
on compact subsets of an open set where `V_theta` is bounded, and for the
truncations `f \/ (V_theta - C)`, which is where the proof needs a finite real
function.

A minimum of two nonpositive `theta`-PSH potentials satisfies it, by
`Pending.RooftopTruncatedObstacleConcentration.exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle`. -/
def RefTruncationsQuasiContinuous (theta : ClosedRealOneOneForm n M)
    (f : M → EReal) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∀ Omega : Set M, IsOpen Omega →
    IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
    ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (refTrunc theta f C y).toReal) (K \ G)

/-! ### An `ENNReal` squeeze -/

/-- A quantity bounded by `K * eps` for every `eps > 0`, with `K` finite, is `0`. -/
theorem eq_zero_of_forall_le_mul_ofReal {mu K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ eps : ℝ, 0 < eps → mu ≤ K * ENNReal.ofReal eps) : mu = 0 := by
  refine le_antisymm ?_ zero_le
  have h0 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hten : Tendsto (fun m : ℕ => K * ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul h0 (Or.inr hK)
    simpa using this
  exact ge_of_tendsto hten (Eventually.of_forall fun m => h _ (by positivity))

end

end SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
