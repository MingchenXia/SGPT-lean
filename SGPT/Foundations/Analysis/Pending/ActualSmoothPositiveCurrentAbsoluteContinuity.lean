import SGPT.Foundations.Analysis.Pending.LocalSmoothScalarCurrents
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition

set_option autoImplicit false

/-! # Actual smooth positive scalar currents and their genuine trace density

The smooth correction is made positive from natural smooth PSH input.
Arbitrary smooth remainders and global Siu assembly are separate.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualSmoothPositiveCurrentAbsoluteContinuity
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorCollar
  LocalCurrentPullbackDdc LocalSmoothScalarCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality ScalarLeviPositiveCurrent

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- Natural smooth PSH input produces positivity, its exact actual trace
density and both actual coefficient Lebesgue parts. -/
theorem smooth_scalar_current_trace_and_parts
    {g : ComplexModel (m + 1) → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hp : PlurisubharmonicOn (fun x => (g x : EReal)) U) :
    let T := regularDistribution volume g
      (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    ∃ hB : IsPositive (ddc (scalarTopCurrent T)),
      hB.traceMeasure = volume.withDensity
        (formWeight U (smoothDDC g) (kahlerPower (m + 1) m)) ∧
      hB.traceMeasure ≪ volume ∧
      sgPart hB = 0 ∧ acPart hB = ddc (scalarTopCurrent T) := by
  dsimp only
  let T := regularDistribution volume g
    (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
  have heq : ddc (scalarTopCurrent T) = ddcMul (oneCurrent U) g := by
    rw [ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge hg,
      ddcMul_eq_ddcWedge isPositive_oneCurrent (isClosedAny_oneCurrent (U := U)) hg]
  have hB : IsPositive (ddc (scalarTopCurrent T)) := by
    rw [heq]
    exact isPositive_ddcMul_oneCurrent
      (isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh hg hp))
  have hαc : ContinuousOn (smoothDDC g) U := (contDiffOn_ddcForm hg).continuousOn
  have hα : ∀ x ∈ U, IsSemipositiveOneOne (smoothDDC g x) :=
    fun _ hx => isSemipositiveOneOne_smoothDDC hg hp hx
  have hω : kahlerPower (m + 1) m ∈ posCone (m + 1) m :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm m
  have htr : hB.traceMeasure = volume.withDensity
      (formWeight U (smoothDDC g) (kahlerPower (m + 1) m)) := by
    apply eq_of_forall_testFunction_integral_eq hB.traceMeasure_compl
      (formWeight_compl (smoothDDC g) _)
      (fun K hK hKU => hB.traceMeasure_lt_top hK hKU) (formWeight_lt_top hαc _)
    intro φ
    rw [hB.integral_traceMeasure, heq, ddcMul_oneCurrent_apply hg,
      integral_formWeight hαc hα hω]
  have hAC : hB.traceMeasure ≪ volume := by
    rw [htr]
    exact withDensity_absolutelyContinuous _ _
  have hac : acPart hB = ddc (scalarTopCurrent T) :=
    acPart_eq_self_of_absolutelyContinuous hB hAC
  have hsg : sgPart hB = 0 := by
    have hsum := sgPart_add_acPart hB
    rw [hac] at hsum
    exact add_right_cancel (hsum.trans (zero_add _).symm)
  exact ⟨hB, htr, hAC, hsg, hac⟩

end SGPT.Foundations.Analysis.Pending.ActualSmoothPositiveCurrentAbsoluteContinuity
