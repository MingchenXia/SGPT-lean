import SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection
import SGPT.Foundations.Analysis.Pending.ActualSmoothPositiveCurrentAbsoluteContinuity
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

/-! # Actual positive-current parts with an unrestricted smooth remainder

The positive quadratic is produced internally.  The unrestricted signed
current coefficient reader and global Siu assembly remain separate.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualSmoothRemainderCurrentParts
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorLocality LocalCurrentLebesgue
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing LocalBedfordTaylorCollar
  ActualPositiveCurrentLebesgueACAddition ActualSmoothLocalQuadraticCorrection
  ActualSmoothPositiveCurrentAbsoluteContinuity

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem smooth_differential_add
    {f g : ComplexModel (m + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ddc (scalarTopCurrent (regularDistribution volume (fun x => f x + g x)
      ((hf.add hg).continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) =
    ddc (scalarTopCurrent (regularDistribution volume f
      (hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) +
    ddc (scalarTopCurrent (regularDistribution volume g
      (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) := by
  have hl := LelongPoincareDivisor.regularDistribution_add' (μ := volume)
    (hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    ((hf.add hg).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
  have hscalar : scalarTopCurrent (regularDistribution volume (fun x => f x + g x)
      ((hf.add hg).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)) =
      scalarTopCurrent (regularDistribution volume f
        (hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)) +
      scalarTopCurrent (regularDistribution volume g
        (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)) := by
    ext γ φ
    simp only [scalarTopCurrent_apply, hl, _root_.add_apply, LinearMap.add_apply, mul_add]
  rw [hscalar, ddc_add]

private theorem parts_eq_of_current_eq {S T : LocalProductCurrent (m + 1) U m}
    (h : S = T) (hS : IsPositive S) (hT : IsPositive T) :
    sgPart hS = sgPart hT ∧ acPart hS = acPart hT := by
  subst T
  exact ⟨rfl, rfl⟩

/-- Natural positivity of the original sum and local smoothness produce
the complete parts on an actual smaller ball; the smooth remainder itself
need not be positive. -/
theorem exists_local_parts_of_smooth_remainder
    {F : LocalProductCurrent (m + 1) U m} (hF : IsPositive F)
    {b : ComplexModel (m + 1) → ℝ} (hb : ContDiffOn ℝ ∞ b U)
    (hC : IsPositive (F + ddc (scalarTopCurrent (regularDistribution volume b
      (hb.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)))))
    {z₀ : ComplexModel (m + 1)} (hz₀ : z₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      let V : Opens (ComplexModel (m + 1)) := ⟨ball z₀ r, isOpen_ball⟩
      ∃ hVU : V ≤ U,
        let hbV := hb.mono hVU
        let B := ddc (scalarTopCurrent (regularDistribution volume b
          (hbV.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)))
        ∃ hCV : IsPositive (restrict hVU F + B),
          sgPart hCV = sgPart (isPositive_restrict hF hVU) ∧
          acPart hCV = acPart (isPositive_restrict hF hVU) + B := by
  obtain ⟨A, r, _hA, hr, hball, hqP, hbqP⟩ :=
    exists_positive_quadratic_correction hb hz₀
  let V : Opens (ComplexModel (m + 1)) := ⟨ball z₀ r, isOpen_ball⟩
  have hVU : V ≤ U := hball
  have hbV : ContDiffOn ℝ ∞ b V := hb.mono hVU
  let q := ballPot A z₀ 0
  have hqV : ContDiffOn ℝ ∞ q V := (contDiff_ballPot A z₀ 0).contDiffOn
  let B := ddc (scalarTopCurrent (regularDistribution volume b
    (hbV.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)))
  let Q := ddc (scalarTopCurrent (regularDistribution volume q
    (hqV.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)))
  let R := ddc (scalarTopCurrent (regularDistribution volume (fun x => b x + q x)
    ((hbV.add hqV).continuousOn.locallyIntegrableOn V.isOpen.measurableSet)))
  obtain ⟨hQ, _, hQa, _, _⟩ := smooth_scalar_current_trace_and_parts hqV hqP
  obtain ⟨hR, _, hRa, _, _⟩ := smooth_scalar_current_trace_and_parts (hbV.add hqV) hbqP
  have hRBQ : R = B + Q := smooth_differential_add hbV hqV
  let FV := restrict hVU F
  let hFV := isPositive_restrict hF hVU
  let CV := FV + B
  have hBr : restrict hVU (ddc (scalarTopCurrent (regularDistribution volume b
      (hb.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)))) = B := by
    rw [ddc_scalarTopCurrent_restrict, restrictDistribution_regularDistribution]
  have hCr : restrict hVU (F + ddc (scalarTopCurrent (regularDistribution volume b
      (hb.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)))) = CV := by
    have hadd (S S' : LocalProductCurrent (m + 1) U m) :
        restrict hVU (S + S') = restrict hVU S + restrict hVU S' := by
      ext γ φ
      rfl
    rw [hadd, hBr]
  have hCV : IsPositive CV := by
    rw [← hCr]
    exact isPositive_restrict hC hVU
  have hsum : CV + Q = FV + R := by rw [hRBQ, ← add_assoc]
  have hleft := parts_of_add_absolutelyContinuous (T := CV) (B := Q) hCV hQ hQa
  have hright := parts_of_add_absolutelyContinuous (T := FV) (B := R) hFV hR hRa
  have htransport := parts_eq_of_current_eq hsum (hCV.add hQ) (hFV.add hR)
  have hsgLeft : sgPart (hFV.add hR) = sgPart hCV :=
    htransport.1.symm.trans hleft.1
  have hacLeft : acPart (hFV.add hR) = acPart hCV + Q :=
    htransport.2.symm.trans hleft.2
  refine ⟨r, hr, hVU, hCV, hsgLeft.symm.trans hright.1, ?_⟩
  apply add_right_cancel (b := Q)
  rw [← hacLeft, hright.2]
  change acPart hFV + R = (acPart hFV + B) + Q
  rw [hRBQ, ← add_assoc]

end SGPT.Foundations.Analysis.Pending.ActualSmoothRemainderCurrentParts
