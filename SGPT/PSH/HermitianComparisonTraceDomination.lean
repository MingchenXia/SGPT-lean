import SGPT.PSH.HermitianComparisonTorsion
import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

/-!
# Positive smooth trace domination on possibly nonclosed currents

The finite lower-trace torsion bound is converted from fixed coordinate
forms to the Hermitian background by positivity alone. No current or
background closedness enters these cone and coefficient-current estimates.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonTraceDomination

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem formPower_smul (c : ℝ) (omega : RealForm n 2) :
    ∀ q, formPower (c • omega) q = c ^ q • formPower omega q
  | 0 => by simp only [formPower_zero, pow_zero, one_smul]
  | q + 1 => by
    rw [formPower_succ, formPower_succ, formPower_smul c omega q,
      coordinateWedge_smul_left, coordinateWedge_smul_right, smul_smul, pow_succ]

/-- Positivity of powers is monotone in the real `(1,1)` cone. -/
theorem formPower_sub_mem_spCone {A B : RealForm n 2}
    (hA : IsSemipositiveOneOne A) (hB : IsSemipositiveOneOne B)
    (hBA : IsSemipositiveOneOne (B - A)) :
    ∀ q, formPower B q - formPower A q ∈ spCone q
  | 0 => by simp only [formPower_zero, sub_self]; exact (spCone 0).zero_mem
  | q + 1 => by
    have he : formPower B (q + 1) - formPower A (q + 1) =
        coordinateWedge (formPower B q - formPower A q) B +
          coordinateWedge (formPower A q) (B - A) := by
      simp only [formPower_succ, ← wedgeBilin_apply, map_sub, LinearMap.sub_apply]
      abel
    rw [he]
    exact (spCone (q + 1)).add_mem
      (wedge_mem_spCone (formPower_sub_mem_spCone hA hB hBA q) hB)
      (wedge_mem_spCone (formPower_mem_spCone hA q) hBA)

theorem wedgeProd_mem_spCone : ∀ q (A : Fin q → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (A i)) → wedgeProd q A ∈ spCone q
  | 0, _, _ => unit_mem_spCone
  | q + 1, A, hA => wedge_mem_spCone
      (wedgeProd_mem_spCone q (fun i => A i.castSucc) (fun i => hA i.castSucc)) (hA (Fin.last q))

/-- Every factor in a mixed smooth trace can be replaced by a dominating
semipositive factor. The resulting difference is an actual cone element. -/
theorem wedgeProd_sub_mem_spCone : ∀ q (A B : Fin q → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (A i)) →
    (∀ i, IsSemipositiveOneOne (B i)) →
    (∀ i, IsSemipositiveOneOne (B i - A i)) →
    wedgeProd q B - wedgeProd q A ∈ spCone q
  | 0, _, _, _, _, _ => by simp only [wedgeProd_zero, sub_self]; exact (spCone 0).zero_mem
  | q + 1, A, B, hA, hB, hBA => by
    have he : wedgeProd (q + 1) B - wedgeProd (q + 1) A =
        coordinateWedge (wedgeProd q (fun i => B i.castSucc) -
          wedgeProd q (fun i => A i.castSucc)) (B (Fin.last q)) +
        coordinateWedge (wedgeProd q (fun i => A i.castSucc))
          (B (Fin.last q) - A (Fin.last q)) := by
      simp only [wedgeProd_succ, ← wedgeBilin_apply, map_sub, LinearMap.sub_apply]
      abel
    rw [he]
    exact (spCone (q + 1)).add_mem
      (wedge_mem_spCone (wedgeProd_sub_mem_spCone q _ _
        (fun i => hA i.castSucc) (fun i => hB i.castSucc) (fun i => hBA i.castSucc))
        (hB (Fin.last q)))
      (wedge_mem_spCone (wedgeProd_mem_spCone q _ (fun i => hA i.castSucc)) (hBA (Fin.last q)))

theorem contDiffOn_formPower {omega : ComplexModel n → RealForm n 2}
    (homega : ContDiffOn ℝ ∞ omega U) (q : ℕ) :
    ContDiffOn ℝ ∞ (fun x => formPower (omega x) q) U := by
  simpa only [formPower_eq_wedgeProd] using contDiffOn_wedgeProd q (fun _ => omega) (fun _ => homega)

/-- A pointwise dominated semipositive coordinate form can be replaced by
the Hermitian form in every genuine smooth trace wedge of a positive
current. Closedness is not assumed for the current or either form. -/
theorem isPositive_power_trace_difference {q : ℕ}
    (T : LocalProductCurrent n U q) (hT : IsPositive T)
    {omega gamma : ComplexModel n → RealForm n 2}
    (homega : ContDiffOn ℝ ∞ omega U) (hgamma : ContDiffOn ℝ ∞ gamma U)
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x))
    (hgammaP : ∀ x ∈ U, IsSemipositiveOneOne (gamma x))
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ x ∈ U, IsSemipositiveOneOne (C • omega x - gamma x)) :
    IsPositive (C ^ q • wedgeForm (by omega : 0 + q = q) T (contDiffOn_formPower homega q) -
      wedgeForm (by omega : 0 + q = q) T (contDiffOn_formPower hgamma q)) := by
  have hpoint : ∀ x ∈ U,
      C ^ q • formPower (omega x) q - formPower (gamma x) q ∈ spCone q := by
    intro x hx
    rw [← formPower_smul]
    exact formPower_sub_mem_spCone (hgammaP x hx) ((homegaP x hx).smul hC) (hdom x hx) q
  have hp := isPositive_wedgeForm (by omega : 0 + q = q) hT
    (((contDiffOn_formPower homega q).const_smul (C ^ q)).sub
      (contDiffOn_formPower hgamma q)) hpoint
  rw [SGPT.PSH.HermitianProducts.wedgeForm_sub (by omega : 0 + q = q) T
      ((contDiffOn_formPower homega q).const_smul (C ^ q)) (contDiffOn_formPower hgamma q),
    SGPT.PSH.HermitianProducts.wedgeForm_smul (by omega : 0 + q = q) T
      (contDiffOn_formPower homega q) (C ^ q)] at hp
  exact hp

/-- Positivity of an actual current difference gives domination of its
actual native trace measures, first on the coordinate domain. -/
theorem traceMeasureOn_le_of_positive_difference {q : ℕ}
    {S T : LocalProductCurrent n U q} (hS : IsPositive S) (hT : IsPositive T)
    (c : NNReal) (hdiff : IsPositive ((c : ℝ) • T - S)) :
    hS.traceMeasureOn ≤ c • hT.traceMeasureOn := by
  let := hS.isLocallyFiniteMeasure_traceMeasureOn
  let := hT.isLocallyFiniteMeasure_traceMeasureOn
  apply SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
  intro φ hφ
  rw [integral_smul_nnreal_measure, hS.integral_traceMeasureOn, hT.integral_traceMeasureOn]
  have hp := hdiff.positiveDistribution_trace φ hφ
  simp only [LinearMap.sub_apply, _root_.sub_apply, LinearMap.smul_apply,
    _root_.smul_apply, NNReal.smul_def, smul_eq_mul] at hp ⊢
  linarith

/-- The same actual native measure domination after extension by zero to
the ambient coordinate space; it applies to all measurable comparison sets. -/
theorem traceMeasure_le_of_positive_difference {q : ℕ}
    {S T : LocalProductCurrent n U q} (hS : IsPositive S) (hT : IsPositive T)
    (c : NNReal) (hdiff : IsPositive ((c : ℝ) • T - S)) :
    hS.traceMeasure ≤ c • hT.traceMeasure := by
  have h := Measure.map_mono (traceMeasureOn_le_of_positive_difference hS hT c hdiff)
    (measurable_subtype_coe : Measurable (Subtype.val : U → ComplexModel n))
  simpa only [IsPositive.traceMeasure, Measure.map_smul] using h

/-- The native positive measure of the smooth Hermitian trace. -/
def powerTraceMeasure {q : ℕ} (T : LocalProductCurrent n U q) (hT : IsPositive T)
    {omega : ComplexModel n → RealForm n 2} (homega : ContDiffOn ℝ ∞ omega U)
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x)) : Measure (ComplexModel n) :=
  (isPositive_wedgeForm (by omega : 0 + q = q) hT (contDiffOn_formPower homega q)
    (fun x hx => formPower_mem_spCone (homegaP x hx) q)).traceMeasure

theorem powerTraceMeasure_le {q : ℕ}
    (T : LocalProductCurrent n U q) (hT : IsPositive T)
    {omega gamma : ComplexModel n → RealForm n 2}
    (homega : ContDiffOn ℝ ∞ omega U) (hgamma : ContDiffOn ℝ ∞ gamma U)
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x))
    (hgammaP : ∀ x ∈ U, IsSemipositiveOneOne (gamma x))
    (C : NNReal) (hdom : ∀ x ∈ U, IsSemipositiveOneOne ((C : ℝ) • omega x - gamma x)) :
    powerTraceMeasure T hT hgamma hgammaP ≤ C ^ q • powerTraceMeasure T hT homega homegaP := by
  apply traceMeasure_le_of_positive_difference
  simpa only [NNReal.coe_pow] using isPositive_power_trace_difference T hT homega hgamma
    homegaP hgammaP C.coe_nonneg hdom

def mixedTraceMeasure {q : ℕ} (T : LocalProductCurrent n U q) (hT : IsPositive T)
    (A : Fin q → ComplexModel n → RealForm n 2)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hAP : ∀ i x, x ∈ U → IsSemipositiveOneOne (A i x)) : Measure (ComplexModel n) :=
  (isPositive_wedgeForm (by omega : 0 + q = q) hT (contDiffOn_wedgeProd q A hA)
    (fun x hx => wedgeProd_mem_spCone q (fun i => A i x) (fun i => hAP i x hx))).traceMeasure

/-- Mixed fixed correction and coordinate trace forms are all replaced by
the Hermitian background in one genuine native measure inequality. -/
theorem mixedTraceMeasure_le_powerTraceMeasure {q : ℕ}
    (T : LocalProductCurrent n U q) (hT : IsPositive T)
    {omega : ComplexModel n → RealForm n 2} (homega : ContDiffOn ℝ ∞ omega U)
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x))
    (A : Fin q → ComplexModel n → RealForm n 2)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hAP : ∀ i x, x ∈ U → IsSemipositiveOneOne (A i x))
    (C : NNReal)
    (hdom : ∀ i x, x ∈ U → IsSemipositiveOneOne ((C : ℝ) • omega x - A i x)) :
    mixedTraceMeasure T hT A hA hAP ≤ C ^ q • powerTraceMeasure T hT homega homegaP := by
  have hpoint : ∀ x ∈ U, (C : ℝ) ^ q • formPower (omega x) q -
      wedgeProd q (fun i => A i x) ∈ spCone q := by
    intro x hx
    rw [← formPower_smul, formPower_eq_wedgeProd]
    exact wedgeProd_sub_mem_spCone q (fun i => A i x) (fun _ => (C : ℝ) • omega x)
      (fun i => hAP i x hx) (fun _ => (homegaP x hx).smul C.coe_nonneg)
      (fun i => hdom i x hx)
  have hp := isPositive_wedgeForm (by omega : 0 + q = q) hT
    (((contDiffOn_formPower homega q).const_smul ((C : ℝ) ^ q)).sub
      (contDiffOn_wedgeProd q A hA)) hpoint
  rw [SGPT.PSH.HermitianProducts.wedgeForm_sub (by omega : 0 + q = q) T
      ((contDiffOn_formPower homega q).const_smul ((C : ℝ) ^ q)) (contDiffOn_wedgeProd q A hA),
    SGPT.PSH.HermitianProducts.wedgeForm_smul (by omega : 0 + q = q) T
      (contDiffOn_formPower homega q) ((C : ℝ) ^ q)] at hp
  apply traceMeasure_le_of_positive_difference
  simpa only [NNReal.coe_pow] using hp

end SGPT.PSH.HermitianComparisonTraceDomination
