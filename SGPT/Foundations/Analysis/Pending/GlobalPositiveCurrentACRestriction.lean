import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity

set_option autoImplicit false

/-! # Full positive global readings and exact AC top-measure restriction

The full blueprint statements and ENTIRE proofs precede this implementation.
Global compatibility remains internal to the actual `GlobalCurrent`; full
positivity is tested on its actual complementary compact forms.  Neither
closedness nor finite determinant mass is assumed or inferred here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction

open FirstPass FirstPass.MongeAmpere GlobalCurrents GlobalCurrentPotentials StronglyPositiveForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents LocalProductCurrents
  LocalBedfordTaylorLocality LocalCurrentLebesgue LocalCurrentDeterminant
  LocalCurrentDensityMatrix PositiveCurrentACTopMeasure
  CanonicalComplementaryCurrentTests ActualAnalyticCurrentLocalDensity

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Full positivity of the original global compact test functional, in every
genuine chart.  This is separate from closedness and type `(1,1)`. -/
def IsFullPositive (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∀ (e : ComplexChart (m + 1) M) (α : TestForm (chartTarget e) (2 * m)),
    (∀ x, α x ∈ spCone m) →
      0 ≤ T.inChart e (castTestDegree
        (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α)

private def castTestCLM {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b) :
    TestForm U a →L[ℝ] TestForm U b :=
  h ▸ ContinuousLinearMap.id ℝ (TestForm U a)

private theorem castTestCLM_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm U a) : castTestCLM h α = castTestDegree h α := by
  subst b
  rfl

/-- Actual global full positivity internally supplies each positive local
complementary coefficient current, with no local positivity certificate. -/
theorem isPositive_chartSpanCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M) :
    IsPositive (chartSpanCurrent T e) := by
  intro ι _ γ φ hγφ
  let α : TestForm (chartTarget e) (2 * m) :=
    ∑ i, constantTestFormCLM (γ i : RealForm (m + 1) (2 * m)) (φ i)
  have hα : ∀ x, α x ∈ spCone m := by
    intro x
    simpa only [α, _root_.sum_apply, constantTestFormCLM_apply] using hγφ x
  have hp := hT e α hα
  rw [← castTestCLM_apply] at hp
  change 0 ≤ T.inChart e (castTestCLM
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) at hp
  change 0 ≤ ∑ i, T.inChart e (castTestCLM
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
        (constantTestFormCLM (γ i : RealForm (m + 1) (2 * m)) (φ i)))
  simpa only [α, map_sum] using hp

variable {U V : Opens (ComplexModel (m + 1))}
  {T : LocalProductCurrent (m + 1) U m}

/-- The actual canonical RN density two-form commutes with restriction,
Haar-almost everywhere on the smaller open set, including zero RN weight. -/
theorem ae_acForm_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    ∀ᵐ x ∂volume, x ∈ V → acForm (isPositive_restrict hT hVU) x = acForm hT x := by
  classical
  let hR := isPositive_restrict hT hVU
  have hdb : ∀ᵐ x ∂hR.traceMeasure,
      ∀ i : Fin (Module.finrank ℝ (formSpan (m + 1) m)),
        densityForm hR x (formBasis (m + 1) m i) =
          densityForm hT x (formBasis (m + 1) m i) :=
    ae_all_iff.mpr fun i => densityForm_restrict_ae hT hVU (formBasis (m + 1) m i)
  have hd : ∀ᵐ x ∂hR.traceMeasure, densityForm hR x = densityForm hT x := by
    filter_upwards [hdb] with x hx
    exact (formBasis (m + 1) m).ext hx
  have hdac := (Measure.absolutelyContinuous_of_le (acMeasure_le hR)).ae_le hd
  change ∀ᵐ x ∂volume.withDensity (hR.traceMeasure.rnDeriv volume),
    densityForm hR x = densityForm hT x at hdac
  have hdvol := (ae_withDensity_iff (Measure.measurable_rnDeriv _ _)).mp hdac
  have hr := Measure.rnDeriv_restrict hT.traceMeasure volume V.isOpen.measurableSet
  rw [← traceMeasure_restrict hT hVU] at hr
  filter_upwards [hr, hdvol] with x hx hd hxV
  have hw : acWeight hR x = acWeight hT x := by
    unfold acWeight
    rw [hx, indicator_of_mem hxV]
  apply acForm_eq_of_forall hR x (isOneOne_acForm hT x)
  intro γ
  rw [← acWeight_mul_densityForm_eq hT x γ, hw]
  by_cases hz : hR.traceMeasure.rnDeriv volume x = 0
  · have hw0 : acWeight hT x = 0 := by
      rw [← hw]
      simp only [acWeight, hz, ENNReal.toReal_zero]
    simp only [hw0, zero_mul]
  · rw [hd hz]

/-- Exact restriction of the genuine AC top measure.  Infinite mass and the
empty open-set cases are retained without any finiteness premise. -/
theorem acTopMeasure_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    acTopMeasure (isPositive_restrict hT hVU) = (acTopMeasure hT).restrict V := by
  have hd : (fun x => ENNReal.ofReal (actualTopPowerDensity
      (acForm (isPositive_restrict hT hVU) x)))
      =ᵐ[volume.restrict (V : Set (ComplexModel (m + 1)))] fun x => ENNReal.ofReal
        (actualTopPowerDensity (acForm hT x)) := by
    have hform := (ae_restrict_iff' V.isOpen.measurableSet).mpr
      (ae_acForm_restrict hT hVU)
    filter_upwards [hform] with x hx
    rw [hx]
  unfold acTopMeasure
  rw [Measure.restrict_restrict_of_subset hVU,
    restrict_withDensity V.isOpen.measurableSet,
    restrict_withDensity V.isOpen.measurableSet]
  exact withDensity_congr_ae hd

end SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
