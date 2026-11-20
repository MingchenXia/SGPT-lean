import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.CurrentPairing

set_option autoImplicit false

/-! Full NEW mathematical statement and ENTIRE proof precede this baseline. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualFiniteDivisorCurrentOffSupport
open FirstPass HolomorphicIdealSheaves GlobalCurrents GlobalCurrentPotentials
  _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem smooth_curvature_restrict_eq_neg_ddC
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (E : MeteredEffectiveQDivisor (m + 1) M) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget e)
    (hpot : IsSmoothLocalPotential (-E.curvature).val e W
      (fun y => (E.weight (e.val.symm y)).toReal)) :
    restrictForm (smoothFormDistribution b E.curvature.val e) hW =
      -ddC (regularDistribution b.addHaar
        (fun y => (E.weight (e.val.symm y)).toReal)
        (hpot.2.2.1.continuousOn.locallyIntegrableOn W.isOpen.measurableSet)) := by
  ext v φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hint : Integrable (fun y => (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) y •
      E.curvature.val.coeff e y) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b E.curvature.val e) _
  rw [restrictForm_apply, AlternatingMap.neg_apply, neg_apply, hv,
    ddC_regularDistribution_apply_of_contDiffOn hpot.2.2.1,
    smoothFormDistribution_apply, ← formEvaluationCLM_apply,
    ← (formEvaluationCLM _).integral_comp_comm hint, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [formEvaluationCLM_apply]
  rw [congrFun (testFunction_inclusion_coe hW φ) y]
  by_cases hy : y ∈ W
  · have hp := hpot.2.2.2 hy
    rw [ClosedRealOneOneForm.coeff_neg] at hp
    have hc : E.curvature.val.coeff e y =
        -smoothDDC (fun z => (E.weight (e.val.symm z)).toReal) y :=
      neg_eq_iff_eq_neg.mp hp.symm
    rw [hc, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
      smul_eq_mul, mul_neg]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (φ.tsupport_subset h))]
    simp

private theorem single_divisor_local_zero
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (E : MeteredEffectiveQDivisor (m + 1) M) {x : M}
    (hx : x ∉ E.support) (e : ComplexChart (m + 1) M) (hxe : x ∈ e.val.source) :
    ∃ (W : Opens (ComplexModel (m + 1))) (hW : W ≤ chartTarget e),
      e.val x ∈ W ∧
      restrictForm ((integrationCurrent b (Nat.succ_pos m) E).coefficients b e) hW = 0 := by
  obtain ⟨U, hxU, hpot⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hx e hxe
  let W : Opens (ComplexModel (m + 1)) := ⟨U, hpot.1⟩
  have hW : W ≤ chartTarget e := hpot.2.1
  refine ⟨W, hW, hxU, ?_⟩
  rw [coefficients_integrationCurrent, restrictForm_add, chartDDC, restrictForm_ddC,
    restrictDistribution_regularDistribution,
    smooth_curvature_restrict_eq_neg_ddC b E e hW hpot]
  exact add_neg_cancel _

private theorem restrict_twice
    {U V W : Opens (ComplexModel (m + 1))} (hVU : V ≤ U) (hWV : W ≤ V)
    (A : DistributionForm U 2) :
    restrictForm (restrictForm A hVU) hWV = restrictForm A (hWV.trans hVU) := by
  ext v φ
  simp only [restrictForm_apply]
  congr 1
  ext y
  rw [congrFun (testFunction_inclusion_coe hVU (TestFunction.monoCLM ℝ φ)) y,
    congrFun (testFunction_inclusion_coe hWV φ) y,
    congrFun (testFunction_inclusion_coe (hWV.trans hVU) φ) y]

private theorem full_restriction_zero_of_coefficients
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (C : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e)
    (hcoeff : restrictForm (C.coefficients b e) hW = 0) :
    C.restrictChart e hW = 0 := by
  have hfrom : fromLocalCurrent b (degreeTwo (Nat.succ_pos m)) (C.restrictChart e hW) = 0 := by
    ext v χ
    rw [GlobalCurrent.coefficients_restrictChart b C e hW v χ]
    exact congrArg (fun A => A v χ) hcoeff
  calc
    C.restrictChart e hW = toLocalCurrent b (degreeTwo (Nat.succ_pos m))
        (fromLocalCurrent b (degreeTwo (Nat.succ_pos m)) (C.restrictChart e hW)) :=
      (CurrentPairing.toLocalCurrent_fromLocalCurrent b (degreeTwo (Nat.succ_pos m)) _).symm
    _ = 0 := by
      rw [hfrom]
      ext η
      simp [toLocalCurrent, wedgePairing_apply]

/-- The actual finite divisor family produces a common ball on which
all coefficients and entire variable-test current restrictions vanish. -/
theorem exists_ball_finite_divisor_current_restrict_zero
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    {K : ℕ} (E : Fin K → MeteredEffectiveQDivisor (m + 1) M) (a : Fin K → ℝ)
    {x : M} (hx : ∀ j, x ∉ (E j).support)
    (e : ComplexChart (m + 1) M) (hxe : x ∈ e.val.source) :
    ∃ (r : ℝ) (_hr : 0 < r),
      let W : Opens (ComplexModel (m + 1)) := ⟨ball (e.val x) r, isOpen_ball⟩
      ∃ hW : W ≤ chartTarget e,
        (∀ j, restrictForm ((integrationCurrent b (Nat.succ_pos m) (E j)).coefficients b e)
          hW = 0 ∧ (integrationCurrent b (Nat.succ_pos m) (E j)).restrictChart e hW = 0) ∧
        let D := ∑ j, a j • integrationCurrent b (Nat.succ_pos m) (E j)
        restrictForm (D.coefficients b e) hW = 0 ∧ D.restrictChart e hW = 0 := by
  classical
  have hlocal := fun j => single_divisor_local_zero b (E j) (hx j) e hxe
  choose U hU hz hzero using hlocal
  have htarget : ∀ᶠ y in 𝓝 (e.val x), y ∈ chartTarget e :=
    (chartTarget e).isOpen.mem_nhds (e.val.map_source hxe)
  have hnear : ∀ᶠ y in 𝓝 (e.val x), y ∈ chartTarget e ∧ ∀ j, y ∈ U j :=
    htarget.and (eventually_all.mpr (fun j => (U j).isOpen.mem_nhds (hz j)))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let W : Opens (ComplexModel (m + 1)) := ⟨ball (e.val x) r, isOpen_ball⟩
  have hW : W ≤ chartTarget e := fun y hy => (hball y hy).1
  have hWU : ∀ j, W ≤ U j := fun j y hy => (hball y hy).2 j
  have hc : ∀ j, restrictForm
      ((integrationCurrent b (Nat.succ_pos m) (E j)).coefficients b e) hW = 0 := by
    intro j
    rw [← restrict_twice (hU j) (hWU j), hzero j]
    ext v χ
    rfl
  refine ⟨r, hr, hW, fun j => ⟨hc j,
    full_restriction_zero_of_coefficients b _ e hW (hc j)⟩, ?_⟩
  have hsum (s : Finset (Fin K)) :
      restrictForm ((∑ j ∈ s, a j • integrationCurrent b (Nat.succ_pos m) (E j)).coefficients
        b e) hW = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, GlobalCurrent.coefficients_zero]
      ext v χ
      rfl
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, GlobalCurrent.coefficients_add, restrictForm_add,
        GlobalCurrent.coefficients_smul]
      have hs : restrictForm
          (a j • (integrationCurrent b (Nat.succ_pos m) (E j)).coefficients b e) hW =
          a j • restrictForm ((integrationCurrent b (Nat.succ_pos m) (E j)).coefficients b e) hW := by
        ext v χ
        rfl
      rw [hs, hc j, ih, smul_zero, zero_add]
  exact ⟨hsum Finset.univ, full_restriction_zero_of_coefficients b _ e hW (hsum Finset.univ)⟩

end SGPT.Foundations.Analysis.Pending.ActualFiniteDivisorCurrentOffSupport
