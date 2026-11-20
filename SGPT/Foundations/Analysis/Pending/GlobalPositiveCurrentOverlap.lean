import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
import SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport

set_option autoImplicit false

/-! # Actual overlap pullback of every full positive global current

The owned blueprint statements and ENTIRE proofs were completed first.
Only the original global full-test compatibility and source positivity are
used; the coordinate counterpart and local pullback equality are produced.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentOverlap

open FirstPass FirstPass.HolomorphicMaps GlobalCurrents GlobalCurrentPotentials
  _root_.SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  LocalProductCurrents LocalCurrentLebesgue LocalCurrentPullback
  LocalBedfordTaylorLocality LocalBedfordTaylorForms BedfordTaylor
  CompactVariableCurrentTests CanonicalComplementaryCurrentTests
  ActualAnalyticCurrentLocalDensity GlobalPositiveCurrentACRestriction

/-- Actual holomorphic chart transitions supply all six biholomorphic-pair
conditions, including dimension zero and empty overlap domains. -/
theorem isBiholomorphicPair_chartTransition
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (e f : ComplexChart n M) :
    IsBiholomorphicPair (overlapSource e f) (overlapTarget e f)
      (chartTransition e f) (chartTransition e f).symm := by
  refine {
    holo := fun x hx => (chartTransition_contDiffAt e f hx).contDiffWithinAt
    holo_inv := fun y hy => by
      change y ∈ (chartTransition e f).target at hy
      have hfun : ((chartTransition e f).symm : ComplexModel n → ComplexModel n) =
          chartTransition f e := funext (DDCOverlap.chartTransition_symm_apply e f)
      rw [hfun]
      apply (chartTransition_contDiffAt f e _).contDiffWithinAt
      simpa [chartTransition] using hy
    mapsTo := fun x hx => (chartTransition e f).map_source hx
    mapsTo_inv := fun y hy => (chartTransition e f).map_target hy
    left_inv := fun x hx => (chartTransition e f).left_inv hx
    right_inv := fun y hy => (chartTransition e f).right_inv hy }

private def castTestCLM {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b) :
    TestForm U a →L[ℝ] TestForm U b :=
  h ▸ ContinuousLinearMap.id ℝ (TestForm U a)

private theorem castTestCLM_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm U a) : castTestCLM h α = castTestDegree h α := by
  subst b
  rfl

private theorem castTestDegree_mono {n a b : ℕ} {U V : Opens (ComplexModel n)}
    (h : a = b) (_hUV : U ≤ V) (α : TestForm U a) :
    castTestDegree h (TestFunction.monoCLM ℝ α : TestForm V a) =
      (TestFunction.monoCLM ℝ (castTestDegree h α) : TestForm V b) := by
  subst b
  rfl

private theorem cast_related {n a b : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (h : a = b) (e f : ComplexChart n M)
    (α : TestForm (overlapSource e f) a) (β : TestForm (overlapTarget e f) a)
    (hrel : ∀ x ∈ (chartTransition e f).source, ∀ w : Fin a → ComplexModel n,
      α x w = β (chartTransition e f x)
        (fun i => chartTransitionDerivative e f x (w i))) :
    OverlapTestRelated e f (castTestDegree h α) (castTestDegree h β) := by
  subst b
  exact hrel

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem restricted_constant_reading
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {V : Opens (ComplexModel (m + 1))}
    (hV : V ≤ chartTarget e) (γ : formSpan (m + 1) m) (φ : 𝓓(V, ℝ)) :
    restrict hV (chartSpanCurrent T e) γ φ = T.restrictChart e hV
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
          (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)) := by
  have hext : constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) (extTest hV φ) =
      (TestFunction.monoCLM ℝ
        (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ) :
          TestForm (chartTarget e) (2 * m)) := by
    apply TestFunction.ext
    intro x
    rw [constantTestFormCLM_apply, extTest_apply, testForm_inclusion_apply hV,
      constantTestFormCLM_apply]
  change T.inChart e (castTestCLM _
      (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) (extTest hV φ))) =
    T.inChart e (TestFunction.monoCLM ℝ (castTestDegree _
      (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)))
  rw [hext, castTestCLM_apply, castTestDegree_mono _ hV]

private theorem restricted_full_span_reading
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {V : Opens (ComplexModel (m + 1))}
    (hV : V ≤ chartTarget e) (α : TestForm V (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    T.restrictChart e hV (castTestDegree
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∑ i, restrict hV (chartSpanCurrent T e) (formBasis (m + 1) m i) (coeffTest α i) := by
  classical
  have heq : α = ∑ i, constantTestFormCLM
      (formBasis (m + 1) m i : RealForm (m + 1) (2 * m)) (coeffTest α i) := by
    apply TestFunction.ext
    intro x
    simpa only [_root_.sum_apply, constantTestFormCLM_apply] using eq_sum_coeffTest α hα x
  conv_lhs => rw [heq]
  rw [← castTestCLM_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [castTestCLM_apply]
  exact (restricted_constant_reading T e hV _ _).symm

private theorem inverse_test_reading {n q : ℕ} {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {S : LocalProductCurrent n B q} (hS : IsPositive S)
    (γ : formSpan n q) (φ : 𝓓(A, ℝ)) (ζ : TestForm B (2 * q))
    (hζ : ∀ y ∈ B, ζ y = φ (σ y) •
      (γ : RealForm n (2 * q)).compContinuousLinearMap (fderiv ℝ σ y)) :
    (∑ i, S (formBasis n q i) (coeffTest ζ i)) = pullback h hS γ φ := by
  classical
  let hi : IsBiholomorphicPair B A σ τ :=
    ⟨h.holo_inv, h.holo, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩
  have hc (i : Fin (Module.finrank ℝ (formSpan n q))) (y : ComplexModel n) (hy : y ∈ B) :
      coeffTest ζ i y = φ (σ y) *
        (formBasis n q).repr (pullSpan q (fderiv ℂ σ y) γ) i := by
    change coeffCLM n q i (ζ y) = _
    rw [hζ y hy, fderiv_real_eq hi hy, map_smul]
    change φ (σ y) * (formBasis n q).repr
      (formProj n q (pullSpan q (fderiv ℂ σ y) γ : RealForm n (2 * q))) i = _
    rw [formProj_coe]
  have hint (i : Fin (Module.finrank ℝ (formSpan n q))) :=
    integrable_densityForm hS le_rfl (formBasis n q i) (coeffTest ζ i)
  have hcarried : hS.traceMeasure.restrict (B : Set (ComplexModel n)) = hS.traceMeasure :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hS.traceMeasure_compl)
  rw [pullback_apply, hcarried]
  simp only [apply_eq_integral_densityForm hS]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr hS.traceMeasure_compl] with y hy
  have heq : densityForm hS y (pullSpan q (fderiv ℂ σ y) γ) =
      ∑ i, (formBasis n q).repr (pullSpan q (fderiv ℂ σ y) γ) i *
        densityForm hS y (formBasis n q i) := by
    conv_lhs => rw [← (formBasis n q).sum_repr (pullSpan q (fderiv ℂ σ y) γ)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
  rw [heq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i y hy]
  exact mul_assoc _ _ _

/-- The original global overlap and internally transported FULL tensor tests
produce actual local pullback covariance in complementary degree `n-1`. -/
theorem pullback_chartSpanCurrent_eq_restrict
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e f : ComplexChart (m + 1) M) :
    pullback (isBiholomorphicPair_chartTransition e f)
      (isPositive_restrict (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent T hT f)
        (overlapTarget_le e f)) =
      restrict (overlapSource_le e f) (chartSpanCurrent T e) := by
  classical
  let F := chartTransition e f
  let h := isBiholomorphicPair_chartTransition e f
  let S := restrict (overlapTarget_le e f) (chartSpanCurrent T f)
  let hS := isPositive_restrict
    (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent T hT f)
      (overlapTarget_le e f)
  ext γ φ
  have hcounter := ActualChartOverlapTestTransport.exists_constant_form_counterpart
    e f ⊤ ⊤ (2 * m)
  have hU : (⟨(⊤ : Opens (ComplexModel (m + 1))) ∩
      (F.source ∩ F ⁻¹' (⊤ : Opens (ComplexModel (m + 1)))),
      (⊤ : Opens (ComplexModel (m + 1))).isOpen.inter
        (F.isOpen_inter_preimage (⊤ : Opens (ComplexModel (m + 1))).isOpen)⟩ :
      Opens (ComplexModel (m + 1))) = overlapSource e f := by
    ext x
    change x ∈ univ ∩ (F.source ∩ F ⁻¹' univ) ↔ x ∈ F.source
    simp only [preimage_univ, inter_univ, univ_inter]
  dsimp only at hcounter
  rw [hU, top_inf_eq] at hcounter
  obtain ⟨ζ, _hsupp, hζ, hrel⟩ := hcounter φ (γ : RealForm (m + 1) (2 * m))
  let α := constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ
  have hrelated := cast_related
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) e f α ζ hrel
  have hspan : ∀ y, ζ y ∈ formSpan (m + 1) m := by
    intro y
    by_cases hy : y ∈ overlapTarget e f
    · have hinv : IsBiholomorphicPair (overlapTarget e f) (overlapSource e f) F.symm F :=
        ⟨h.holo_inv, h.holo, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩
      have hyF : y ∈ (chartTransition e f).target := hy
      rw [hζ y, if_pos hyF, fderiv_real_eq hinv hy]
      exact (formSpan (m + 1) m).smul_mem _
        (compContinuousLinearMap_mem_formSpan _ γ.property)
    · rw [image_eq_zero_of_notMem_tsupport (fun hs => hy (ζ.tsupport_subset hs))]
      exact (formSpan (m + 1) m).zero_mem
  have ht := T.overlap e f _ _ hrelated
  rw [restricted_full_span_reading T f (overlapTarget_le e f) ζ hspan] at ht
  have htarget : (∑ i, S (formBasis (m + 1) m i) (coeffTest ζ i)) =
      pullback h hS γ φ := by
    apply inverse_test_reading h hS γ φ ζ
    intro y hy
    have hyF : y ∈ (chartTransition e f).target := hy
    rw [hζ y, if_pos hyF]
  rw [htarget] at ht
  exact ht.symm.trans (restricted_constant_reading T e (overlapSource_le e f) γ φ).symm

end SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentOverlap
