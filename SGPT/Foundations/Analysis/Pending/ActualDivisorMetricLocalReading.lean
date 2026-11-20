import SGPT.Foundations.Analysis.Pending.ActualMeteredDivisorSingularReading
import SGPT.Foundations.Analysis.Pending.ActualSmoothRemainderCurrentParts
import SGPT.Foundations.Analysis.Pending.DivisorMetric

set_option autoImplicit false

/-! # The full normalized local current of a genuine divisor metric

The complete mathematical statement and ENTIRE proof precede this baseline.
The metric and the invertible ideal are natural inputs; the generator,
nonzero germs, reading domain and full current identity are produced.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
namespace SGPT.Foundations.Analysis.Pending.ActualDivisorMetricLocalReading
open FirstPass FirstPass.HolomorphicIdealSheaves GlobalCurrents
  StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalCurrentLebesgue ScalarLeviPositiveCurrent
  ActualDistributionTwoFormReading ActualDistributionTwoFormDdc
  ActualOpenLogarithmicDivisorSingularity ActualMeteredDivisorSingularReading
  ActualSmoothRemainderCurrentParts DivisorIntegrationCurrent LocalPositiveCurrentGluing

open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}

private def readerLinear : DistributionForm U 2 →ₗ[ℝ] LocalProductCurrent (m + 1) U m where
  toFun := complementaryRead
  map_add' A B := by
    ext γ φ
    simp only [complementaryRead, AlternatingMap.add_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply,
      _root_.smul_apply, _root_.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext γ φ
    have hmul (r s : ℝ) : r * (c * s) = c * (r * s) := by ring
    simp only [complementaryRead, AlternatingMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    simp only [hmul, ← Finset.mul_sum]

private theorem reader_restrict (hVU : V ≤ U) (A : DistributionForm U 2) :
    restrict hVU (complementaryRead A) =
      complementaryRead (LelongPoincareDivisor.restrictForm A hVU) := by
  ext γ φ
  simp only [complementaryRead, LocalBedfordTaylorLocality.restrict_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    LelongPoincareDivisor.restrictForm_apply, extTest]

private theorem restrict_twice {W : Opens (ComplexModel (m + 1))}
    (hVU : V ≤ U) (hWV : W ≤ V) (T : LocalProductCurrent (m + 1) U m) :
    restrict hWV (restrict hVU T) = restrict (hWV.trans hVU) T := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply]
  congr 1
  ext y
  simp only [extTest_apply]

private theorem divisor_reading_restrict {g : ComplexModel (m + 1) → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (hVU : V ≤ U) :
    restrict hVU (complementaryRead (DivisorIntegrationCurrent.divisorCurrent hg hg0)) =
      complementaryRead (DivisorIntegrationCurrent.divisorCurrent (hg.mono hVU)
        (fun y hy => hg0 y (hVU hy))) := by
  rw [← ddC_log_normSq_eq_divisorCurrent, complementaryRead_ddC,
    ddc_scalarTopCurrent_restrict, restrictDistribution_regularDistribution,
    ← complementaryRead_ddC, ddC_log_normSq_eq_divisorCurrent]

private theorem regular_sub {μ : Measure (ComplexModel (m + 1))}
    {f g : ComplexModel (m + 1) → ℝ}
    (hf : LocallyIntegrableOn f U μ) (hg : LocallyIntegrableOn g U μ) :
    regularDistribution μ (fun y => f y - g y) (hf.sub hg) =
      regularDistribution μ f hf - regularDistribution μ g hg := by
  ext φ
  have hiF : Integrable (fun y => φ y * f y) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf φ
  have hiG : Integrable (fun y => φ y * g y) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hg φ
  rw [regularDistribution_apply, _root_.sub_apply, regularDistribution_apply,
    regularDistribution_apply, ← integral_sub hiF hiG]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem metric_generator
    (D : EffectiveDivisor (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hm : DivisorMetric.IsDivisorMetric D E) (x : M) :
    ∃ (V : Set M), IsOpen V ∧ x ∈ V ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g V ∧
      (∀ W : Set M, IsOpen W → W ⊆ V → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ V, ∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := m + 1) (· = g) y f) ∧
      ∃ H : M → ℝ,
        (∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞ (fun z => H (e.val.symm z))
          (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
        ∀ y ∈ V, E.weight y = generatorLog (fun _ : Fin 1 => g) y + (H y : EReal) := by
  obtain ⟨V₀, hV₀, hx₀, g₀, hg₀, hn₀, hgen₀⟩ := D.isInvertible x
  obtain ⟨V₁, hV₁, hx₁, g, hg, hgen, H, hH, he⟩ := hm x
  obtain ⟨V, u, hV, hxV, hsub, _hu, hun, heq⟩ :=
    DivisorMetric.exists_unit_of_generators hV₀ hV₁ hg₀ hg hn₀ hgen₀ hgen hx₀ hx₁
  refine ⟨V, hV, hxV, g, hg.mono (fun y hy => (hsub hy).2), ?_,
    fun y hy => hgen y (hsub hy).2, H, ?_, fun y hy => he y (hsub hy).2⟩
  · intro W hW hWV hne
    obtain ⟨y, hy, hgy⟩ := hn₀ W hW (fun y hy => (hsub (hWV hy)).1) hne
    refine ⟨y, hy, ?_⟩
    rw [heq y (hWV hy)]
    exact mul_ne_zero (hun y (hWV hy)) hgy
  · intro e
    exact (hH e).mono (fun y hy => ⟨hy.1, (hsub hy.2).2⟩)

omit [IsComplexManifold (m + 1) M] in
private theorem chart_generator_frequent
    {V : Set M} (hV : IsOpen V) {g : M → ℂ}
    (hn : ∀ W : Set M, IsOpen W → W ⊆ V → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (e : ComplexChart (m + 1) M) :
    ∀ y ∈ e.val.target ∩ e.val.symm ⁻¹' V,
      ∃ᶠ z in 𝓝 y, g (e.val.symm z) ≠ 0 := by
  let U : Opens (ComplexModel (m + 1)) :=
    ⟨e.val.target ∩ e.val.symm ⁻¹' V, e.val.isOpen_inter_preimage_symm hV⟩
  intro y hy
  rw [Filter.frequently_iff]
  intro s hs
  obtain ⟨W, hWs, hWo, hyW⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem hs (U.isOpen.mem_nhds hy))
  have hWt : W ⊆ e.val.symm.source := fun z hz => (hWs hz).2.1
  have hWopen : IsOpen (e.val.symm '' W) :=
    e.val.symm.isOpen_image_of_subset_source hWo hWt
  have hWV : e.val.symm '' W ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hWs hz).2.2
  obtain ⟨_, ⟨z, hzW, rfl⟩, hm⟩ := hn _ hWopen hWV ⟨_, mem_image_of_mem _ hyW⟩
  exact ⟨z, (hWs hzW).1, hm⟩

private theorem metric_current_eq
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (E : MeteredEffectiveQDivisor (m + 1) M)
    (e : ComplexChart (m + 1) M) (P : LelongPoincareDivisor.LocalPresentation E)
    (hUP : U ≤ P.chartDomain e) {G : ComplexModel (m + 1) → ℂ}
    (hG : DifferentiableOn ℂ G U) (hG0 : ∀ y ∈ U, ∃ᶠ w in 𝓝 y, G w ≠ 0)
    {H : ComplexModel (m + 1) → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (he : ∀ y ∈ U, chartFunction E.weight e y =
      generatorLog (fun _ : Fin 1 => G) y + (H y : EReal)) :
    let B := fun y => (LelongPoincareDivisor.haarFactor b : ℝ) * (H y - P.chartH e y)
    let hB : ContDiffOn ℝ ∞ B U :=
      contDiffOn_const.mul (hH.sub ((P.contDiffOn_chartH e).mono (fun _y hy => hUP hy)))
    restrict (hUP.trans (P.chartDomain_le e)) (complementaryRead
      ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)) =
      (LelongPoincareDivisor.haarFactor b : ℝ) • complementaryRead (divisorCurrent hG hG0) +
        ddc (scalarTopCurrent (regularDistribution volume B
          (hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) := by
  let hUe := hUP.trans (P.chartDomain_le e)
  let f := fun y => (chartFunction E.weight e y).toReal
  let H' := fun y => H y - P.chartH e y
  have hH' : ContDiffOn ℝ ∞ H' U :=
    hH.sub ((P.contDiffOn_chartH e).mono (fun y hy => hUP hy))
  have hf : LocallyIntegrableOn f U b.addHaar :=
    (LelongPoincareDivisor.chartLocallyIntegrable_weight b E e).mono_set (fun y hy => hUe hy)
  have hP : LocallyIntegrableOn (P.chartH e) U b.addHaar :=
    (((P.contDiffOn_chartH e).mono hUP).continuousOn.locallyIntegrableOn
      U.isOpen.measurableSet)
  have hA : LelongPoincareDivisor.restrictForm
      ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e) hUe =
      ddC (regularDistribution b.addHaar (fun y => f y - P.chartH e y) (hf.sub hP)) := by
    have h := congrArg (fun A => LelongPoincareDivisor.restrictForm A hUP)
      (LelongPoincareDivisor.restrictForm_coefficients_eq_ddC b (Nat.succ_pos m) P e)
    have htwice : LelongPoincareDivisor.restrictForm
        (LelongPoincareDivisor.restrictForm
          ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
          (P.chartDomain_le e)) hUP =
        LelongPoincareDivisor.restrictForm
          ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
          hUe := by
      ext v φ
      simp only [LelongPoincareDivisor.restrictForm_apply]
      congr 1
      ext y
      rw [congrFun (testFunction_inclusion_coe (P.chartDomain_le e)
        (TestFunction.monoCLM ℝ φ)) y,
        congrFun (testFunction_inclusion_coe hUP φ) y,
        congrFun (testFunction_inclusion_coe hUe φ) y]
    rw [htwice, LelongPoincareDivisor.restrictForm_ddC] at h
    have hsub (S T : 𝓓'(P.chartDomain e, ℝ)) :
        restrictDistribution (S - T) hUP =
          restrictDistribution S hUP - restrictDistribution T hUP := rfl
    have hrt (T : 𝓓'(chartTarget e, ℝ)) :
        restrictDistribution (restrictDistribution T (P.chartDomain_le e)) hUP =
          restrictDistribution T hUe := by
      ext φ
      simp only [restrictDistribution_apply]
      congr 1
      ext y
      rw [congrFun (testFunction_inclusion_coe (P.chartDomain_le e)
        (TestFunction.monoCLM ℝ φ)) y,
        congrFun (testFunction_inclusion_coe hUP φ) y,
        congrFun (testFunction_inclusion_coe hUe φ) y]
    rw [hsub, hrt, restrictDistribution_regularDistribution,
      restrictDistribution_regularDistribution] at h
    exact h.trans (congrArg ddC (regular_sub hf hP).symm)
  have hf' : LocallyIntegrableOn f U (LelongPoincareDivisor.haarFactor b • volume) := by
    rw [← LelongPoincareDivisor.addHaar_eq_smul b]
    exact hf
  have hP' : LocallyIntegrableOn (P.chartH e) U
      (LelongPoincareDivisor.haarFactor b • volume) := by
    rw [← LelongPoincareDivisor.addHaar_eq_smul b]
    exact hP
  have hae : ∀ᵐ y ∂(volume.restrict U), f y - P.chartH e y =
      ∑ _i : Fin 1, (1 : ℝ) * Real.log (‖G y‖ ^ 2) + H' y := by
    filter_upwards [LelongPoincareDivisor.ae_ne_zero U.isOpen hG hG0,
      ae_restrict_mem U.isOpen.measurableSet] with y hy hyU
    dsimp only [f, H']
    rw [he y hyU, LelongPoincareDivisor.generatorLog_one_of_ne_zero hy,
      ← EReal.coe_add, EReal.toReal_coe]
    simp only [Fintype.sum_unique, one_mul]
    ring
  have hLP := LelongPoincareDivisor.ddC_eq_sum_divisorCurrent_add
    (LelongPoincareDivisor.haarFactor b) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => hG) (fun _ => hG0) hH' hae (hf'.sub hP')
  simp only [Fintype.sum_unique, one_smul] at hLP
  have hHv := hH'.continuousOn.locallyIntegrableOn U.isOpen.measurableSet (μ := volume)
  let B := fun y => (LelongPoincareDivisor.haarFactor b : ℝ) * H' y
  have hB : ContDiffOn ℝ ∞ B U := contDiffOn_const.mul hH'
  have hBv := hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet (μ := volume)
  have hdist : regularDistribution (LelongPoincareDivisor.haarFactor b • volume) H'
      (hH'.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) =
      regularDistribution volume B hBv := by
    rw [LelongPoincareDivisor.regularDistribution_smul_measure
      (LelongPoincareDivisor.haarFactor b) hHv]
    exact (LelongPoincareDivisor.regularDistribution_const_mul
      (LelongPoincareDivisor.haarFactor b : ℝ) hHv hBv).symm
  rw [hdist] at hLP
  rw [reader_restrict, hA]
  have hμ : ddC (regularDistribution b.addHaar (fun y => f y - P.chartH e y)
      (hf.sub hP)) = ddC (regularDistribution (LelongPoincareDivisor.haarFactor b • volume)
        (fun y => f y - P.chartH e y) (hf'.sub hP')) := by
    congr 2
    exact LelongPoincareDivisor.addHaar_eq_smul b
  rw [hμ, hLP]
  change readerLinear (_ + _) = _
  rw [map_add, map_smul]
  change (LelongPoincareDivisor.haarFactor b : ℝ) • complementaryRead (divisorCurrent hG hG0) +
    complementaryRead (ddC (regularDistribution volume B hBv)) = _
  rw [complementaryRead_ddC]

private theorem sg_transport {S T : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hT : IsPositive T) (he : S = T) :
    sgPart hS = sgPart hT := by
  subst T
  rfl

private theorem local_eq_of_singular_smooth_difference
    {C F : LocalProductCurrent (m + 1) U m} (hC : IsPositive C) (hF : IsPositive F)
    (hsC : sgPart hC = C) (hsF : sgPart hF = F)
    {B : ComplexModel (m + 1) → ℝ} (hB : ContDiffOn ℝ ∞ B U)
    (he : C = F + ddc (scalarTopCurrent (regularDistribution volume B
      (hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))))
    {z : ComplexModel (m + 1)} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      let W : Opens (ComplexModel (m + 1)) := ⟨ball z r, isOpen_ball⟩
      ∃ hWU : W ≤ U, restrict hWU C = restrict hWU F := by
  have hsum : IsPositive (F + ddc (scalarTopCurrent (regularDistribution volume B
      (hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)))) := by
    rw [← he]
    exact hC
  obtain ⟨r, hr, hWU, hWsum, hsg, _hac⟩ :=
    exists_local_parts_of_smooth_remainder hF hB hsum hz
  let W : Opens (ComplexModel (m + 1)) := ⟨ball z r, isOpen_ball⟩
  have hBr : restrict hWU (ddc (scalarTopCurrent (regularDistribution volume B
      (hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)))) =
      ddc (scalarTopCurrent (regularDistribution volume B
        ((hB.mono hWU).continuousOn.locallyIntegrableOn W.isOpen.measurableSet))) := by
    rw [ddc_scalarTopCurrent_restrict, restrictDistribution_regularDistribution]
  have hadd (S T : LocalProductCurrent (m + 1) U m) :
      restrict hWU (S + T) = restrict hWU S + restrict hWU T := by ext γ φ; rfl
  have hWr : restrict hWU F + ddc (scalarTopCurrent (regularDistribution volume B
      ((hB.mono hWU).continuousOn.locallyIntegrableOn W.isOpen.measurableSet))) =
      restrict hWU C := by
    rw [he, hadd, hBr]
  have hCW : sgPart (isPositive_restrict hC hWU) = restrict hWU C := by
    rw [← sgPart_restrict hC hWU, hsC]
  have hFW : sgPart (isPositive_restrict hF hWU) = restrict hWU F := by
    rw [← sgPart_restrict hF hWU, hsF]
  have hWsg : sgPart hWsum = restrict hWU C :=
    (sg_transport hWsum (isPositive_restrict hC hWU) hWr).trans hCW
  exact ⟨r, hr, hWU, hWsg.symm.trans (hsg.trans hFW)⟩

/-- A genuine divisor metric internally produces its local generator and
the full normalized metered-current reading on a smaller actual domain. -/
theorem exists_normalized_local_divisor_reading
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (D : EffectiveDivisor (m + 1) M)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hm : DivisorMetric.IsDivisorMetric D E)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ chartTarget e) :
    let C := complementaryRead
      ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
    ∃ (W : Opens (ComplexModel (m + 1))) (hWe : W ≤ chartTarget e), z ∈ W ∧
      ∃ g : M → ℂ,
        let G := fun y => g (e.val.symm y)
        ∃ (hG : DifferentiableOn ℂ G W) (hG0 : ∀ y ∈ W, ∃ᶠ w in 𝓝 y, G w ≠ 0),
          (∀ y ∈ W, ∀ f, D.ideal.mem (e.val.symm y) f ↔
            IsInSpanAt (n := m + 1) (· = g) (e.val.symm y) f) ∧
          restrict hWe C = (LelongPoincareDivisor.haarFactor b : ℝ) •
            complementaryRead (divisorCurrent hG hG0) := by
  obtain ⟨V, hV, hzV, g, hg, hn, hgen, H, hH, he⟩ :=
    metric_generator D E hm (e.val.symm z)
  obtain ⟨P, hzP⟩ := LelongPoincareDivisor.exists_localPresentation E (e.val.symm z)
  let Um : Opens (ComplexModel (m + 1)) :=
    ⟨e.val.target ∩ e.val.symm ⁻¹' V, e.val.isOpen_inter_preimage_symm hV⟩
  let U := P.chartDomain e ⊓ Um
  have hUP : U ≤ P.chartDomain e := inf_le_left
  have hUm : U ≤ Um := inf_le_right
  have hUe : U ≤ chartTarget e := hUP.trans (P.chartDomain_le e)
  have hzU : z ∈ U := ⟨⟨hz, hzP⟩, ⟨hz, hzV⟩⟩
  let G := fun y => g (e.val.symm y)
  have hGU : DifferentiableOn ℂ G U :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg).mono (fun _y hy => hUm hy)
  have hG0U : ∀ y ∈ U, ∃ᶠ w in 𝓝 y, G w ≠ 0 :=
    fun y hy => chart_generator_frequent hV hn e y (hUm hy)
  have hHU : ContDiffOn ℝ ∞ (fun y => H (e.val.symm y)) U :=
    (hH e).mono (fun _y hy => hUm hy)
  have heU : ∀ y ∈ U, chartFunction E.weight e y =
      generatorLog (fun _ : Fin 1 => G) y + (H (e.val.symm y) : EReal) := by
    intro y hy
    exact he (e.val.symm y) (hUm hy).2
  let C := complementaryRead
    ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
  obtain ⟨hC, _hsC, hsC, _haC⟩ := exists_positive_singular_chart_reading b E e
  let F := (LelongPoincareDivisor.haarFactor b : ℝ) • complementaryRead (divisorCurrent hGU hG0U)
  obtain ⟨_hdiff, hGpos, hsG, _hsgG, _hacG⟩ :=
    exists_positive_singular_divisor_reading hGU hG0U
  let hF : IsPositive F := hGpos.smul (LelongPoincareDivisor.haarFactor b).coe_nonneg
  have hsF : hF.traceMeasure ⟂ₘ volume := by
    rw [SourceBedfordTaylorTraceNormalization.traceMeasure_smul hGpos
      (LelongPoincareDivisor.haarFactor b).coe_nonneg]
    exact hsG.smul_nnreal (Real.toNNReal (LelongPoincareDivisor.haarFactor b : ℝ))
  have hsgF : sgPart hF = F :=
    (ofMeasure_congr hF (sgMeasure_le hF) le_rfl
      (Measure.singularPart_eq_self.mpr hsF)).trans (ofMeasure_traceMeasure hF)
  let B := fun y => (LelongPoincareDivisor.haarFactor b : ℝ) *
    (H (e.val.symm y) - P.chartH e y)
  have hB : ContDiffOn ℝ ∞ B U :=
    contDiffOn_const.mul (hHU.sub ((P.contDiffOn_chartH e).mono (fun _y hy => hUP hy)))
  have hflat : restrict hUe C = F + ddc (scalarTopCurrent (regularDistribution volume B
      (hB.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) :=
    metric_current_eq b E e P hUP hGU hG0U hHU heU
  have hsgCU : sgPart (isPositive_restrict hC hUe) = restrict hUe C := by
    rw [← sgPart_restrict hC hUe, hsC]
  obtain ⟨r, hr, hWU, hEq⟩ := local_eq_of_singular_smooth_difference
    (isPositive_restrict hC hUe) hF hsgCU hsgF hB hflat hzU
  let W : Opens (ComplexModel (m + 1)) := ⟨ball z r, isOpen_ball⟩
  let hWe : W ≤ chartTarget e := hWU.trans hUe
  refine ⟨W, hWe, mem_ball_self hr, g, hGU.mono hWU,
    (fun y hy => hG0U y (hWU hy)),
    (fun y hy => hgen (e.val.symm y) (hUm (hWU hy)).2), ?_⟩
  rw [← restrict_twice hUe hWU, hEq]
  change restrict hWU ((LelongPoincareDivisor.haarFactor b : ℝ) •
    complementaryRead (divisorCurrent hGU hG0U)) = _
  have hsmul (a : ℝ) (T : LocalProductCurrent (m + 1) U m) :
      restrict hWU (a • T) = a • restrict hWU T := by ext γ φ; rfl
  rw [hsmul, divisor_reading_restrict]

end SGPT.Foundations.Analysis.Pending.ActualDivisorMetricLocalReading
