import SGPT.Foundations.Analysis.Pending.ActualBoundedPshCutoffWeightedConvergence
import SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousBorelRepresentative
import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityZeroNull

set_option autoImplicit false

/-! # Arbitrary bounded quasicontinuous multipliers of actual cutoff weights

The original weight need not be Borel. Its actual representative and actual
NP capacity-null transfer, bounded measure control and continuous-cutoff
weighted limits are internally produced from the natural function data.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedQuasiContinuousCutoffWeightedConvergence

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar ThetaCapacity
  CapacityWeightedConvergence PluripolarCapacityZero

noncomputable section

section WeightedApproximation

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormalSpace X]

private theorem tendsto_multiplier
    {cap : Set X → ℝ≥0∞} {μ : ℕ → Measure X} {ν : Measure X}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hcontrol : UniformCapacityControl cap μ ν)
    {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ j, Measurable (a j)) (hb : Measurable b)
    {R : ℝ} (hR : 0 ≤ R) (haR : ∀ j x, |a j x| ≤ R) (hbR : ∀ x, |b x| ≤ R)
    (hcontinuous : ∀ v : C(X, ℝ), Tendsto (fun j => ∫ x, v x * a j x ∂μ j)
      atTop (𝓝 (∫ x, v x * b x ∂ν)))
    {χ : X → ℝ} (hχ : Measurable χ) (hquasi : QuasiContinuousFor cap χ)
    {B : ℝ} (hB : 0 ≤ B) (hχB : ∀ x, |χ x| ≤ B) :
    Tendsto (fun j => ∫ x, χ x * a j x ∂μ j) atTop (𝓝 (∫ x, χ x * b x ∂ν)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  let r : ℝ := eps / (8 * (B * R + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨eta, heta, hsmall⟩ := hcontrol r hr
  obtain ⟨G, hG, hGcap, hχG⟩ := hquasi eta heta
  obtain ⟨v, hvB, heq⟩ := exists_continuous_eqOn_compl hB hχB hG hχG
  obtain ⟨hmG, hnG⟩ := hsmall G hG.measurableSet hGcap
  have hmGr : ∀ j, (μ j).real G ≤ r := fun j =>
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmG j)).trans_eq (ENNReal.toReal_ofReal hr.le)
  have hnGr : ν.real G ≤ r :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnG).trans_eq (ENNReal.toReal_ofReal hr.le)
  have hrmul : r * (8 * (B * R + 1)) = eps := by
    dsimp [r]
    exact div_mul_cancel₀ _ (by positivity)
  have herr : 2 * (B * R) * r < eps / 4 := by nlinarith [mul_nonneg hB hR]
  have hmerr : ∀ j, |(∫ x, χ x * a j x ∂μ j) - ∫ x, v x * a j x ∂μ j| < eps / 4 := by
    intro j
    have hh := abs_integral_sub_le_of_eqOn_compl (mu := μ j) (G := G) (hχ.mul (ha j)) (v.continuous.measurable.mul (ha j))
      (mul_nonneg hB hR)
      (fun x => by rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hχB x) (haR j x) (abs_nonneg _) hB)
      (fun x => by rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hvB x) (haR j x) (abs_nonneg _) hB)
      (fun x hx => by simp only [Pi.mul_apply, heq hx])
    exact hh.trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hmGr j) (by positivity)) herr)
  have hnerr : |(∫ x, χ x * b x ∂ν) - ∫ x, v x * b x ∂ν| < eps / 4 := by
    have hh := abs_integral_sub_le_of_eqOn_compl (mu := ν) (G := G) (hχ.mul hb) (v.continuous.measurable.mul hb)
      (mul_nonneg hB hR)
      (fun x => by rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hχB x) (hbR x) (abs_nonneg _) hB)
      (fun x => by rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hvB x) (hbR x) (abs_nonneg _) hB)
      (fun x hx => by simp only [Pi.mul_apply, heq hx])
    exact hh.trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnGr (by positivity)) herr)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hcontinuous v) (eps / 2) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have hvlim := hN j hj
  rw [Real.dist_eq] at hvlim ⊢
  have htri := abs_add_three
    ((∫ x, χ x * a j x ∂μ j) - ∫ x, v x * a j x ∂μ j)
    ((∫ x, v x * a j x ∂μ j) - ∫ x, v x * b x ∂ν)
    ((∫ x, v x * b x ∂ν) - ∫ x, χ x * b x ∂ν)
  have hid : ((∫ x, χ x * a j x ∂μ j) - ∫ x, v x * a j x ∂μ j) +
      ((∫ x, v x * a j x ∂μ j) - ∫ x, v x * b x ∂ν) +
      ((∫ x, v x * b x ∂ν) - ∫ x, χ x * b x ∂ν) =
      (∫ x, χ x * a j x ∂μ j) - ∫ x, χ x * b x ∂ν := by ring
  rw [hid, abs_sub_comm (∫ x, v x * b x ∂ν) (∫ x, χ x * b x ∂ν)] at htri
  linarith [hmerr j]

end WeightedApproximation

private theorem abs_toReal_le_one {a : EReal} (ha : (-1 : EReal) ≤ a ∧ a ≤ 0) :
    |a.toReal| ≤ 1 := by
  have hb : a ≠ ⊥ := (lt_of_lt_of_le (EReal.bot_lt_coe (-1)) ha.1).ne'
  have ht : a ≠ ⊤ := (lt_of_le_of_lt ha.2 (EReal.coe_lt_top 0)).ne
  apply abs_le.mpr
  constructor
  · have hh := EReal.toReal_le_toReal ha.1 (EReal.coe_ne_bot (-1)) ht
    norm_num at hh
    exact hh
  · have hz : a.toReal ≤ 0 := by
      simpa only [EReal.toReal_zero] using EReal.toReal_le_toReal ha.2 hb EReal.zero_ne_top
    exact hz.trans zero_le_one

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Original bounded quasicontinuous weights, without a measurability premise,
multiply genuine PSH cutoff classifiers in actual bounded mixed limits. -/
theorem tendsto_integral_classifier_mul_quasiContinuous (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {p : ℕ → Fin n → M → EReal} {q : Fin n → M → EReal}
    (hp : ∀ j i, IsThetaPshPotential (θ i).val (p j i))
    (hq : ∀ i, IsThetaPshPotential (θ i).val (q i))
    {B : ℝ} (hB : 0 ≤ B)
    (hpB : ∀ j i x, ((-B : ℝ) : EReal) ≤ p j i x ∧ p j i x ≤ (B : EReal))
    (hqB : ∀ i x, ((-B : ℝ) : EReal) ≤ q i x ∧ q i x ≤ (B : EReal))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(p j i x).toReal - (q i x).toReal|}) atTop (𝓝 0))
    {m : ℕ} {w : ℕ → Fin m → M → EReal} {z : Fin m → M → EReal}
    (hw : ∀ j i, IsThetaPshPotential omega.form.val (w j i))
    (hz : ∀ i, IsThetaPshPotential omega.form.val (z i))
    (hwB : ∀ j i x, (-1 : EReal) ≤ w j i x ∧ w j i x ≤ 0)
    (hzB : ∀ i x, (-1 : EReal) ≤ z i x ∧ z i x ≤ 0)
    (hseedcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(w j i x).toReal - (z i x).toReal|}) atTop (𝓝 0))
    {Φ : (Fin m → ℝ) → ℝ} {L : NNReal} (hΦ : LipschitzWith L Φ)
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, |χ x| ≤ C)
    (hχ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ)
    (h : C(M, ℝ)) :
    (∀ j, Integrable (fun x => χ x * h x * Φ (fun i => (w j i x).toReal))
      (globalMixedMeasure θ (p j) (fun i => (hp j i).1))) ∧
    Integrable (fun x => χ x * h x * Φ (fun i => (z i x).toReal))
      (globalMixedMeasure θ q (fun i => (hq i).1)) ∧
    Tendsto (fun j => ∫ x, χ x * h x * Φ (fun i => (w j i x).toReal)
      ∂globalMixedMeasure θ (p j) (fun i => (hp j i).1)) atTop
      (𝓝 (∫ x, χ x * h x * Φ (fun i => (z i x).toReal)
        ∂globalMixedMeasure θ q (fun i => (hq i).1))) := by
  classical
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  let μ : ℕ → Measure M := fun j => globalMixedMeasure θ (p j) (fun i => (hp j i).1)
  let ν : Measure M := globalMixedMeasure θ q (fun i => (hq i).1)
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  obtain ⟨g, hgm, hgC, hgQC, E, _hEm, hEo, heq⟩ :=
    ActualQuasiContinuousBorelRepresentative.exists_borel_representative omega hC hχC hχ
  have hEcap : thetaCapacity omega.form (fun _ => 0) E = 0 := by
    refine le_antisymm (le_of_forall_gt fun eta heta => ?_) zero_le
    obtain ⟨G, _hGo, hEG, hGcap⟩ := hEo eta heta
    exact (thetaCapacity_mono hEG).trans_lt hGcap
  have hsame (r : Fin n → M → EReal) (hr : ∀ i, IsThetaPshPotential (θ i).val (r i)) :
      χ =ᵐ[globalMixedMeasure θ r (fun i => (hr i).1)] g := by
    apply ae_iff.mpr
    apply measure_mono_null _ (ActualMixedCapacityZeroNull.globalMixedMeasure_eq_zero_of_capacity_eq_zero
      omega hr hEcap)
    intro x hx
    by_contra hxE
    exact hx (heq hxE)
  have hmember (a : Fin m → M → EReal)
      (ha : ∀ i x, (-1 : EReal) ≤ a i x ∧ a i x ≤ 0) (x : M) :
      (fun i => (a i x).toReal) ∈ closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall]
    apply (dist_pi_le_iff zero_le_one).mpr
    intro i
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using abs_toReal_le_one (ha i x)
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : Fin m → ℝ) 1).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous.continuousOn
  let R : ℝ := max H 0 * max D 0
  have hR : 0 ≤ R := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hbound (a : Fin m → M → EReal)
      (ha : ∀ i x, (-1 : EReal) ≤ a i x ∧ a i x ≤ 0) (x : M) :
      |h x * Φ (fun i => (a i x).toReal)| ≤ R := by
    rw [abs_mul]
    have hh : |h x| ≤ max H 0 := by
      simpa only [Real.norm_eq_abs] using (hH x (mem_univ x)).trans (le_max_left H 0)
    have hφ : |Φ (fun i => (a i x).toReal)| ≤ max D 0 := by
      simpa only [Real.norm_eq_abs] using (hD _ (hmember a ha x)).trans (le_max_left D 0)
    exact mul_le_mul hh hφ (abs_nonneg _) (le_max_right _ _)
  let a : ℕ → M → ℝ := fun j x => h x * Φ (fun i => (w j i x).toReal)
  let b : M → ℝ := fun x => h x * Φ (fun i => (z i x).toReal)
  have ha : ∀ j, Measurable (a j) := fun j => h.continuous.measurable.mul
    (hΦ.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
      (hw j i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable.ereal_toReal))
  have hb : Measurable b := h.continuous.measurable.mul
    (hΦ.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
      (hz i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable.ereal_toReal))
  have haR : ∀ j x, |a j x| ≤ R := fun j => hbound (w j) (hwB j)
  have hbR : ∀ x, |b x| ≤ R := hbound z hzB
  obtain ⟨K, _hK, hdom⟩ :=
    ActualBoundedMixedCapacityDomination.exists_uniform_capacity_bound omega θ B hB
  have hmod : Tendsto (fun t : ENNReal => ENNReal.ofReal K * t) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using ENNReal.Tendsto.const_mul
      (tendsto_id : Tendsto (fun t : ENNReal => t) (𝓝 0) (𝓝 0)) (Or.inr ENNReal.ofReal_ne_top)
  have hcontrol : UniformCapacityControl (thetaCapacity omega.form (fun _ => 0)) μ ν :=
    uniformCapacityControl_of_modulus hmod (fun j F _ => hdom (p j) (hp j) (hpB j) F)
      (fun F _ => hdom q hq hqB F)
  have hcontinuous : ∀ v : C(M, ℝ), Tendsto (fun j => ∫ x, v x * a j x ∂μ j)
      atTop (𝓝 (∫ x, v x * b x ∂ν)) := by
    intro v
    simpa only [μ, ν, a, b, ContinuousMap.mul_apply, mul_assoc] using
      ActualBoundedPshCutoffWeightedConvergence.tendsto_integral_classifier_of_capacity
        omega hp hq hB hpB hqB hcap hw hz hwB hzB hseedcap hΦ (v * h)
  have hlim := tendsto_multiplier hcontrol ha hb hR haR hbR hcontinuous hgm hgQC hC hgC
  have hμae (j : ℕ) : (fun x => χ x * a j x) =ᵐ[μ j] (fun x => g x * a j x) := by
    filter_upwards [hsame (p j) (hp j)] with x hx
    rw [hx]
  have hνae : (fun x => χ x * b x) =ᵐ[ν] (fun x => g x * b x) := by
    filter_upwards [hsame q hq] with x hx
    rw [hx]
  have hiμ : ∀ j, Integrable (fun x => χ x * a j x) (μ j) := fun j =>
    (integrable_of_bounded (B := C * R) (hgm.mul (ha j)) (fun x => by
      rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hgC x) (haR j x) (abs_nonneg _) hC)).congr (hμae j).symm
  have hiν : Integrable (fun x => χ x * b x) ν :=
    (integrable_of_bounded (B := C * R) (hgm.mul hb) (fun x => by
      rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hgC x) (hbR x) (abs_nonneg _) hC)).congr hνae.symm
  have hlimχ : Tendsto (fun j => ∫ x, χ x * a j x ∂μ j) atTop
      (𝓝 (∫ x, χ x * b x ∂ν)) := by
    rw [integral_congr_ae hνae]
    exact hlim.congr (fun j => (integral_congr_ae (hμae j)).symm)
  simpa only [μ, ν, a, b, mul_assoc] using And.intro hiμ (And.intro hiν hlimχ)

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedQuasiContinuousCutoffWeightedConvergence
