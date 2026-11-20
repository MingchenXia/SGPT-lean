import SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityContinuity
import SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity

set_option autoImplicit false

/-! # Actual PSH-generated cutoff weights for bounded mixed products

Genuine PSH seeds may differ from the tuple producing the measures.
Their finite-coordinate Lipschitz classifier internally has boundedness,
quasicontinuity and capacity convergence. Actual mixed weak continuity
and capacity domination produce weighted integrals; no target limit
or measure-control certificate is a caller premise.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedPshCutoffWeightedConvergence

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar ThetaCapacity
  CapacityWeightedConvergence PoleCoalescingCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
private theorem classifier_capacity {m : ℕ} {f : ℕ → Fin m → M → ℝ}
    {g : Fin m → M → ℝ} {Φ : (Fin m → ℝ) → ℝ} {L : NNReal}
    (hΦ : LipschitzWith L Φ) (omega : KahlerBackground n M)
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |f j i x - g i x|}) atTop (𝓝 0)) :
    ∀ a : ℝ, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |Φ (fun i => f j i x) - Φ (fun i => g i x)|}) atTop (𝓝 0) := by
  classical
  intro a ha
  let b : ℝ := a / (L + 1)
  have hb : 0 < b := div_pos ha (by positivity)
  let E : ℕ → Fin m → Set M := fun j i => {x | b < |f j i x - g i x|}
  have hsum : Tendsto (fun j => ∑ i : Fin m, thetaCapacity omega.form (fun _ => 0) (E j i))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun i _ => hcap i b hb)
  have hbound (j : ℕ) : thetaCapacity omega.form (fun _ => 0)
      {x | a < |Φ (fun i => f j i x) - Φ (fun i => g i x)|} ≤
      ∑ i : Fin m, thetaCapacity omega.form (fun _ => 0) (E j i) := by
    refine (thetaCapacity_mono ?_).trans
      (by simpa only [tsum_fintype] using thetaCapacity_iUnion_le omega.form (fun _ => 0) (E j))
    intro x hx
    by_contra hn
    have hcoord : ∀ i, dist (f j i x) (g i x) ≤ b := by
      intro i
      rw [Real.dist_eq]
      exact not_lt.mp (fun hh => hn (mem_iUnion.mpr ⟨i, hh⟩))
    have hvect : dist (fun i => f j i x) (fun i => g i x) ≤ b :=
      (dist_pi_le_iff hb.le).mpr hcoord
    have hd : |Φ (fun i => f j i x) - Φ (fun i => g i x)| ≤ (L : ℝ) * b := by
      rw [← Real.dist_eq]
      exact (hΦ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hvect L.coe_nonneg)
    have hba : (L : ℝ) * b < a := by
      have he : b * ((L : ℝ) + 1) = a := div_mul_cancel₀ _ (by positivity)
      nlinarith
    exact (not_lt_of_ge (hd.trans hba.le)) hx
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hbound

omit [BorelSpace M] in
private theorem classifier_quasicontinuous {m : ℕ} {g : Fin m → M → ℝ}
    {Φ : (Fin m → ℝ) → ℝ} (hΦ : Continuous Φ) (omega : KahlerBackground n M)
    (hg : ∀ i, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (g i)) :
    QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0))
      (fun x => Φ (fun i => g i x)) := by
  classical
  intro η hη
  obtain ⟨r, _hr0, hr, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  let b : ℝ := r / (m + 1)
  have hb : 0 < b := div_pos hrpos (by positivity)
  choose G hGo hGc hGcont using fun i => hg i (ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr hb)
  have hsum : (∑ i : Fin m, ENNReal.ofReal b) = ENNReal.ofReal ((m : ℝ) * b) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
  have hbr : (m : ℝ) * b < r := by
    have he : b * ((m : ℝ) + 1) = r := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hGcap : thetaCapacity omega.form (fun _ => 0) (⋃ i, G i) < η := by
    have hle : thetaCapacity omega.form (fun _ => 0) (⋃ i, G i) ≤
        ENNReal.ofReal ((m : ℝ) * b) := by
      refine (thetaCapacity_iUnion_le _ _ G).trans ?_
      rw [tsum_fintype, ← hsum]
      exact Finset.sum_le_sum fun i _ => (hGc i).le
    exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hbr |>.trans hrη)
  refine ⟨⋃ i, G i, isOpen_iUnion hGo, hGcap, ?_⟩
  apply hΦ.comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (hGcont i).mono (fun x hx hi => hx (mem_iUnion.mpr ⟨i, hi⟩))

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
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

/-- Actual bounded mixed measures and independent genuine PSH seeds produce
weighted limits for any fixed finite-coordinate Lipschitz cutoff classifier. -/
theorem tendsto_integral_classifier_of_capacity (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {p : ℕ → Fin n → M → EReal} {q : Fin n → M → EReal}
    (hp : ∀ j i, IsThetaPshPotential (θ i).val (p j i))
    (hq : ∀ i, IsThetaPshPotential (θ i).val (q i))
    {B : ℝ} (hB : 0 ≤ B)
    (hpB : ∀ j i x, ((-B : ℝ) : EReal) ≤ p j i x ∧ p j i x ≤ (B : EReal))
    (hqB : ∀ i x, ((-B : ℝ) : EReal) ≤ q i x ∧ q i x ≤ (B : EReal))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(p j i x).toReal - (q i x).toReal|}) atTop (𝓝 0))
    {m : ℕ} {w : ℕ → Fin m → M → EReal} {v : Fin m → M → EReal}
    (hw : ∀ j i, IsThetaPshPotential omega.form.val (w j i))
    (hv : ∀ i, IsThetaPshPotential omega.form.val (v i))
    (hwB : ∀ j i x, (-1 : EReal) ≤ w j i x ∧ w j i x ≤ 0)
    (hvB : ∀ i x, (-1 : EReal) ≤ v i x ∧ v i x ≤ 0)
    (hseedcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | a < |(w j i x).toReal - (v i x).toReal|}) atTop (𝓝 0))
    {Φ : (Fin m → ℝ) → ℝ} {L : NNReal} (hΦ : LipschitzWith L Φ)
    (h : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, h x * Φ (fun i => (w j i x).toReal)
      ∂globalMixedMeasure θ (p j) (fun i => (hp j i).1)) atTop
      (𝓝 (∫ x, h x * Φ (fun i => (v i x).toReal)
        ∂globalMixedMeasure θ q (fun i => (hq i).1))) := by
  let μ : ℕ → Measure M := fun j => globalMixedMeasure θ (p j) (fun i => (hp j i).1)
  let ν : Measure M := globalMixedMeasure θ q (fun i => (hq i).1)
  let _ : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let _ : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  have hweak : ∀ h : C(M, ℝ), Tendsto (fun j => ∫ x, h x ∂μ j) atTop
      (𝓝 (∫ x, h x ∂ν)) := fun h =>
    ActualBoundedMixedCapacityContinuity.tendsto_integral_continuous_of_capacity
      omega hp hq hB hpB hqB hcap h
  obtain ⟨K, _hK, hdom⟩ :=
    ActualBoundedMixedCapacityDomination.exists_uniform_capacity_bound omega θ B hB
  have hmod : Tendsto (fun a : ENNReal => ENNReal.ofReal K * a) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using ENNReal.Tendsto.const_mul
      (tendsto_id : Tendsto (fun a : ENNReal => a) (𝓝 0) (𝓝 0))
      (Or.inr ENNReal.ofReal_ne_top)
  have hcontrol : UniformCapacityControl (thetaCapacity omega.form (fun _ => 0)) μ ν :=
    uniformCapacityControl_of_modulus hmod (fun j E _ => hdom (p j) (hp j) (hpB j) E)
      (fun E _ => hdom q hq hqB E)
  have hmember (a : Fin m → M → EReal)
      (ha : ∀ i x, (-1 : EReal) ≤ a i x ∧ a i x ≤ 0) (x : M) :
      (fun i => (a i x).toReal) ∈ closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall]
    apply (dist_pi_le_iff zero_le_one).mpr
    intro i
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using abs_toReal_le_one (ha i x)
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : Fin m → ℝ) 1).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  let C : ℝ := max D 0
  have hC : 0 ≤ C := le_max_right _ _
  have hweightBound (a : Fin m → M → EReal)
      (ha : ∀ i x, (-1 : EReal) ≤ a i x ∧ a i x ≤ 0) (x : M) :
      |Φ (fun i => (a i x).toReal)| ≤ C := by
    have hh := hD _ (hmember a ha x)
    simpa only [Real.norm_eq_abs] using hh.trans (le_max_left D 0)
  have hwm : ∀ j, Measurable (fun x => Φ (fun i => (w j i x).toReal)) := fun j =>
    hΦ.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
      (hw j i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable.ereal_toReal)
  have hvm : Measurable (fun x => Φ (fun i => (v i x).toReal)) :=
    hΦ.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
      (hv i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable.ereal_toReal)
  have hqc : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0))
      (fun x => Φ (fun i => (v i x).toReal)) :=
    classifier_quasicontinuous hΦ.continuous omega (fun i =>
      quasiContinuousFor_toReal_of_le_zero omega omega.isSemipositive (hv i)
        (fun x => (hvB i x).2))
  exact tendsto_integral_mul_of_capacity hcontrol hweak hwm hvm hqc hC
    (fun j => hweightBound (w j) (hwB j)) (hweightBound v hvB)
    (classifier_capacity hΦ omega hseedcap) h

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedPshCutoffWeightedConvergence
