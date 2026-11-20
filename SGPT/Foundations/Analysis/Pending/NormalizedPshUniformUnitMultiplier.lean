import SGPT.Foundations.Analysis.Pending.NormalizedPshChartLogarithmicBound
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.POrderAffineRooftop
import SGPT.Foundations.Analysis.Pending.IEnvelopeCompetitors

set_option autoImplicit false

/-! # Uniform actual unit multiplier germs from normalized PSH geometry -/

open Metric Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NormalizedPshUniformUnitMultiplier
open FirstPass FirstPass.HolomorphicIdealSheaves ThetaPshUniformL1Bound
  BergmanSupWeight

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  {θ : SmoothRealForm n M 2}

/-- A uniform positive range of actual unit multiplier germs on the inner chart
is produced from normalized PSH data and the true Bergman/Skoda estimate. -/
theorem exists_small_level_one_mem_on_inner_chart (hn : 0 < n)
    (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) (c : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ d : ℝ, 0 < d → d ≤ a → ∀ u : M → EReal,
      ThetaPlurisubharmonic θ u → (∀ y, u y ≤ 0) →
      (∃ y₀, ((-c : ℝ) : EReal) ≤ u y₀) →
      ∀ x ∈ H.e.val.source, H.e.val x ∈ ball H.z (H.r / 4) →
        (multiplierIdeal (n := n) d u).mem x (fun _ => (1 : ℂ)) := by
  classical
  obtain ⟨K, hK⟩ := NormalizedPshChartLogarithmicBound.exists_uniform_log_exponent_bound hn hθ H c
  have hden : 0 < max K 0 + 1 := by linarith [le_max_right K 0]
  refine ⟨1 / (max K 0 + 1), one_div_pos.mpr hden,
    fun d hd hda u hu hle hex x hxs hxinner => ?_⟩
  have hKd : K < 2 / d := by
    have hmul : d * (max K 0 + 1) ≤ 1 := (le_div_iff₀ hden).mp hda
    have hleK : K ≤ max K 0 := le_max_left K 0
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  by_contra hnotone
  have hxzero : x ∈ (multiplierIdeal (n := n) d u).zeroLocus := by
    by_contra hnotzero
    exact hnotone (SkodaIntegrability.one_mem_multiplierIdeal_of_notMem_zeroLocus hnotzero)
  let p : ComplexModel n := H.e.val x
  have hpinner : p ∈ ball H.z (H.r / 4) := hxinner
  have hpdist : dist p H.z < H.r / 4 := mem_ball.mp hpinner
  have hpW : p ∈ H.W := H.ball_subset_W (mem_ball.mpr (by linarith [H.r_pos]))
  have hclosed : closedBall p H.r ⊆ H.W := by
    intro z hz
    apply H.closedBall_subset
    apply mem_closedBall.mpr
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle z p H.z
    linarith [H.r_pos]
  let Φ : ComplexModel n → EReal := H.corrected u
  let Ψ : ComplexModel n → EReal := fun z => (d : EReal) * Φ z
  have hΦ : PlurisubharmonicOn Φ H.W :=
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hu H.e H.potential
  have hΨ : PlurisubharmonicOn Ψ H.W := hΦ.const_mul hd
  have hweight : AEMeasurable (fun z => multiplierWeight d (Φ z))
      (volume.restrict (ball p H.r)) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((hΦ.mono (ball_subset_closedBall.trans hclosed)).upperSemicontinuousOn) hd.ne'
  have hvan : ∀ f ∈ bergmanBall (ball p H.r) (fun z => multiplierWeight 1 (Ψ z)), f p = 0 := by
    intro f hf
    have hint : ∫⁻ z in ball p H.r, multiplierDensity Φ d f z ∂volume ≤ 1 := by
      have h := hf.2
      simp only [Ψ, SkodaIntegrability.multiplierWeight_one_mul] at h
      exact h
    have hG : MultiplierIntegrableAt Φ d f p volume := by
      refine ⟨hd, ball p H.r, isOpen_ball, mem_ball_self H.r_pos, hf.1, ?_,
        hint.trans_lt ENNReal.one_lt_top⟩
      exact ((ENNReal.continuous_ofReal.comp_continuousOn
        (hf.1.continuousOn.norm.pow 2)).aemeasurable isOpen_ball.measurableSet).mul hweight
    have hmem := DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hu hd H.e
      H.potential.1 H.potential.2.2.1.continuousOn hxs hpW hG
    exact hxzero _ hmem
  obtain ⟨r, C, hr, hbound⟩ := SkodaIntegrability.exists_log_bound_of_forall_bergmanBall_vanish
    hΨ H.r_pos hclosed hvan
  have hadm : ∀ z : ComplexModel n, 0 < ‖z - p‖ → ‖z - p‖ < r →
      H.corrected u z ≤ (((2 / d) * Real.log ‖z - p‖ + C / d : ℝ) : EReal) := by
    intro z hzpos hzlt
    have hzneq : z ≠ p := sub_ne_zero.mp (norm_pos_iff.mp hzpos)
    have hzbound := hbound z (mem_ball_iff_norm.mpr hzlt) hzneq
    change (d : EReal) * H.corrected u z ≤ _ at hzbound
    induction hv : H.corrected u z using EReal.rec with
    | bot => exact bot_le
    | top =>
        rw [hv, EReal.coe_mul_top_of_pos hd] at hzbound
        exact False.elim (EReal.coe_ne_top _ (top_le_iff.mp hzbound))
    | coe t =>
        rw [hv, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hzbound
        rw [EReal.coe_le_coe_iff]
        have ht : t ≤ (2 * Real.log ‖z - p‖ + C) / d := by
          apply (le_div_iff₀ hd).mpr
          nlinarith [hzbound]
        have heq : (2 * Real.log ‖z - p‖ + C) / d =
            (2 / d) * Real.log ‖z - p‖ + C / d := by ring
        exact heq ▸ ht
  exact hKd.not_ge (hK u hu hle hex p hpinner (2 / d) (C / d) r hr hadm)

/-- An actual finite inner-chart cover produces one positive multiplier level
whose unit germ is present at every point for every normalized PSH potential. -/
theorem exists_uniform_small_level_one_mem (hn : 0 < n)
    (hθ : HasSmoothLocalPotentials θ) (c : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ u : M → EReal, ThetaPlurisubharmonic θ u →
      (∀ y, u y ≤ 0) → (∃ y₀, ((-c : ℝ) : EReal) ≤ u y₀) →
      ∀ x : M, (multiplierIdeal (n := n) a u).mem x (fun _ => (1 : ℂ)) := by
  classical
  have hex : ∀ x : M, ∃ Hx : HarnackBall θ,
      Hx.e = complexChartAt (n := n) x ∧
      Hx.z = (complexChartAt (n := n) x).val x ∧ Hx.r < 1 := fun x =>
    exists_harnackBall hθ _ ((complexChartAt (n := n) x).val.map_source
      (mem_complexChartAt_source x)) one_pos
  choose Hx hHxe hHxz _ using hex
  let D : M → Set M := fun x => (Hx x).e.val.source ∩
    (Hx x).e.val ⁻¹' ball (Hx x).z ((Hx x).r / 4)
  have hDopen : ∀ x, IsOpen (D x) := fun x =>
    (Hx x).e.val.continuousOn.isOpen_inter_preimage (Hx x).e.val.open_source isOpen_ball
  have hmem : ∀ x, x ∈ D x := by
    intro x
    refine ⟨by rw [hHxe]; exact mem_complexChartAt_source x, ?_⟩
    rw [mem_preimage, hHxe, ← hHxz]
    exact mem_ball_self (by linarith [(Hx x).r_pos])
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover D hDopen
    (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  choose a ha hlocal using fun x => exists_small_level_one_mem_on_inner_chart hn hθ (Hx x) c
  let S : ℝ := ∑ i ∈ s, 1 / a i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (ha i)).le
  have hden : 0 < S + 1 := by linarith
  refine ⟨1 / (S + 1), one_div_pos.mpr hden, fun u hu hle hnorm x => ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hsingle : 1 / a i ≤ S :=
    Finset.single_le_sum (fun j _ => (one_div_pos.mpr (ha j)).le) hi
  have hlevel : 1 / (S + 1) ≤ a i := by
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hsingle (ha i).le
    have hcancel : a i * (1 / a i) = 1 := by
      rw [mul_one_div, div_self (ha i).ne']
    rw [hcancel] at hmul
    nlinarith [ha i]
  exact hlocal i (1 / (S + 1)) (one_div_pos.mpr hden) hlevel u hu hle hnorm x hxi.1 hxi.2

/-- Genuine compact PSH potentials attain finite maxima.  Actual finite
translation therefore removes normalization from the common small unit level. -/
theorem exists_uniform_small_level_one_mem_of_genuine (hn : 0 < n)
    (hθ : HasSmoothLocalPotentials θ) :
    ∃ a : ℝ, 0 < a ∧ ∀ u : M → EReal, IsThetaPshPotential θ u →
      ∀ x : M, (multiplierIdeal (n := n) a u).mem x (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hsmall⟩ := exists_uniform_small_level_one_mem hn hθ 0
  refine ⟨a, ha, fun u hu x => ?_⟩
  obtain ⟨y, m, hym, hmax⟩ := hu.exists_max
  have hnorm : ∀ z, u z - (m : EReal) ≤ 0 := by
    intro z
    have h := add_le_add (hmax z) (le_refl ((-m : ℝ) : EReal))
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add,
      add_neg_cancel, EReal.coe_zero] using h
  have hyzero : u y - (m : EReal) = 0 := by
    rw [hym, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  have hmem := hsmall (fun z => u z - (m : EReal)) (hu.sub_const m).1 hnorm
    ⟨y, by simpa only [neg_zero, EReal.coe_zero, hyzero] using (le_refl (0 : EReal))⟩ x
  obtain ⟨ha', U, hU, hxU, hhol, hint⟩ := hmem.2
  refine ⟨hmem.1, ha', U, hU, hxU, hhol, ?_⟩
  exact (weightedL2On_sub_const_iff m).mp hint

end
end SGPT.Foundations.Analysis.Pending.NormalizedPshUniformUnitMultiplier
