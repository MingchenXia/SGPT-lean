import SGPT.Okounkov.SourceSliceAllDimensions
import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.TranscendentalSliceValuation
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceCurrentValuation
open Set Filter
open scoped Topology Pointwise NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody

/-- Larger nonnegative multiples of the SAME upper-bounded potential are
more singular; the zero coefficient and poles are retained. -/
theorem singularityLE_smul_of_le {X : Type*} {v : X → EReal} {B c q : ℝ}
    (hv : ∀ x, v x ≤ (B : EReal)) (hc : 0 ≤ c) (hcq : c ≤ q) :
    SingularityLE (fun x => (q : EReal) * v x) (fun x => (c : EReal) * v x) := by
  refine (singularityLE_iff_exists_real _ _).mpr ⟨(q - c) * B, fun x => ?_⟩
  have hq : 0 ≤ q := hc.trans hcq
  generalize hval : v x = a at *
  induction a using EReal.rec with
  | bot =>
      by_cases hc0 : c = 0
      · subst c
        by_cases hq0 : q = 0
        · subst q; simp
        · rw [EReal.coe_mul_bot_of_pos (lt_of_le_of_ne hq (Ne.symm hq0))]
          exact bot_le
      · rw [EReal.coe_mul_bot_of_pos (lt_of_le_of_ne hc (Ne.symm hc0)),
          EReal.coe_mul_bot_of_pos (lt_of_lt_of_le (lt_of_le_of_ne hc (Ne.symm hc0)) hcq)]
        simp
  | top => exact False.elim ((not_le_of_gt (EReal.coe_lt_top B)) (by simpa only [hval] using hv x))
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have ha : a ≤ B := EReal.coe_le_coe_iff.mp (by simpa only [hval] using hv x)
      nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hcq)]

/-- Internal rational points approach an arbitrary unchanged real coefficient
from above, staying inside a prescribed positive tolerance. -/
theorem exists_rat_above_tendsto (c δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ℕ → ℚ, (∀ j, c < (q j : ℝ) ∧ (q j : ℝ) < c + δ) ∧
      Tendsto (fun j => (q j : ℝ)) atTop (𝓝 c) := by
  have hchoose (j : ℕ) : ∃ q : ℚ,
      c < (q : ℝ) ∧ (q : ℝ) < c + min δ (1 / (j + 1 : ℝ)) := by
    apply exists_rat_btwn
    have hpos : (0 : ℝ) < 1 / (j + 1 : ℝ) := by positivity
    exact lt_add_of_pos_right c (lt_min hδ hpos)
  choose q hq using hchoose
  refine ⟨q, fun j => ⟨(hq j).1, by linarith [(hq j).2, min_le_left δ (1 / (j + 1 : ℝ))]⟩, ?_⟩
  have hlim : Tendsto (fun j => (q j : ℝ) - c) atTop (𝓝 0) :=
    squeeze_zero (fun j => sub_nonneg.mpr (hq j).1.le)
      (fun j => by linarith [min_le_right δ (1 / (j + 1 : ℝ)), (hq j).2])
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [zero_add, sub_add_cancel] using hlim.add_const c

/-- A REAL multiple of the actual unit divisor valuation belongs to the
actual body of that SAME real divisor current. Rationality is internal only. -/
theorem smul_flagValuation_mem_generalPartialBody_weight {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {c : ℝ} (hc : 0 ≤ c) :
    c • flagValuation F E.weight ∈ generalPartialBody F (c • E.curvature)
      (fun x => (c : EReal) * E.weight x) := by
  have hweight := TranscendentalSlice.weight_mem_analyticCurrents hE
  have hcu := isThetaPshPotential_nonneg_smul hweight.1 hc
  rw [generalPartialBody_eq_iInter_pos hcu, mem_iInter₂]
  intro ε hε
  have hKcu := isKahlerCurrentPotential_add_smul hcu F.omega hε
  obtain ⟨C, hC, hdom⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul F.omega (-E.curvature)
  obtain ⟨B, hB⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hweight.1
  obtain ⟨q, hq, hqt⟩ := exists_rat_above_tendsto c (ε / (2 * (C + 1))) (by positivity)
  have hmem (j : ℕ) : (q j : ℝ) • flagValuation F E.weight ∈
      kahlerPartialBody F (c • E.curvature + ε • F.omega.form)
        (fun x => (c : EReal) * E.weight x) := by
    have hqpos : (0 : ℝ) < q j := hc.trans_lt (hq j).1
    have hqQ : (0 : ℚ) < q j := by exact_mod_cast hqpos
    have hqu := isThetaPshPotential_nonneg_smul hweight.1 hqpos.le
    have hKqu := isKahlerCurrentPotential_add_smul hqu F.omega (half_pos hε)
    have hsmall : ((q j : ℝ) - c) * C ≤ ε / 2 := by
      have hδ : 0 < 2 * (C + 1) := by positivity
      have hb := (lt_div_iff₀ hδ).mp (by linarith [(hq j).2] :
        (q j : ℝ) - c < ε / (2 * (C + 1)))
      nlinarith [(hq j).1]
    have hsemi : (c • E.curvature + ε • F.omega.form -
        ((q j : ℝ) • E.curvature + (ε / 2) • F.omega.form)).val.IsSemipositive := by
      have heq : c • E.curvature + ε • F.omega.form -
          ((q j : ℝ) • E.curvature + (ε / 2) • F.omega.form) =
          ((q j : ℝ) - c) • (-E.curvature + C • F.omega.form) +
            (ε / 2 - ((q j : ℝ) - c) * C) • F.omega.form := by module
      rw [heq]
      intro e z hz v
      have h₁ := KahlerDomination.isSemipositive_smul hdom
        (sub_nonneg.mpr (hq j).1.le) e z hz v
      have h₂ := KahlerDomination.isSemipositive_smul F.omega.isSemipositive
        (show 0 ≤ ε / 2 - ((q j : ℝ) - c) * C by linarith) e z hz v
      simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
        using add_nonneg h₁ h₂
    have hK := isKahlerCurrentPotential_of_le hKqu hsemi
    have hA : (fun x => (((q j : ℝ)) : EReal) * E.weight x) ∈
        analyticCurrents (c • E.curvature + ε • F.omega.form) := by
      refine ⟨isThetaPshPotential_of_isKahlerCurrentPotential hK, fun e z hz => ?_⟩
      exact QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
        (hweight.2 e z hz) hqQ
    have hpoint := flagValuation_self_mem_partialOkounkovBody_of_analytic hK hA
    rw [flagValuation_smul hweight.1 hqpos.le] at hpoint
    exact partialOkounkovBody_subset_kahlerPartialBody hKcu
      (partialOkounkovBody_mono _ (singularityLE_smul_of_le hB hc (hq j).1.le) hpoint)
  exact (isClosed_kahlerPartialBody _ _).mem_of_tendsto
    (hqt.smul tendsto_const_nhds) (Eventually.of_forall hmem)

end SGPT.Okounkov.SourceCurrentValuation
