import SGPT.Foundations.Analysis.Pending.DemaillyAlgebraicApproximationInterface
import SGPT.Foundations.Analysis.Pending.PotentialSmoothTruncation
import SGPT.Foundations.Analysis.Pending.PushforwardPotentialCollarConstruction
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

/-!
# Original global smooth real approximation before choosing auxiliary positivity

The actual C>0 is manufactured FIRST from original geometry. Only then is
an auxiliary ample metric chosen with curvature-C*omega >= kappa*omega.
No vanishing lower-curvature loss is asserted after smoothing non-nef data.
Blueprint: work/sgpt-resume-20261114/bert-e2-global-real-approx/blueprint/bert-e2-global-real-approx.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniGlobalRealApproximation
open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open PotentialSmoothTruncation SmoothMax

def realTruncationValue (w : EReal) (t : ℝ) : ℝ :=
  -t + SmoothMax.posPart ((max w ((-t - 2 : ℝ) : EReal)).toReal + t)

theorem posPart_original_bounds (a : ℝ) : 0 ≤ SmoothMax.posPart a ∧ a ≤ SmoothMax.posPart a := by
  constructor
  · by_cases ha : a ≤ -1
    · rw [posPart_eq_zero ha]
    · have h := posPart_monotone (le_of_not_ge ha)
      rw [posPart_eq_zero (le_refl (-1))] at h
      exact h
  · by_cases ha : 1 ≤ a
    · rw [posPart_eq_self ha]
    · have h := sub_posPart_monotone (le_of_not_ge ha)
      change a - SmoothMax.posPart a ≤ 1 - SmoothMax.posPart 1 at h
      rw [posPart_eq_self (le_refl 1)] at h
      linarith

theorem realTruncationValue_coe (a t : ℝ) :
    realTruncationValue (a : EReal) t = -t + SmoothMax.posPart (a + t) := by
  rw [realTruncationValue, posPart_max_coe]

theorem realTruncationValue_bot (t : ℝ) : realTruncationValue ⊥ t = -t := by
  unfold realTruncationValue
  rw [max_eq_right bot_le, EReal.toReal_coe, posPart_eq_zero (by linarith), add_zero]

theorem realTruncationValue_mono {w z : EReal} (hw : w ≠ ⊤) (hz : z ≠ ⊤)
    (h : w ≤ z) (t : ℝ) : realTruncationValue w t ≤ realTruncationValue z t := by
  induction w using EReal.rec with
  | bot =>
    induction z using EReal.rec with
    | bot => exact le_refl _
    | coe b => rw [realTruncationValue_bot, realTruncationValue_coe]; linarith [(posPart_original_bounds (b + t)).1]
    | top => exact (hz rfl).elim
  | coe a =>
    induction z using EReal.rec with
    | bot => exact ((EReal.bot_lt_coe a).not_ge h).elim
    | coe b =>
      rw [realTruncationValue_coe, realTruncationValue_coe]
      have hab := EReal.coe_le_coe_iff.mp h
      have hp := posPart_monotone (show a + t ≤ b + t by linarith)
      linarith
    | top => exact (hz rfl).elim
  | top => exact (hw rfl).elim

theorem realTruncationValue_antitone_level {w : EReal} (hw : w ≠ ⊤) {s t : ℝ}
    (hst : s ≤ t) : realTruncationValue w t ≤ realTruncationValue w s := by
  induction w using EReal.rec with
  | bot => rw [realTruncationValue_bot, realTruncationValue_bot]; linarith
  | coe a =>
    rw [realTruncationValue_coe, realTruncationValue_coe]
    have h := sub_posPart_monotone (show a + s ≤ a + t by linarith)
    change a + s - SmoothMax.posPart (a + s) ≤ a + t - SmoothMax.posPart (a + t) at h
    linarith
  | top => exact (hw rfl).elim

theorem original_le_realTruncationValue {w : EReal} (hw : w ≠ ⊤) (t : ℝ) :
    w ≤ (realTruncationValue w t : EReal) := by
  induction w using EReal.rec with
  | bot => exact bot_le
  | coe a =>
    rw [realTruncationValue_coe]
    apply EReal.coe_le_coe_iff.mpr
    linarith [(posPart_original_bounds (a + t)).2]
  | top => exact (hw rfl).elim

theorem realTruncationValue_lt_of_original_small {w : EReal} (hw : w ≠ ⊤)
    {R t : ℝ} (hsmall : w < ((R - 2 : ℝ) : EReal)) (hlevel : -t < R - 2) :
    realTruncationValue w t < R := by
  induction w using EReal.rec with
  | bot => rw [realTruncationValue_bot]; linarith
  | coe a =>
    have ha : a < R - 2 := EReal.coe_lt_coe_iff.mp hsmall
    rw [realTruncationValue_coe]
    by_cases ht : 1 ≤ a + t
    · rw [posPart_eq_self ht]; linarith
    · have h := posPart_monotone (le_of_not_ge ht)
      rw [posPart_eq_self (le_refl 1)] at h
      linarith
  | top => exact (hw rfl).elim

theorem tendsto_realTruncationValue_diagonal (u : ℕ → EReal) (hun : ∀ j, u j ≠ ⊤)
    {w : EReal} (hwn : w ≠ ⊤) (huw : ∀ j, w ≤ u j)
    (hlim : Tendsto u atTop (𝓝 w)) :
    Tendsto (fun j => (realTruncationValue (u j) (j : ℝ) : EReal)) atTop (𝓝 w) := by
  induction w using EReal.rec with
  | bot =>
    apply EReal.tendsto_nhds_bot_iff_real.mpr
    intro R
    have he : ∀ᶠ j in atTop, u j < ((R - 2 : ℝ) : EReal) :=
      hlim.eventually (gt_mem_nhds (EReal.bot_lt_coe _))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 - R)
    filter_upwards [he, eventually_ge_atTop N] with j hj hjN
    apply EReal.coe_lt_coe_iff.mpr
    apply realTruncationValue_lt_of_original_small (hun j) hj
    have hc : (N : ℝ) ≤ j := by exact_mod_cast hjN
    linarith
  | coe a =>
    obtain ⟨N, hN⟩ := exists_nat_gt (1 - a)
    have he : ∀ᶠ j in atTop, (realTruncationValue (u j) (j : ℝ) : EReal) = u j := by
      filter_upwards [eventually_ge_atTop N] with j hjN
      have hbot : u j ≠ ⊥ := by
        intro hb
        exact (EReal.bot_lt_coe a).not_ge (hb ▸ huw j)
      have hc : (N : ℝ) ≤ j := by exact_mod_cast hjN
      have ha : a ≤ (u j).toReal := by
        have h := huw j
        rw [← EReal.coe_toReal (hun j) hbot] at h
        exact EReal.coe_le_coe_iff.mp h
      have hlevel : 1 ≤ (u j).toReal + (j : ℝ) := by linarith
      have hv : realTruncationValue (u j) (j : ℝ) = (u j).toReal := by
        conv_lhs => rw [← EReal.coe_toReal (hun j) hbot]
        rw [realTruncationValue_coe, posPart_eq_self hlevel]
        ring
      rw [hv]
      exact EReal.coe_toReal (hun j) hbot
    exact hlim.congr' (he.mono fun j hj => hj.symm)
  | top => exact (hwn rfl).elim

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

theorem exists_uniform_semipositive_background (omega : KahlerBackground n X)
    (α : ClosedRealOneOneForm n X) {δ : ℕ → ℝ} (hδ0 : ∀ j, 0 ≤ δ j)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ (C • omega.form).val.IsSemipositive ∧
      ∀ j, ((C • omega.form) - (α + δ j • omega.form)).val.IsSemipositive := by
  obtain ⟨D, hD⟩ := hδlim.bddAbove_range
  have hD0 : 0 ≤ D := (hδ0 0).trans (hD ⟨0, rfl⟩)
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-α)
  have hC : 0 < A + D + 1 := by linarith
  refine ⟨A + D + 1, hC, KahlerDomination.isSemipositive_smul omega.isSemipositive hC.le, ?_⟩
  intro j c z hz v
  have h1 := hdom c z hz v
  have h2 := omega.isSemipositive c z hz v
  have hδj : δ j ≤ D := hD ⟨j, rfl⟩
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
  nlinarith [mul_nonneg (by linarith : 0 ≤ D + 1 - δ j) h2]

theorem exists_original_global_real_approximation (omega : KahlerBackground n X)
    (α : ClosedRealOneOneForm n X) (φ : X → EReal) (hφ : IsThetaPshPotential α.val φ) :
    ∃ (C : ℝ) (v : ℕ → X → ℝ), 0 < C ∧ (∀ j, ChartSmooth (n := n) (v j)) ∧
      (∀ x, Antitone (fun j => v j x)) ∧ (∀ j x, φ x ≤ (v j x : EReal)) ∧
      (∀ x, Tendsto (fun j => (v j x : EReal)) atTop (𝓝 (φ x))) ∧
      ∀ j, IsThetaPshPotential (C • omega.form).val (fun x => (v j x : EReal)) := by
  obtain ⟨u, δ, han, hanti, hinf, hδ0, hδlim, hpsh⟩ :=
    DemaillyAlgebraicApproximation.exists_algebraicApproximation omega α φ hφ
  obtain ⟨C, hC, hCsemi, hdom⟩ := exists_uniform_semipositive_background omega α hδ0 hδlim
  have hu : ∀ j, IsThetaPshPotential (C • omega.form).val (u j) := fun j =>
    PushforwardPotentialCollarConstruction.isThetaPshPotential_mono (hpsh j) (hdom j)
  have hun : ∀ j x, u j x ≠ ⊤ := fun j x =>
    ManifoldQuasiPlurisubharmonic.ne_top (fun e => (hu j).1.quasiPlurisubharmonic e) x
  have hφn : ∀ x, φ x ≠ ⊤ := fun x =>
    ManifoldQuasiPlurisubharmonic.ne_top (fun e => hφ.1.quasiPlurisubharmonic e) x
  have hφu : ∀ j x, φ x ≤ u j x := by
    intro j x
    rw [← hinf x]
    exact iInf_le _ j
  let v : ℕ → X → ℝ := fun j => smoothTruncation (u j) (j : ℝ)
  have hv : ∀ j x, v j x = realTruncationValue (u j x) (j : ℝ) := fun _ _ => rfl
  refine ⟨C, v, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact chartSmooth_smoothTruncation_of_smoothOffPole (hu j).1 (han j) _
  · intro x i j hij
    change v j x ≤ v i x
    rw [hv, hv]
    exact (realTruncationValue_mono (hun j x) (hun i x) (hanti x hij) (j : ℝ)).trans
      (realTruncationValue_antitone_level (hun i x) (by exact_mod_cast hij))
  · intro j x
    rw [hv]
    exact (hφu j x).trans (original_le_realTruncationValue (hun j x) _)
  · intro x
    have hlim : Tendsto (fun j => u j x) atTop (𝓝 (φ x)) := by
      rw [← hinf x]
      exact tendsto_atTop_iInf (hanti x)
    simpa only [hv] using tendsto_realTruncationValue_diagonal (fun j => u j x)
      (fun j => hun j x) (hφn x) (fun j => hφu j x) hlim
  · intro j
    exact isThetaPshPotential_smoothTruncation_of_smoothOffPole hCsemi (hu j).1 (han j) _

theorem exists_original_global_qpsh_real_approximation (omega : KahlerBackground n X)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    ∃ (C : ℝ) (v : ℕ → X → ℝ), 0 < C ∧ (∀ j, ChartSmooth (n := n) (v j)) ∧
      (∀ x, Antitone (fun j => v j x)) ∧ (∀ j x, φ x ≤ (v j x : EReal)) ∧
      (∀ x, Tendsto (fun j => (v j x : EReal)) atTop (𝓝 (φ x))) ∧
      ∀ j, IsThetaPshPotential (C • omega.form).val (fun x => (v j x : EReal)) := by
  obtain ⟨A, _, hAφ⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul omega hφ
  exact exists_original_global_real_approximation omega (A • omega.form) φ hAφ

end SGPT.Trace.BertiniGlobalRealApproximation
