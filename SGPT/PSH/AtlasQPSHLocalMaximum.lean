import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.Foundations.Analysis.Pending.ActualLocalQuasiPshQuadraticCorrection

/-! Local maximum regularity in the original varying-dimensional atlas.

The simultaneous quadratic correction is manufactured from both genuine
original inputs. No globally closed common background is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open SGPT.Foundations.Analysis.Pending.ActualLocalQuasiPshQuadraticCorrection
open scoped Topology ContDiff

universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The actual coordinate reader has both raw quasi-PSH and original
nondegeneracy, on the entire actual chart target. -/
theorem IsQPSH.coordinate_localQuasiPshPotential {u : X → EReal}
    (hu : A.IsQPSH u) (i : A.Index) :
    LocalQuasiPshPotentialOn (A.coordinate u i) (A.chart i).target := by
  refine ⟨(A.chart i).open_target, hu.chart_quasiPSH i, ?_⟩
  intro z hz V hV hzV
  obtain ⟨y, hy, hfin⟩ := SGPT.PSH.LocallyNondegenerate.exists_coordinate_ne_bot
    hu.locallyNondegenerate
    (A.chart i) ((A.chart i).open_target.inter hV) inter_subset_left ⟨hz, hzV⟩
  exact ⟨y, hy, hfin⟩

/-- Both independent original backgrounds produce ONE actual positive local
quadratic correction; no correction or coefficient is a caller premise. -/
theorem IsQPSH.exists_common_local_quadratic_correction {u w : X → EReal}
    (hu : A.IsQPSH u) (hw : A.IsQPSH w) (i : A.Index)
    {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ball z r ⊆ (A.chart i).target ∧
      PlurisubharmonicOn
        (fun y ↦ A.coordinate u i y + (ballPot C z 0 y : EReal)) (ball z r) ∧
      PlurisubharmonicOn
        (fun y ↦ A.coordinate w i y + (ballPot C z 0 y : EReal)) (ball z r) := by
  obtain ⟨B, b, hB, hb, hbT, huB, hQB, _⟩ :=
    exists_noncollapsed_positive_quadratic_correction (hu.coordinate_localQuasiPshPotential i) hz
  obtain ⟨D, d, hD, hd, hdT, hwD, hQD, _⟩ :=
    exists_noncollapsed_positive_quadratic_correction (hw.coordinate_localQuasiPshPotential i) hz
  have hsubB : ball z (min b d) ⊆ ball z b := ball_subset_ball (min_le_left b d)
  have hsubD : ball z (min b d) ⊆ ball z d := ball_subset_ball (min_le_right b d)
  have hsum (y : ComplexModel (A.dimension i)) :
      ballPot B z 0 y + ballPot D z 0 y = ballPot (B + D) z 0 y := by
    simp only [ballPot]
    ring
  refine ⟨B + D, min b d, add_pos hB hD, lt_min hb hd,
    hsubB.trans hbT, ?_, ?_⟩
  · have h := (huB.mono hsubB).add (hQD.mono hsubD)
    convert h using 1
    funext y
    rw [add_assoc, ← EReal.coe_add, hsum]
  · have h := (hwD.mono hsubD).add (hQB.mono hsubB)
    convert h using 1
    funext y
    rw [add_assoc, ← EReal.coe_add, add_comm (ballPot D z 0 y), hsum]

/-- Actual local PSH-plus-smooth germs of the unchanged original maximum,
including every original pole and zero-dimensional chart. -/
theorem IsQPSH.max_chart_quasiPSH {u w : X → EReal}
    (hu : A.IsQPSH u) (hw : A.IsQPSH w) (i : A.Index) :
    QuasiPlurisubharmonicOn (A.coordinate (fun x ↦ max (u x) (w x)) i)
      (A.chart i).target := by
  intro z hz
  obtain ⟨C, r, _hC, hr, _hsub, huQ, hwQ⟩ :=
    hu.exists_common_local_quadratic_correction hw i hz
  have hmax := (huQ.max hwQ) z (mem_ball_self hr)
  have hp : PlurisubharmonicAt
      (fun y ↦ max (A.coordinate u i y) (A.coordinate w i y) +
        (ballPot C z 0 y : EReal)) z := by
    apply hmax.congr
    exact Eventually.of_forall fun y ↦
      max_add_add_right (A.coordinate u i y) (A.coordinate w i y) (ballPot C z 0 y : EReal)
  refine ⟨_, fun y ↦ -ballPot C z 0 y, hp,
    Eventually.of_forall (fun y ↦ (contDiff_ballPot C z 0).neg.contDiffAt), ?_⟩
  exact Eventually.of_forall fun y ↦ by
    change max (u ((A.chart i).symm y)) (w ((A.chart i).symm y)) =
      (max (u ((A.chart i).symm y)) (w ((A.chart i).symm y)) +
        (ballPot C z 0 y : EReal)) + ((-ballPot C z 0 y : ℝ) : EReal)
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- Every original open neighborhood contains a nonpole of the actual maximum. -/
theorem IsQPSH.max_locallyNondegenerate {u w : X → EReal}
    (hu : A.IsQPSH u) : LocallyNondegenerate (fun x ↦ max (u x) (w x)) := by
  intro x U hU hx
  obtain ⟨y, hy, hfin⟩ := hu.locallyNondegenerate x U hU hx
  refine ⟨y, hy, ?_⟩
  intro hbot
  exact hfin (le_bot_iff.mp ((le_max_left (u y) (w y)).trans_eq hbot))

/-- The actual locally nondegenerate function supplies a proper zero locus
in the SAME original connected analytic presentation. -/
theorem HasRationalAnalyticType.exists_proper_presentation_of_locallyNondegenerate
    {u : X → EReal} (han : A.HasRationalAnalyticType u)
    (hu : LocallyNondegenerate u) (x : X) :
    ∃ (c : ℚ) (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
      0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧ (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y ↦ ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U ∧
        ∃ y ∈ U, ∃ j, f j y ≠ 0 := by
  obtain ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hxU, hf, hb, heq⟩ := han x
  obtain ⟨y, hy, hfin⟩ := hu x U hU hxU
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnonzero : ¬ ∀ j, f j y = 0 := by
    intro hz
    exact hfin ((heq hy).trans ((scaled_generatorLog_add_eq_bot_iff f y hcR (b y)).mpr hz))
  push Not at hnonzero
  exact ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hxU, hf, hb, heq, y, hy, hnonzero⟩

/-- Original analytic max presentations are genuine and noncollapsed, with no
new global-QPSH assumption on the output maximum. -/
theorem IsQPSH.exists_local_maximum_analytic_presentation {u w : X → EReal}
    (hu : A.IsQPSH u) (hanU : A.HasRationalAnalyticType u)
    (hanW : A.HasRationalAnalyticType w) (x : X) :
    ∃ (c : ℚ) (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
      0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧ (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn (fun y ↦ max (u y) (w y))
          (fun y ↦ ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U ∧
        ∃ y ∈ U, ∃ j, f j y ≠ 0 :=
  (hanU.max hanW).exists_proper_presentation_of_locallyNondegenerate
    hu.max_locallyNondegenerate x

end SGPT.PSH.VariableComplexAtlas
