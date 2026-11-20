import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.LogPole

set_option autoImplicit false

/-! # A genuine uniform extended divisorial slice bound for a whole family -/

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.DivisorialUniformFamilySliceBound

open FirstPass FirstPass.NonKahlerLocus DemaillyApproximantDivisorialLelong
  DivisorialSliceBound ThetaPshDecreasingLimit

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]


/-- One actual local potential gives a uniform extended slice barrier for a
whole raw family, including its genuine negative-infinite divisor values. -/
theorem exists_uniform_extended_slice_bound {I : Type*} [Nonempty I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal))
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ,
      ball (0 : ComplexModel (m + 1)) r ⊆ Φ.Φ.target ∧
      ∀ γ : ℝ≥0, 0 < γ →
        (∀ i, (γ : ℝ≥0∞) < divisorialLelongNumber m (u i) E) →
        ∀ i z, z ∈ ball (0 : ComplexModel (m + 1)) r →
          u i (Φ.point z) ≤ (((γ : ℝ) / 2 : ℝ) : EReal) *
            logNormSq (z (Fin.last m)) + ((A - (γ : ℝ) * Real.log r : ℝ) : EReal) := by
  classical
  let e := complexChartAt (n := m + 1) x
  obtain ⟨W, ρ, hxW, hρ, _⟩ := hu (Classical.arbitrary I) e (e.val x)
    (e.val.map_source (mem_complexChartAt_source x))
  let U : Set (ComplexModel (m + 1)) := Φ.Φ.target ∩ Φ.Φ.invFun ⁻¹' W
  have hU : IsOpen U :=
    Φ.Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.Φ.isOpen_target hρ.1
  have h0U : (0 : ComplexModel (m + 1)) ∈ U := by
    refine ⟨Φ.zero_mem_target, ?_⟩
    simpa only [mem_preimage, Φ.invFun_zero] using hxW
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  let H : ComplexModel (m + 1) → ℝ := fun z => ρ (Φ.Φ.invFun z)
  let P : I → ComplexModel (m + 1) → EReal := fun i z => u i (Φ.point z) + (H z : EReal)
  have hHU : ContinuousOn H U := hρ.2.2.1.continuousOn.comp
    (Φ.Φ.invFun_holomorphic.continuousOn.mono inter_subset_left) (fun _ hz => hz.2)
  have hP (i : I) : PlurisubharmonicOn (P i) U := by
    have hc := plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hu i) e hρ
    exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU
      (Φ.Φ.invFun_holomorphic.mono inter_subset_left) (fun _ hz => hz.2) hc
  have hclosed : closedBall (0 : ComplexModel (m + 1)) (R / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ComplexModel (m + 1)) (R / 2)).exists_bound_of_continuousOn
    (hHU.mono hclosed)
  have habs (z : ComplexModel (m + 1)) (hz : z ∈ closedBall (0 : ComplexModel (m + 1)) (R / 2)) :
      |H z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z hz
  let r : ℝ := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h2r : 2 * r = R / 2 := by dsimp [r]; ring
  have hΩ : closedBall (0 : ComplexModel (m + 1)) (2 * r) ⊆ U := by
    rw [h2r]; exact hclosed
  have hsmall : ball (0 : ComplexModel (m + 1)) r ⊆
      closedBall (0 : ComplexModel (m + 1)) (R / 2) :=
    (ball_subset_ball (by dsimp [r]; linarith)).trans ball_subset_closedBall
  have hK (i : I) (z : ComplexModel (m + 1))
      (hz : z ∈ closedBall (0 : ComplexModel (m + 1)) (2 * r)) :
      P i z ≤ ((B + M : ℝ) : EReal) := by
    have hz' : z ∈ closedBall (0 : ComplexModel (m + 1)) (R / 2) := by rwa [h2r] at hz
    exact (add_le_add (hB i _) (EReal.coe_le_coe_iff.mpr (abs_le.mp (habs z hz')).2)).trans_eq
      (EReal.coe_add B M).symm
  have hlow (i : I) (z : ComplexModel (m + 1))
      (hz : z ∈ closedBall (0 : ComplexModel (m + 1)) (R / 2)) :
      P i z ≤ u i (Φ.point z) + (M : EReal) :=
    add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (habs z hz)).2)
  have hupper (i : I) (z : ComplexModel (m + 1))
      (hz : z ∈ closedBall (0 : ComplexModel (m + 1)) (R / 2)) :
      u i (Φ.point z) ≤ P i z + (M : EReal) := by
    have hn : 0 ≤ H z + M := by linarith [(abs_le.mp (habs z hz)).1]
    calc u i (Φ.point z) = u i (Φ.point z) + (0 : EReal) := (add_zero _).symm
      _ ≤ u i (Φ.point z) + ((H z + M : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_nonneg.mpr hn)
      _ = P i z + (M : EReal) := by simp only [P, EReal.coe_add, add_assoc]
  refine ⟨r, hr, B + 2 * M, (fun z hz => (hclosed (hsmall hz)).1), ?_⟩
  intro γ hγ hν i z hz
  have hγreal : 0 < (γ : ℝ) := by exact_mod_cast hγ
  have hzt : z ∈ Φ.Φ.target := (hclosed (hsmall hz)).1
  by_cases hz0 : z (Fin.last m) = 0
  · have hpoint : (γ : ℝ≥0∞) < lelongNumber (n := m + 1) (u i) (Φ.point z) :=
      (hν i).trans_le (divisorialLelongNumber_le (Φ.point_mem hzt hz0))
    have hbot := eq_bot_of_lelongNumber_pos (Nat.succ_pos m) (hu i)
      ((ENNReal.coe_pos.mpr hγ).trans hpoint)
    rw [hbot, hz0, logNormSq_zero, EReal.coe_mul_bot_of_pos (by positivity)]
    exact bot_le
  have hadm : ∀ q ∈ ball (0 : ComplexModel (m + 1)) r, q (Fin.last m) = 0 →
      ∃ γ' > (γ : ℝ), ∃ C : ℝ, ∀ᶠ w in 𝓝[≠] q,
        P i w ≤ ((γ' * Real.log ‖w - q‖ + C : ℝ) : EReal) := by
    intro q hq hq0
    have hqt : q ∈ Φ.Φ.target := (hclosed (hsmall hq)).1
    have hcomp := LelongNumberComparison.lelongNumber_le_comp
      (u := u i) (Φ.mdifferentiableAt_point hqt)
      (eq_bot_of_lelongNumber_pos (Nat.succ_pos m) (hu i))
    have hlt : (γ : ℝ≥0∞) < lelongNumber (n := m + 1) (fun w => u i (Φ.point w)) q :=
      ((hν i).trans_le (divisorialLelongNumber_le (Φ.point_mem hqt hq0))).trans_le hcomp
    obtain ⟨γ', hγ', C, hC⟩ := exists_admissible_of_lt_lelongNumber hlt
    have hnear : ∀ᶠ w in 𝓝[≠] q,
        w ∈ closedBall (0 : ComplexModel (m + 1)) (R / 2) := by
      apply nhdsWithin_le_nhds
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds
        (ball_subset_ball (by dsimp [r] at hq ⊢; linarith) hq)) ball_subset_closedBall
    refine ⟨γ', hγ', C + M, ?_⟩
    filter_upwards [hC, hnear] with w hw hwb
    calc P i w ≤ u i (Φ.point w) + (M : EReal) := hlow i w hwb
      _ ≤ ((γ' * Real.log ‖w - q‖ + C : ℝ) : EReal) + (M : EReal) := add_le_add hw le_rfl
      _ = ((γ' * Real.log ‖w - q‖ + (C + M) : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
  have hs := le_log_last_add_of_admissible (hP i) (by simp) hΩ (hK i) hadm hz hz0
  have hlog : logNormSq (z (Fin.last m)) = ((2 * Real.log ‖z (Fin.last m)‖ : ℝ) : EReal) := by
    rw [logNormSq_of_ne_zero hz0, Real.log_pow]; norm_num
  rw [hlog, ← EReal.coe_mul, ← EReal.coe_add]
  exact (hupper i z (hsmall hz)).trans (add_le_add hs le_rfl) |>.trans_eq (by
    rw [← EReal.coe_add]; congr 1; ring)


/-- Actual local upper-semicontinuous regularization keeps the complete
uniform family bound, including the negative-infinite coordinate divisor. -/
theorem exists_uniform_regularized_sup_slice_bound {I : Type*} [Nonempty I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal))
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ,
      ball (0 : ComplexModel (m + 1)) r ⊆ Φ.Φ.target ∧
      ∀ γ : ℝ≥0, 0 < γ →
        (∀ i, (γ : ℝ≥0∞) < divisorialLelongNumber m (u i) E) →
        ∀ z, z ∈ ball (0 : ComplexModel (m + 1)) r →
          uscRegularization (fun w => ⨆ i, u i (Φ.point w)) z ≤
            (((γ : ℝ) / 2 : ℝ) : EReal) * logNormSq (z (Fin.last m)) +
              ((A - (γ : ℝ) * Real.log r : ℝ) : EReal) := by
  obtain ⟨r, hr, A, hrt, hall⟩ := exists_uniform_extended_slice_bound hu hB Φ
  refine ⟨r, hr, A, hrt, ?_⟩
  intro γ hγ hν z hz
  have hc : Continuous (fun w : ComplexModel (m + 1) => w (Fin.last m)) := by fun_prop
  have hg : UpperSemicontinuous (fun w : ComplexModel (m + 1) =>
      (((γ : ℝ) / 2 : ℝ) : EReal) * logNormSq (w (Fin.last m)) +
        ((A - (γ : ℝ) * Real.log r : ℝ) : EReal)) :=
    upperSemicontinuous_add_coe_continuous
      (upperSemicontinuous_eReal_const_mul
        (continuous_logNormSq.comp hc).upperSemicontinuous (by positivity)) continuous_const
  apply uscRegularization_le_of_eventually_le (hg z)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact iSup_le fun i => hall γ hγ hν i w hw

end
end SGPT.Foundations.Analysis.Pending.DivisorialUniformFamilySliceBound
