import SGPT.Foundations.Analysis.BallSubmean
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.ExtendedDifference
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Genuine moving-ball upper recovery for singular PSH functions

The literal original extended-real functions are bounded at every moving
center by the genuine canonical L1 error on one larger compact ball. Poles
are preserved and the real representative is used only after actual
almost-everywhere finiteness and integrability have been proved.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate

open FirstPass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Real ball submeans for the original singular function, with only a finite center. -/
theorem real_ball_submean_of_ne_bot {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {R : ℝ} (hR : 0 < R) (hB : closedBall a R ⊆ U)
    (ha : u a ≠ ⊥) :
    (μ (ball a R)).toReal * (u a).toReal ≤ ∫ x in ball a R, (u x).toReal ∂μ := by
  have hmassfin : μ (ball a R) < ⊤ := measure_ball_lt_top
  let : IsFiniteMeasure (μ.restrict (ball a R)) := ⟨by simpa using hmassfin⟩
  obtain ⟨C, hC⟩ := hu.exists_compact_upper_bound (isCompact_closedBall a R)
    ⟨a, mem_closedBall_self hR.le⟩ hB
  have hCa : u a ≠ ⊤ := hu.ne_top a (hB (mem_closedBall_self hR.le))
  have hrealCa : (u a).toReal ≤ C := by
    have h := hC a (mem_closedBall_self hR.le)
    rw [← EReal.coe_toReal hCa ha, EReal.coe_le_coe_iff] at h
    exact h
  have hU : ball a R ⊆ U := ball_subset_closedBall.trans hB
  obtain ⟨hfinite, hint, _⟩ := hu.ae_finite_and_integrableOn_ball μ a hR hB ha
  let d : E → ℝ≥0∞ := fun x => ((C : EReal) - u x).toENNReal
  have hdvalue (z : E) (ht : u z ≠ ⊤) (hb : u z ≠ ⊥) :
      d z = ENNReal.ofReal (C - (u z).toReal) := by
    calc d z = ((C : EReal) - (((u z).toReal : ℝ) : EReal)).toENNReal := by
          rw [EReal.coe_toReal ht hb]
      _ = _ := by rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hd : AEMeasurable d (μ.restrict (ball a R)) :=
    hu.aemeasurable_deficit_restrict measurableSet_ball hU C μ
  have hdfin : ∀ᵐ x ∂μ.restrict (ball a R), d x < ⊤ := by
    filter_upwards [hfinite] with x hx
    rw [hdvalue x hx.1 hx.2]
    exact ENNReal.ofReal_lt_top
  have hdeq : ∫ x in ball a R, (d x).toReal ∂μ =
      (μ (ball a R)).toReal * C - ∫ x in ball a R, (u x).toReal ∂μ := by
    have heq : (fun x => (d x).toReal) =ᶠ[ae (μ.restrict (ball a R))]
        (fun x => C - (u x).toReal) := by
      filter_upwards [ae_restrict_mem measurableSet_ball, hfinite] with x hx hxf
      have hbound : (u x).toReal ≤ C := by
        have h := hC x (ball_subset_closedBall hx)
        rw [← EReal.coe_toReal hxf.1 hxf.2, EReal.coe_le_coe_iff] at h
        exact h
      rw [hdvalue x hxf.1 hxf.2, ENNReal.toReal_ofReal (sub_nonneg.mpr hbound)]
    rw [integral_congr_ae heq, integral_sub (integrable_const C) hint]
    simp [integral_const, Measure.real, smul_eq_mul]
  have hmass : μ (ball (0 : E) R) = μ (ball a R) := by
    simpa using lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) a R
  have hineq := hu.ball_deficit_le μ a R C hU
    (fun x hx => hC x (ball_subset_closedBall hx))
  have hfin : μ (ball (0 : E) R) * d a ≠ ⊤ := by
    apply ENNReal.mul_ne_top measure_ball_lt_top.ne
    rw [hdvalue a hCa ha]
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin hineq
  change (∫⁻ x in ball a R, d x ∂μ).toReal ≤ _ at hreal
  rw [← integral_toReal hd hdfin, hdeq] at hreal
  change _ ≤ (μ (ball (0 : E) R) * d a).toReal at hreal
  simp only [ENNReal.toReal_mul, hmass, hdvalue a hCa ha,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hrealCa)] at hreal
  nlinarith

/-- Every actual center value is controlled by the integrable real error on its own ball. -/
theorem le_real_bound_add_l1_ball_error {u : E → EReal} {v : E → ℝ} {U : Set E}
    (hu : DiscPshOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {R A : ℝ} (hR : 0 < R) (hB : closedBall a R ⊆ U)
    (hv : IntegrableOn v (ball a R) μ) (hA : ∀ᵐ x ∂μ.restrict (ball a R), v x ≤ A) :
    u a ≤ ((A + (∫ x in ball a R, |(u x).toReal - v x| ∂μ) /
      (μ (ball a R)).toReal : ℝ) : EReal) := by
  by_cases ha : u a = ⊥
  · rw [ha]
    exact bot_le
  have hCa : u a ≠ ⊤ := hu.ne_top a (hB (mem_closedBall_self hR.le))
  let : IsFiniteMeasure (μ.restrict (ball a R)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := μ) (x := a) (r := R))⟩
  have hint := (hu.ae_finite_and_integrableOn_ball μ a hR hB ha).2.1
  have herr : IntegrableOn (fun x => |(u x).toReal - v x|) (ball a R) μ := by
    exact (hint.sub hv).abs
  have hupper : (∫ x in ball a R, (u x).toReal ∂μ) ≤
      (∫ x in ball a R, v x ∂μ) + ∫ x in ball a R, |(u x).toReal - v x| ∂μ := by
    calc (∫ x in ball a R, (u x).toReal ∂μ) ≤
        ∫ x in ball a R, v x + |(u x).toReal - v x| ∂μ := by
          apply integral_mono_ae hint (hv.add herr)
          exact Eventually.of_forall fun x => by
            change (u x).toReal ≤ v x + |(u x).toReal - v x|
            linarith [le_abs_self ((u x).toReal - v x)]
      _ = _ := by simpa only [Pi.add_apply] using integral_add hv herr
  have hvupper : (∫ x in ball a R, v x ∂μ) ≤ (μ (ball a R)).toReal * A := by
    have h := integral_mono_ae hv (integrable_const A) hA
    simpa [integral_const, Measure.real, smul_eq_mul] using h
  have hm : 0 < (μ (ball a R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ a hR).ne' measure_ball_lt_top.ne
  rw [← EReal.coe_toReal hCa ha, EReal.coe_le_coe_iff]
  have hsubmean := real_ball_submean_of_ne_bot hu μ a hR hB ha
  have hdiv : (u a).toReal - A ≤
      (∫ x in ball a R, |(u x).toReal - v x| ∂μ) / (μ (ball a R)).toReal :=
    (le_div_iff₀ hm).mpr (by nlinarith)
  linarith

/-- One canonical L1 error controls all moving centers simultaneously, including poles. -/
theorem eventually_le_on_ball_of_lintegral_canonical_tendsto
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, PlurisubharmonicOn (u j) U) (hv : PlurisubharmonicOn v U)
    (hU : IsPreconnected U) (hne : ∀ j, ∃ a ∈ U, u j a ≠ ⊥)
    (hvne : ∃ a ∈ U, v a ≠ ⊥)
    (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) {r A δ : ℝ}
    (hr : 0 < r) (hK : closedBall x (3 * r) ⊆ U)
    (hA : ∀ z ∈ closedBall x (3 * r), v z ≤ (A : EReal))
    (hlim : Tendsto (fun j => ∫⁻ z in closedBall x (3 * r),
      canonicalERealAbsDiff (u j z) (v z) ∂μ) atTop (𝓝 0))
    (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ y ∈ ball x r, u j y ≤ ((A + δ : ℝ) : EReal) := by
  let K : Set E := closedBall x (3 * r)
  have hcompact : IsCompact K := isCompact_closedBall x (3 * r)
  have hintu (j : ℕ) : IntegrableOn (fun z => (u j z).toReal) K μ :=
    ((hu j).locallyIntegrableOn_toReal μ hU (hne j)).integrableOn_compact_subset hK hcompact
  have hintv : IntegrableOn (fun z => (v z).toReal) K μ :=
    (hv.locallyIntegrableOn_toReal μ hU hvne).integrableOn_compact_subset hK hcompact
  have hfinu (j : ℕ) : ∀ᵐ z ∂μ.restrict K, u j z ≠ ⊤ ∧ u j z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hK ((hu j).ae_finite μ hU (hne j))
  have hfinv : ∀ᵐ z ∂μ.restrict K, v z ≠ ⊤ ∧ v z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hK (hv.ae_finite μ hU hvne)
  let err : ℕ → ℝ := fun j => ∫ z in K, |(u j z).toReal - (v z).toReal| ∂μ
  have herr (j : ℕ) : err j = (∫⁻ z in K, canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal := by
    dsimp only [err]
    have hi : IntegrableOn (fun z => |(u j z).toReal - (v z).toReal|) K μ := by
      exact (hintu j |>.sub hintv |>.abs)
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun z => |(u j z).toReal - (v z).toReal|)
      (Eventually.of_forall fun _ => abs_nonneg _) hi.aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinu j, hfinv] with z hz₁ hz₂
    rw [← EReal.coe_toReal hz₁.1 hz₁.2, ← EReal.coe_toReal hz₂.1 hz₂.2,
      canonicalERealAbsDiff_coe_coe]
    simp only [EReal.toReal_coe]
  have herrlim : Tendsto err atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have h' : Tendsto (fun j => (∫⁻ z in K,
        canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal) atTop (𝓝 0) := by
      change Tendsto (fun j => (∫⁻ z in K,
        canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal) atTop (𝓝 (ENNReal.toReal 0)) at h
      simpa only [ENNReal.toReal_zero] using h
    exact h'.congr (fun j => (herr j).symm)
  let m : ℝ := (μ (ball (0 : E) r)).toReal
  have hm : 0 < m :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  have hsmall : ∀ᶠ j in atTop, err j < δ * m :=
    herrlim.eventually (gt_mem_nhds (mul_pos hδ hm))
  filter_upwards [hsmall] with j hj
  intro y hy
  have hclosed : closedBall y r ⊆ K := by
    intro z hz
    apply mem_closedBall.mpr
    have hzy : dist z y ≤ r := mem_closedBall.mp hz
    have hyx : dist y x < r := mem_ball.mp hy
    have htri := dist_triangle z y x
    linarith
  have hball : ball y r ⊆ K := ball_subset_closedBall.trans hclosed
  have hmass : μ (ball y r) = μ (ball (0 : E) r) := by
    simpa using (lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) y r).symm
  have hlocalA : ∀ᵐ z ∂μ.restrict (ball y r), (v z).toReal ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae_restrict_of_subset hball hfinv] with z hz hzf
    have h := hA z (hball hz)
    rw [← EReal.coe_toReal hzf.1 hzf.2, EReal.coe_le_coe_iff] at h
    exact h
  have hbound := le_real_bound_add_l1_ball_error (hu j).discPshOn μ y hr
    (hclosed.trans hK) (hintv.mono_set hball) hlocalA
  have herror : (∫ z in ball y r, |(u j z).toReal - (v z).toReal| ∂μ) ≤ err j := by
    exact setIntegral_mono_set (hintu j |>.sub hintv |>.abs)
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hball)
  refine hbound.trans (EReal.coe_le_coe_iff.mpr ?_)
  rw [hmass]
  change A + _ / m ≤ A + δ
  exact add_le_add le_rfl ((div_le_iff₀ hm).mpr (herror.trans hj.le))

end SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate
