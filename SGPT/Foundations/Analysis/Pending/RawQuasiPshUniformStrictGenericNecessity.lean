import SGPT.Foundations.Analysis.Pending.RawQuasiPshTestGenericLelongBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

set_option autoImplicit false

/-! # Uniform strict local generic necessity from the original raw germ

The improved exponent is produced on the original raw quasi-PSH germ before
all local reader pieces. Identically bot weights and zero tests are included
in the strong-openness producer. The nonzero test consumer internally supplies
its orders and a strict margin, with no analytic-weight certificate.
Reference: Guan--Zhou strong openness, as proved in the existing regular route;
Xia valuative discussion, supplementary local necessary direction.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshUniformStrictGenericNecessity

open FirstPass FirstPass.NonKahlerLocus HolomorphicGermReducednessBridge

noncomputable section

/-- Genuine raw-germ strong openness: the same original test is integrable at
an internally supplied larger exponent, without a global or nondegenerate weight. -/
theorem exists_gt_multiplierIntegrableAt {n : ℕ} {u : ComplexModel n → EReal}
    {x : ComplexModel n} (hu : QuasiPlurisubharmonicAt u x) {c : ℝ}
    {F : ComplexModel n → ℂ} (hint : MultiplierIntegrableAt u c F x volume) :
    ∃ q : ℝ, c < q ∧ MultiplierIntegrableAt u q F x volume := by
  obtain ⟨P, h, ⟨U, hU, hxU, hdisc⟩, hh, heq⟩ := hu
  have hPU : PlurisubharmonicOn P U := hdisc.plurisubharmonicOn hU
  have hhc : ContinuousAt h x := hh.self_of_nhds.continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, |h y - h x| < 1 := by
    filter_upwards [hhc (Metric.ball_mem_nhds (h x) one_pos)] with y hy
    simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using hy
  have h1 : MoreSingularAt u P x := by
    refine ⟨h x + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    linarith [(abs_lt.mp hb).2]
  have h2 : MoreSingularAt P u x := by
    refine ⟨-h x + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy, add_assoc, ← EReal.coe_add]
    refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
    linarith [(abs_lt.mp hb).1]
  have hPint := multiplierIntegrableAt_of_moreSingularAt
    (hPU x hxU).quasiPlurisubharmonicAt h1 hint
  obtain ⟨q, hcq, hPq⟩ :=
    PositiveCurrentTraceMultiplier.exists_gt_multiplierIntegrableAt hU hPU hxU hPint
  have hraw : QuasiPlurisubharmonicAt u x := ⟨P, h, ⟨U, hU, hxU, hdisc⟩, hh, heq⟩
  exact ⟨q, hcq, multiplierIntegrableAt_of_moreSingularAt hraw h2 hPq⟩

/-- One improved exponent produces one positive strict margin and all test
orders before every local hyperplane reader radius. -/
theorem exists_uniform_strict_generic_bound {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    (hu : QuasiPlurisubharmonicAt u 0) {c : ℝ} {F : ComplexModel (m + 1) → ℂ}
    (hint : MultiplierIntegrableAt u c F 0 volume)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), F z ≠ 0) :
    ∃ (δ : ℝ), 0 < δ ∧ ∃ (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
      (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z),
      (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), H z ≠ 0) ∧
      F =ᶠ[𝓝 0] (fun z => H z * ∏ j : Fin (m + 1), z j ^ a j) ∧
      (∀ j : Fin (m + 1), ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
        (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) ∧
      ∀ R : ℝ, 0 < R →
        ENNReal.ofReal ((1 + δ) * c) *
          (⨅ y ∈ ball (0 : ComplexModel (m + 1)) R ∩ {y | y (Fin.last m) = 0},
            lelongNumber (n := m + 1) u y) <
          ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1)) := by
  have hc : 0 < c := hint.1
  obtain ⟨q, hcq, hq⟩ := exists_gt_multiplierIntegrableAt hu hint
  have hqpos : 0 < q := hc.trans hcq
  let δ : ℝ := (q - c) / (2 * c)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hcq) (by positivity)
  have hcoeff : (1 + δ) * c = (q + c) / 2 := by
    dsimp only [δ]
    field_simp
    ring
  have hκpos : 0 < (1 + δ) * c := by rw [hcoeff]; positivity
  have hκq : (1 + δ) * c < q := by rw [hcoeff]; linarith
  obtain ⟨a, H, hH, hHnon, heq, hnot, hbound⟩ :=
    RawQuasiPshTestGenericLelongBound.exists_orders_and_generic_bound hu hq hne
  refine ⟨δ, hδ, a, H, hH, hHnon, heq, hnot, fun R hR => ?_⟩
  have hB : 0 < 2 * ((a (Fin.last m) : ℝ) + 1) := by positivity
  have hprod : (1 + δ) * c * (2 * ((a (Fin.last m) : ℝ) + 1) / q) <
      2 * ((a (Fin.last m) : ℝ) + 1) := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hqpos).mpr
    nlinarith [mul_lt_mul_of_pos_right hκq hB]
  calc
    _ ≤ ENNReal.ofReal ((1 + δ) * c) *
        ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1) / q) :=
      by
        gcongr
        exact hbound R hR
    _ = ENNReal.ofReal ((1 + δ) * c * (2 * ((a (Fin.last m) : ℝ) + 1) / q)) :=
      (ENNReal.ofReal_mul hκpos.le).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hB).mpr hprod

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshUniformStrictGenericNecessity
