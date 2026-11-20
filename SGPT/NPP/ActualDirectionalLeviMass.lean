import SGPT.NPP.LeviMassCutoff
import SGPT.Foundations.Analysis.PositiveDistributionMeasure

/-!
# Actual directional Levi measures and the crude radius-mass bound

Complete blueprint: `blueprint/src/dnt-big-actual-levi-mass.tex`, written
first. Positive Levi measures are manufactured from the actual PSH regular
distribution. The actual scaled smooth cutoff and actual integration by parts
prove the radius-mass bound; no assigned measure or mass certificate is input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology Distributions ContDiff CompactlySupported ENNReal

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

private def massCutoffTest {Ω : Opens (ComplexModel n)}
    (y : ComplexModel n) (r : ℝ) (hr : 0 < r) (hK : closedBall y (2 * r) ⊆ Ω) :
    𝓓(Ω, ℝ) where
  toFun := leviMassCutoff y r
  contDiff' := contDiff_leviMassCutoff y r
  hasCompactSupport' := (isCompact_closedBall y (2 * r)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_leviMassCutoff_subset hr y)
  tsupport_subset' := (tsupport_leviMassCutoff_subset hr y).trans hK

private theorem compact_test_integrable {Ω : Opens (ComplexModel n)}
    (ν : Measure Ω) [IsLocallyFiniteMeasure ν] (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x : Ω => φ x) ν := by
  let f : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
  exact (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).congr
    (Eventually.of_forall fun x => by simp [f])

private theorem cutoff_pairing_abs_le {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {B N : ℝ} (hB0 : 0 ≤ B)
    (hub : ∀ x ∈ Ω, |u x| ≤ B)
    (hN : ∀ (y : ComplexModel n) (r : ℝ), 0 < r → ∀ x v : ComplexModel n,
      |leviForm (leviMassCutoff y r) x v| ≤ N * ‖v‖ ^ 2 / r ^ 2 ∧
      (x ∉ closedBall y (2 * r) → leviForm (leviMassCutoff y r) x v = 0))
    (hN0 : 0 ≤ N) (y : ComplexModel n) (r : ℝ) (hr : 0 < r)
    (hK : closedBall y (2 * r) ⊆ Ω) (v : ComplexModel n) :
    |∫ x, u x * leviForm (massCutoffTest y r hr hK) x v| ≤
      B * (N * ‖v‖ ^ 2 / r ^ 2) * volume.real (closedBall y (2 * r)) := by
  let K : Set (ComplexModel n) := closedBall y (2 * r)
  let D : ℝ := B * (N * ‖v‖ ^ 2 / r ^ 2)
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hdom : Integrable (K.indicator (fun _ : ComplexModel n => D)) volume :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hbound : ∀ᵐ x ∂volume,
      ‖u x * leviForm (massCutoffTest y r hr hK) x v‖ ≤ K.indicator (fun _ => D) x := by
    exact Eventually.of_forall fun x => by
      change ‖u x * leviForm (leviMassCutoff y r) x v‖ ≤ K.indicator (fun _ => D) x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hub x (hK hx)) (hN y r hr x v).1 (abs_nonneg _) hB0
      · rw [Set.indicator_of_notMem hx, (hN y r hr x v).2 hx, mul_zero, norm_zero]
  have hh := norm_integral_le_of_norm_le hdom hbound
  rw [Real.norm_eq_abs, integral_indicator measurableSet_closedBall] at hh
  simpa only [setIntegral_const, smul_eq_mul, measureReal_def, D, mul_comm] using hh

/-- Actual finite PSH, its actual positive Levi distribution and an actual
scaled cutoff manufacture both the directional measures and their ball bound. -/
theorem exists_directionalLeviMeasures_ball_bound_of_boundedPsh
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun x => (u x : EReal)) Ω)
    {B : ℝ} (hB0 : 0 ≤ B) (hub : ∀ x ∈ Ω, |u x| ≤ B)
    {c : ComplexModel n} {a : ℝ} (_ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ Ω) :
    let hL := locallyIntegrableOn_of_plurisubharmonicOn_real hu
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ComplexModel n, ∃ ν : Measure Ω,
      ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      (∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) =
        distributionalLeviCLM v (regularDistribution volume u hL) φ) ∧
      ∀ y ∈ ball c (2 * a), ∀ r : ℝ, 0 < r → r < a →
        ν {x : Ω | x.val ∈ ball y r} ≤
          ENNReal.ofReal (C * ‖v‖ ^ 2 * (r ^ Module.finrank ℝ (ComplexModel n) / r ^ 2)) := by
  intro hL
  obtain ⟨N, hN0, hN⟩ := exists_bound_scaled_levi_massCutoff (n := n)
  let d := Module.finrank ℝ (ComplexModel n)
  let V : ℝ := volume.real (closedBall (0 : ComplexModel n) 1)
  let C : ℝ := B * N * 2 ^ d * V
  have hC0 : 0 ≤ C := by dsimp only [C, V]; positivity
  have hT : HasNonnegativeDistributionalLevi (regularDistribution volume u hL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu
  refine ⟨C, hC0, fun v => ?_⟩
  obtain ⟨ν, hregular, hlocal, hrep⟩ := (hT v).exists_regular_measure
  let _ : IsLocallyFiniteMeasure ν := hlocal
  refine ⟨ν, hregular, hlocal, hrep, ?_⟩
  intro y hy r hr hra
  have hKΩ : closedBall y (2 * r) ⊆ Ω := by
    intro x hx
    apply hball
    have hxy : dist x y ≤ 2 * r := hx
    have hyc : dist y c < 2 * a := hy
    change dist x c ≤ 4 * a
    have ht := dist_triangle x y c
    linarith
  let φ : 𝓓(Ω, ℝ) := massCutoffTest y r hr hKΩ
  have hφn : ∀ x : Ω, 0 ≤ φ x := fun x => leviMassCutoff_nonneg y r x
  have hφI : Integrable (fun x : Ω => φ x) ν := compact_test_integrable ν φ
  have hmeas : MeasurableSet {x : Ω | x.val ∈ ball y r} :=
    isOpen_ball.measurableSet.preimage continuous_subtype_val.measurable
  have hmass : ν {x : Ω | x.val ∈ ball y r} ≤ ENNReal.ofReal (∫ x : Ω, φ x ∂ν) := by
    calc
      ν {x : Ω | x.val ∈ ball y r} =
          ∫⁻ x : Ω, ({x : Ω | x.val ∈ ball y r}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
        simp only [lintegral_indicator hmeas, lintegral_const, one_mul, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x : Ω, ENNReal.ofReal (φ x) ∂ν := lintegral_mono fun x => by
        by_cases hx : x.val ∈ ball y r
        · rw [Set.indicator_of_mem (show x ∈ {x : Ω | x.val ∈ ball y r} from hx)]
          change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (leviMassCutoff y r x.val)
          rw [leviMassCutoff_eq_one hr y (ball_subset_closedBall hx)]
          simp
        · rw [Set.indicator_of_notMem (show x ∉ {x : Ω | x.val ∈ ball y r} from hx)]
          exact bot_le
      _ = ENNReal.ofReal (∫ x : Ω, φ x ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hφI (Eventually.of_forall hφn)).symm
  have hpair := cutoff_pairing_abs_le hB0 hub hN hN0 y r hr hKΩ v
  have hvol : volume.real (closedBall y (2 * r)) = (2 * r) ^ d * V :=
    Measure.addHaar_real_closedBall' volume y (by positivity)
  have hvalue : (∫ x : Ω, φ x ∂ν) ≤ C * ‖v‖ ^ 2 * (r ^ d / r ^ 2) := by
    rw [hrep, distributionalLeviCLM_regularDistribution_apply]
    have hh := (le_abs_self (∫ x, u x * leviForm φ x v)).trans hpair
    apply hh.trans
    rw [hvol, mul_pow]
    dsimp only [C]
    ring_nf
    exact le_refl _
  exact hmass.trans (ENNReal.ofReal_le_ofReal hvalue)

end SGPT.NPP.DNTBig
