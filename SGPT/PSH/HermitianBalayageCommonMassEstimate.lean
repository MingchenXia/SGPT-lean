import SGPT.PSH.HermitianBalayageFrozenMassEstimate
import SGPT.PSH.HermitianBalayageTraceMeasure

/-!
# Frozen local mass bounded by one actual fixed comparison measure

A common smooth correction dominates every frozen upper correction. The
actual smooth PSH difference increases each old trace. Canonical locality
then identifies those traces with restrictions of one fixed measure on
the larger coordinate domain, chosen before the center and radius.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalBedfordTaylorLocality
open Hermitian HermitianExtremal
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The frozen corrected-extremal mass is controlled by a single actual
fixed lower-trace measure on the larger coordinate domain. Neither trace
measure domination nor a comparison-measure certificate is assumed. -/
theorem exists_frozen_extremal_common_mass_estimate :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (omega : Background (m + 1) M) (K : Set M) (e : ComplexChart (m + 1) M),
        IsHermitianPSH omega (regularizedExtremal omega K) →
        ∀ S : ℝ, (∀ x, regularizedExtremal omega K x ≤ (S : EReal)) →
        ∀ (Ω₀ : Opens (ComplexModel (m + 1))), Ω₀ ≤ chartTarget e →
        ∀ q₀ : ComplexModel (m + 1) → ℝ, ContDiff ℝ ∞ q₀ →
          (∀ z ∈ Ω₀, ∀ v : ComplexModel (m + 1),
            omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC q₀ z ![v, Complex.I • v]) →
          ∀ (Ω : Opens (ComplexModel (m + 1))), Ω ≤ Ω₀ →
          ∀ (a : ComplexModel (m + 1)) (r κ : ℝ), 0 < r → 0 ≤ κ → κ ≤ 1 →
            closedBall a r ⊆ Ω → Disjoint K (chartDomain e (ball a r)) →
            ∀ qPlus qMinus : ComplexModel (m + 1) → ℝ,
              ContDiff ℝ ∞ qPlus → ContDiff ℝ ∞ qMinus →
              (∀ z ∈ Ω, ∀ v : ComplexModel (m + 1),
                omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC qPlus z ![v, Complex.I • v]) →
              (∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
                smoothDDC qMinus z ![v, Complex.I • v] ≤ omega.form.coeff e z ![v, Complex.I • v]) →
              (∀ z ∈ sphere a r, qMinus z = qPlus z) →
              (∀ z ∈ ball a r, qMinus z - qPlus z ≤ κ * r ^ 2) →
              (∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
                smoothDDC qPlus z ![v, Complex.I • v] ≤ smoothDDC q₀ z ![v, Complex.I • v]) →
              ∃ hU : IsLocallyBoundedPshOn (⟨ball a r, isOpen_ball⟩ : Opens (ComplexModel (m + 1)))
                  (correctedChartReader e Ω (regularizedExtremal omega K) qPlus),
                ∃ hW : IsLocallyBoundedPshOn Ω₀
                    (correctedChartReader e Ω₀ (regularizedExtremal omega K) q₀),
                  (SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure
                    ⟨ball a r, isOpen_ball⟩ (correctedChartReader e Ω (regularizedExtremal omega K) qPlus)
                    hU (closedBall a (r / 4))).toReal ≤
                    C * κ * (oldTraceSumMeasure Ω₀
                      (correctedChartReader e Ω₀ (regularizedExtremal omega K) q₀) hW
                      (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_frozen_extremal_mass_estimate (m := m) (M := M)
  refine ⟨C, hC0, ?_⟩
  intro omega K e hE S hES Ω₀ hΩ₀ q₀ hq₀ hdom₀ Ω hΩ a r κ hr hκ hκ1 hball hdisj
    qPlus qMinus hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap hcommon
  let D : Opens (ComplexModel (m + 1)) := ⟨ball a r, isOpen_ball⟩
  let U := correctedChartReader e Ω (regularizedExtremal omega K) qPlus
  let W := correctedChartReader e Ω₀ (regularizedExtremal omega K) q₀
  have hDΩ : D ≤ Ω := fun _ hz => hball (ball_subset_closedBall hz)
  have hDΩ₀ : D ≤ Ω₀ := hDΩ.trans hΩ
  have hWreader := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne hE e hΩ₀
    hq₀.contDiffOn hdom₀ (regularizedExtremal_nonneg omega K) hES
  have hW : IsLocallyBoundedPshOn Ω₀ W := hWreader.2.1
  have hWD : IsLocallyBoundedPshOn D W := isLocallyBoundedPshOn_mono hW hDΩ₀
  obtain ⟨hU, hmass⟩ := hC omega K e hE S hES Ω (hΩ.trans hΩ₀) a r κ hr hκ hκ1
    hball hdisj qPlus qMinus hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap
  have hdiff : ∀ z ∈ D, ∀ v : ComplexModel (m + 1),
      0 ≤ smoothDDC (fun y => q₀ y - qPlus y) z ![v, Complex.I • v] := by
    intro z hz v
    rw [PositiveClasses.smoothDDC_sub D.isOpen hq₀.contDiffOn hqPlus.contDiffOn hz]
    simp only [ContinuousAlternatingMap.sub_apply]
    exact sub_nonneg.mpr (hcommon z hz v)
  have hUW : ∀ z ∈ D, U z + (q₀ z - qPlus z) = W z := by
    intro z hz
    dsimp only [U, W, correctedChartReader]
    rw [indicator_of_mem (hDΩ hz), indicator_of_mem (hDΩ₀ hz)]
    ring
  have hle (l : ℕ) : nearbyMixedMeasure D U U hU hU l 0 ≤ nearbyMixedMeasure D W W hWD hWD l 0 :=
    nearbyMixedMeasure_old_le_of_smooth_difference hU hWD (hq₀.sub hqPlus).contDiffOn hdiff hUW l
  let O := closedBall a ((3 / 4 : ℝ) * r)
  have hOD : O ⊆ D := closedBall_subset_ball (by linarith)
  have hOΩ₀ : O ⊆ Ω₀ := hOD.trans hDΩ₀
  have hrestrict (l : ℕ) : nearbyMixedMeasure D W W hWD hWD l 0 O =
      nearbyMixedMeasure Ω₀ W W hW hW l 0 O := by
    have h := congrArg (fun μ : Measure (ComplexModel (m + 1)) => μ O)
      (nearbyMixedMeasure_old_restrict hW hDΩ₀ l)
    rw [Measure.restrict_apply isClosed_closedBall.measurableSet, inter_eq_left.mpr hOD] at h
    exact h.symm
  have hleR (l : ℕ) : (nearbyMixedMeasure D U U hU hU l 0 O).toReal ≤
      (nearbyMixedMeasure Ω₀ W W hW hW l 0 O).toReal := by
    have h := hle l O
    rw [hrestrict l] at h
    exact ENNReal.toReal_mono
      (nearbyMixedMeasure_finiteOnCompacts hW hW l 0 (isCompact_closedBall _ _) hOΩ₀).ne h
  refine ⟨hU, hW, ?_⟩
  apply hmass.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 hκ)
  rw [oldTraceSumMeasure_apply_toReal hW (isCompact_closedBall _ _) hOΩ₀]
  exact Finset.sum_le_sum (fun l _ => hleR l)

end SGPT.PSH.HermitianBalayage
