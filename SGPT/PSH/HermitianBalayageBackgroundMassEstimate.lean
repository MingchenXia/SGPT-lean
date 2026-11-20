import SGPT.PSH.HermitianBalayageBackgroundMeasure
import SGPT.PSH.HermitianBalayageCommonMassEstimate

/-!
# The actual background measure satisfies the frozen local mass estimate

The fixed measure is the literal positive Riesz trace of the original
background expansion. Genuine restriction, correction independence and
ordinary product domination connect it to the constructed frozen
homogeneous replacement and its common lower-trace comparison measure.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalBedfordTaylorLocality BedfordTaylor
open Hermitian HermitianExtremal HermitianGlobalProducts
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual fixed background patch measure satisfies the frozen local
mass bound with the actual fixed common-correction trace measure. -/
theorem exists_background_extremal_common_mass_estimate :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (omega : Background (m + 1) M) (K : Set M) (P : BackgroundPatch omega),
        ∀ hE : IsHermitianPSH omega (regularizedExtremal omega K),
        ∀ S : ℝ, ∀ hES : (∀ x, regularizedExtremal omega K x ≤ (S : EReal)),
          ContDiff ℝ ∞ P.correction →
          ∀ (Ω : Opens (ComplexModel (m + 1))), Ω ≤ P.geometry.domain →
          ∀ (a : ComplexModel (m + 1)) (r κ : ℝ), 0 < r → 0 ≤ κ → κ ≤ 1 →
            closedBall a r ⊆ Ω → Disjoint K (chartDomain P.geometry.chart (ball a r)) →
            ∀ qPlus qMinus : ComplexModel (m + 1) → ℝ,
              ContDiff ℝ ∞ qPlus → ContDiff ℝ ∞ qMinus →
              (∀ z ∈ Ω, ∀ v : ComplexModel (m + 1),
                omega.form.coeff P.geometry.chart z ![v, Complex.I • v] ≤ smoothDDC qPlus z ![v, Complex.I • v]) →
              (∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
                smoothDDC qMinus z ![v, Complex.I • v] ≤ omega.form.coeff P.geometry.chart z ![v, Complex.I • v]) →
              (∀ z ∈ sphere a r, qMinus z = qPlus z) →
              (∀ z ∈ ball a r, qMinus z - qPlus z ≤ κ * r ^ 2) →
              (∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
                smoothDDC qPlus z ![v, Complex.I • v] ≤ smoothDDC P.correction z ![v, Complex.I • v]) →
              ∃ hW : IsLocallyBoundedPshOn P.geometry.domain
                  (correctedChartReader P.geometry.chart P.geometry.domain (regularizedExtremal omega K) P.correction),
                (backgroundDiagonalMeasure P (regularizedExtremal omega K) hE
                  ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
                  (closedBall a (r / 4))).toReal ≤
                  C * κ * (oldTraceSumMeasure P.geometry.domain
                    (correctedChartReader P.geometry.chart P.geometry.domain
                      (regularizedExtremal omega K) P.correction) hW
                    (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_frozen_extremal_common_mass_estimate (m := m) (M := M)
  refine ⟨C, hC0, ?_⟩
  intro omega K P hE S hES hqP Ω hΩ a r κ hr hκ hκ1 hball hdisj qPlus qMinus
    hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap hcommon
  let E := regularizedExtremal omega K
  let hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ E x ∧ E x ≤ (b : EReal) :=
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
  let D : Opens (ComplexModel (m + 1)) := ⟨ball a r, isOpen_ball⟩
  let U := correctedChartReader P.geometry.chart Ω E qPlus
  have hDΩ : D ≤ Ω := fun _ hz => hball (ball_subset_closedBall hz)
  have hDP : D ≤ P.geometry.domain := hDΩ.trans hΩ
  obtain ⟨hU, hW, hmass⟩ := hC omega K P.geometry.chart hE S hES P.geometry.domain
    P.geometry.domain_le_target P.correction hqP P.dominates Ω hΩ a r κ hr hκ hκ1
    hball hdisj qPlus qMinus hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap hcommon
  obtain ⟨hF, hμdom⟩ := backgroundDiagonalMeasure_restrict_le_corrected P E hE hb D hDP
    qPlus hqPlus.contDiffOn (fun z hz v => hdomPlus z (hDΩ hz) v)
  have hFU : EqOn (fun z => (chartFunction E P.geometry.chart z).toReal + qPlus z) U D := by
    intro z hz
    dsimp only [U, correctedChartReader]
    rw [indicator_of_mem (hDΩ hz)]
  rw [canonicalScalarMeasure_congrOn hF hU hFU] at hμdom
  have hinner : closedBall a (r / 4) ⊆ D := closedBall_subset_ball (by linarith)
  have hμle := hμdom (closedBall a (r / 4))
  rw [Measure.restrict_apply isClosed_closedBall.measurableSet, inter_eq_left.mpr hinner] at hμle
  have hfinite := (isBTLimit_canonicalBedfordTaylorMeasure hU).2.1
    _ (isCompact_closedBall a (r / 4)) hinner
  exact ⟨hW, (ENNReal.toReal_mono hfinite.ne hμle).trans hmass⟩

end SGPT.PSH.HermitianBalayage
