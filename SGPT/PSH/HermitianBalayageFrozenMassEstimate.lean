import SGPT.PSH.HermitianBalayageFrozenLimit

/-!
# The actual local mass estimate for the frozen bounded extremal

The homogeneous replacement is constructed from the original extremal
competitors. Its actual gap and zero Monge--Ampère measure feed the nearby
bounded trace estimate. The remaining input error concerns only the two
explicit smooth frozen corrections.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open Hermitian HermitianExtremal
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A dimension-only coefficient controls the actual corrected extremal
mass. The canonical homogeneous replacement, its gap and its zero measure
are produced internally, and the right-hand measures use only the original
corrected extremal. -/
theorem exists_frozen_extremal_mass_estimate :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (omega : Background (m + 1) M) (K : Set M) (e : ComplexChart (m + 1) M),
        IsHermitianPSH omega (regularizedExtremal omega K) →
        ∀ S : ℝ, (∀ x, regularizedExtremal omega K x ≤ (S : EReal)) →
        ∀ (Ω : Opens (ComplexModel (m + 1))), Ω ≤ chartTarget e →
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
            ∃ hU : IsLocallyBoundedPshOn (⟨ball a r, isOpen_ball⟩ : Opens (ComplexModel (m + 1)))
                (correctedChartReader e Ω (regularizedExtremal omega K) qPlus),
              (SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure
                ⟨ball a r, isOpen_ball⟩ (correctedChartReader e Ω (regularizedExtremal omega K) qPlus)
                hU (closedBall a (r / 4))).toReal ≤
                C * κ * ∑ l ∈ Finset.range (m + 1),
                  (nearbyMixedMeasure ⟨ball a r, isOpen_ball⟩
                    (correctedChartReader e Ω (regularizedExtremal omega K) qPlus)
                    (correctedChartReader e Ω (regularizedExtremal omega K) qPlus)
                    hU hU l 0 (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_nearby_homogeneous_mass_estimate m
  refine ⟨C, hC0, ?_⟩
  intro omega K e hE S hES Ω hΩ a r κ hr hκ hκ1 hball hdisj qPlus qMinus
    hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap
  let D : Opens (ComplexModel (m + 1)) := ⟨ball a r, isOpen_ball⟩
  let U := correctedChartReader e Ω (regularizedExtremal omega K) qPlus
  have hDΩ : D ≤ Ω := fun _ hz => hball (ball_subset_closedBall hz)
  have hUreader := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne hE e hΩ
    hqPlus.contDiffOn hdomPlus (regularizedExtremal_nonneg omega K) hES
  have hU : IsLocallyBoundedPshOn D U :=
    SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hUreader.2.1 hDΩ
  obtain ⟨v, hvm, hv, hvzero, hvGap⟩ := exists_frozen_extremal_homogeneous_replacement
    omega K e hE hES hΩ a hr hball hdisj hqPlus hqMinus hdomPlus hdomMinus hqBoundary hgap
  have hsmall : closedBall a ((3 / 4 : ℝ) * r) ⊆ D :=
    closedBall_subset_ball (by linarith)
  have hclose : ∀ z ∈ closedBall a ((3 / 4 : ℝ) * r), |v z - U z| ≤ κ * r ^ 2 := by
    intro z hz
    have hg := hvGap z (hsmall hz)
    rw [abs_of_nonneg hg.1]
    exact hg.2
  have hτ := isBTLimit_canonicalBedfordTaylorMeasure hv
  have hτzero : SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure D v hv
      (ball a r) = 0 := by rw [hvzero]; simp
  have h := hC D a r κ hr hκ hκ1 hsmall U v hUreader.1 hvm hU hv hclose
    (SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure D v hv) hτ hτzero
  refine ⟨hU, ?_⟩
  simpa only [nearbyMixedMeasure_old_independent hU hv hU] using h

end SGPT.PSH.HermitianBalayage
