import SGPT.Okounkov.TranscendentalSkodaRegularization
import SGPT.Okounkov.TranscendentalSkodaSurjective
import SGPT.Foundations.Analysis.FirstPass.BTTruncations

/-!
# Local lower bounds for actual singular Skoda weights

The normal-family theorem needs a positive lower bound on a whole ball, not
just pointwise positivity.  This file constructs that bound from the actual
holomorphic tuple and psh weight, including the common zero set and poles of
the psh function.  It assumes no sequence of solutions or `L²` bound.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalSkoda

variable {n r : ℕ}

/-- Every point of the domain has a ball on which the actual singular weight
`exp(-p log |g|²) exp(-ψ)` is bounded below by a strictly positive real
constant.  The extended-nonnegative convention includes `|g| = 0` and
`ψ = -∞` without dividing by either weight. -/
theorem exists_local_lower_bound_singular_skoda_weight
    {D : Set (ComplexModel n)} (hD : IsOpen D)
    {g : Fin r → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) D)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ D)
    {p : ℝ} (hp : 0 < p) {x : ComplexModel n} (hx : x ∈ D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ ball x ρ, ENNReal.ofReal c ≤
        multiplierWeight p (generatorLog g y) * multiplierWeight 1 (ψ y) := by
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp hD x hx
  have hclosed : closedBall x (R / 2) ⊆ D :=
    (closedBall_subset_ball (by linarith)).trans hRD
  obtain ⟨C, hC0, hC⟩ := hψ.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall x (R / 2)) hclosed
  have hSc : ContinuousOn (generatorNormSq g) (closedBall x (R / 2)) :=
    (contDiffOn_generatorNormSq hD hg).continuousOn.mono hclosed
  obtain ⟨B, hB⟩ := (isCompact_closedBall x (R / 2)).exists_bound_of_continuousOn hSc
  set M : ℝ := max B 0 + 2 with hM
  have hMpos : 0 < M := by dsimp [M]; linarith [le_max_right B 0]
  have hSM : ∀ y ∈ closedBall x (R / 2), generatorNormSq g y + 1 ≤ M := by
    intro y hy
    have hb := hB y hy
    rw [Real.norm_of_nonneg (generatorNormSq_nonneg g y)] at hb
    dsimp only [M]
    linarith [le_max_left B 0]
  refine ⟨R / 2, by linarith, M ^ (-p) * Real.exp (-C), by positivity, ?_⟩
  intro y hy
  have hyK : y ∈ closedBall x (R / 2) := ball_subset_closedBall hy
  have hgen : ENNReal.ofReal (M ^ (-p)) ≤ multiplierWeight p (generatorLog g y) := by
    calc
      _ ≤ ENNReal.ofReal ((generatorNormSq g y + 1) ^ (-p)) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (by linarith [generatorNormSq_nonneg g y])
          (hSM y hyK) (by linarith)
      _ ≤ multiplierWeight p (generatorLog g y) :=
        ofReal_rpow_le_multiplierWeight g hp (by norm_num : (0 : ℝ) < 1) y
  have hpsi : ENNReal.ofReal (Real.exp (-C)) ≤ multiplierWeight 1 (ψ y) := by
    have h := multiplierWeight_antitone (c := (1 : ℝ)) (by norm_num) (hC y hyK)
    rw [multiplierWeight_coe, one_mul] at h
    exact h
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)]
  exact mul_le_mul' hgen hpsi

end SGPT.NAPotential.GAGAMult
