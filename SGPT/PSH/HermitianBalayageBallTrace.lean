import SGPT.PSH.HermitianBalayageBoundedTrace
import SGPT.PSH.HermitianBalayageCutoffs

/-!
# The nearby-potential trace recurrence on actual balls

This combines the signed bounded-current cutoff estimate with cutoffs
manufactured on concentric balls. The resulting one-slot mass inequality
has a constant depending only on dimension, bidimension and the two radius
ratios. No cutoff, derivative estimate or mass comparison is an input.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts
open scoped Topology Distributions

variable {n : ℕ}

/-- The genuine one-slot bounded trace recurrence on two concentric balls.
The cutoff and its uniform inverse-square derivative bound are produced
internally. -/
theorem exists_one_slot_ball_trace_mass_le (m : ℕ) {t₀ t₁ : ℝ}
    (ht₀ : 0 < t₀) (htt : t₀ < t₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel n)) (a : ComplexModel n) (r κ : ℝ),
        0 < r → 0 ≤ κ → closedBall a (t₁ * r) ⊆ Ω →
        ∀ (R : LocalProductCurrent n Ω (m + 1)) (hR : IsPositive R)
          (hRc : IsClosedCurrent R) (u v : ComplexModel n → ℝ),
          Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a (t₁ * r), |v x - u x| ≤ κ * r ^ 2) →
            (((isPositive_ddcMul hR hRc hv).1).traceMeasure
                (closedBall a (t₀ * r))).toReal ≤
              (((isPositive_ddcMul hR hRc hu).1).traceMeasure
                  (closedBall a (t₁ * r))).toReal +
                C * κ * (hR.traceMeasure (closedBall a (t₁ * r))).toReal := by
  obtain ⟨B, hB, hcut⟩ := exists_scaled_cutoffs (n := n) ht₀ htt
  obtain ⟨C₀, hC₀, htrace⟩ := exists_one_slot_trace_mass_le (n := n) m
  refine ⟨C₀ * B, mul_nonneg hC₀ hB, ?_⟩
  intro Ω a r κ hr hκ hball R hR hRc u v hum hvm hu hv hclose
  obtain ⟨χ, hχ1, hχs, hχ01, hχderiv⟩ := hcut a r hr Ω hball
  have hub : IsLocallyBoundedOn u Ω := by
    intro K hK hKΩ
    obtain ⟨A, -, hA⟩ := hu.exists_compact_abs_bound hK hKΩ
    exact ⟨A, hA⟩
  have hvb : IsLocallyBoundedOn v Ω := by
    intro K hK hKΩ
    obtain ⟨A, -, hA⟩ := hv.exists_compact_abs_bound hK hKΩ
    exact ⟨A, hA⟩
  have hLK : closedBall a (t₀ * r) ⊆ closedBall a (t₁ * r) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_right htt.le hr.le)
  have h := htrace Ω R hR hRc u v hum hvm hub hvb hu hv χ
    (closedBall a (t₁ * r)) (closedBall a (t₀ * r))
    (isCompact_closedBall a (t₁ * r)) hball (isCompact_closedBall a (t₀ * r)) hLK
    hχs hχ01 hχ1 (B / r ^ 2) (κ * r ^ 2)
    (div_nonneg hB (sq_nonneg r)) (mul_nonneg hκ (sq_nonneg r)) hχderiv hclose
  have hscale : C₀ * (B / r ^ 2) * (κ * r ^ 2) = (C₀ * B) * κ := by
    field_simp
  simpa only [hscale] using h

end SGPT.PSH.HermitianBalayage
