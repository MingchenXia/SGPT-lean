import SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization

set_option autoImplicit false

/-! # Upper pointwise Lelong bound for the actual Bergman kernel weight

Actual point extension, pole-preserving order, and finite bounded-germ invariance.
Reference: Demailly, Analytic Methods, Theorem 14.2(b).
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BergmanPointLelongUpperBound

open FirstPass FirstPass.NonKahlerLocus BergmanWeightConvergence

noncomputable section

/-- Actual point extension gives the upper bound on literal Lelong readers,
including the original poles and infinite growth suprema. -/
theorem lelongNumber_bergmanWeight_le (n : ℕ) : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R →
      ∀ D : Set (ComplexModel n), IsOpen D → Convex ℝ D → (∀ z ∈ D, ‖z‖ < R) →
      ∀ P : ComplexModel n → EReal, PlurisubharmonicOn P D →
      ∀ x ∈ D, ∀ m : ℕ, 1 ≤ m →
        lelongNumber (n := n) (bergmanWeight D P m) x ≤ lelongNumber (n := n) P x := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro R hR D hD hconv hbd P hP x hx m hm
  obtain ⟨C, _, hOT⟩ := le_bergmanWeight n R hR
  let c : ℝ := (m : ℝ)⁻¹ * Real.log C
  have hpoint : ∀ y ∈ D, P y ≤ bergmanWeight D P m y + (c : EReal) := by
    intro y hy
    by_cases hbot : P y = ⊥
    · rw [hbot]
      exact bot_le
    · have htop : P y ≠ ⊤ := (hP y hy).ne_top
      let p : ℝ := (P y).toReal
      have hp : P y = (p : EReal) := (EReal.coe_toReal htop hbot).symm
      have hlow := hOT D hD hconv hbd P hP m hm y hy p hp
      have hsum := add_le_add hlow (le_refl (c : EReal))
      have hcancel : ((p - (m : ℝ)⁻¹ * Real.log C : ℝ) : EReal) + (c : EReal) =
          (p : EReal) := by
        rw [← EReal.coe_add]
        dsimp only [c]
        rw [sub_add_cancel]
      rw [hcancel, ← hp] at hsum
      exact hsum
  have hlocal : ∀ᶠ y in 𝓝 x, P y ≤ bergmanWeight D P m y + (c : EReal) :=
    Filter.mem_of_superset (hD.mem_nhds hx) hpoint
  have hreader := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := n)
    (hlocal.filter_mono nhdsWithin_le_nhds)
  have hb : BoundedRealGermAt (fun _ : ComplexModel n => c) x :=
    boundedRealGermAt_of_continuousAt continuous_const.continuousAt
  rwa [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq hb] at hreader

end
end SGPT.Foundations.Analysis.Pending.BergmanPointLelongUpperBound
