import SGPT.Foundations.Analysis.Pending.ActualMixedMassAdmissibleBarrier
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false

/-! # Actual fixed admissible mass control after a maximum

SGPT PDF0240--0241 Step 3 of Proposition 6.2.4, with an independent
fixed-weight adaptation. The natural admissible diagonal mass gap
internally produces the true barrier and the actual maximum mass bound.
General maximum continuity remains a subsequent obligation.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMaximumMassAdmissibleBarrier

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass
  ThetaPshConvexCombination ConvexCombEnvelopeMass GlobalDiagonalConvexScaling
  GlobalMixedMassMonotone

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- An actual admissible diagonal mass gap internally produces the PSH
barrier and the genuine quantitative mass comparison after a maximum. -/
theorem diagonalPotentialMass_max_le_of_admissibleWeight
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {φ ψ χ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) (hχ : IsThetaPshPotential θ.val χ)
    (hle : φ ≤ ψ) (hpos : 0 < diagonalPotentialMass θ φ hφ) {b : ℝ}
    (hb : IsAdmissibleWeight n (diagonalPotentialMass θ φ hφ)
      (diagonalPotentialMass θ ψ hψ) b) :
    ENNReal.ofReal ((1 - b⁻¹) ^ n) * diagonalPotentialMass θ
        (fun x => max (ψ x) (χ x)) (IsThetaPshPotential.max hψ hχ) ≤
      diagonalPotentialMass θ (fun x => max (φ x) (χ x))
        (IsThetaPshPotential.max hφ hχ) := by
  obtain ⟨ρ, hρ, hbar⟩ := exists_thetaPsh_convexCombBarrier omega θ hφ hψ hle hpos hb
  have hρφ : ρ ≤ φ := competitor_le_left hφ hψ hle hb.one_lt
    (mem_rooftopCompetitors_of_barrier hψ hb.one_lt hρ hbar)
  let t : ℝ := 1 - b⁻¹
  have ht0 : 0 < t := sub_pos.mpr (inv_lt_one_of_one_lt₀ hb.one_lt)
  have ht1 : t < 1 := sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans hb.one_lt))
  have hbar' : convexComb t ψ ρ ≤ φ := by
    rw [convexComb_symm t ψ ρ]
    simpa only [t, sub_sub_cancel] using hbar
  let A : M → EReal := fun x => max (φ x) (χ x)
  let B : M → EReal := fun x => max (ψ x) (χ x)
  have hA : IsThetaPshPotential θ.val A := IsThetaPshPotential.max hφ hχ
  have hB : IsThetaPshPotential θ.val B := IsThetaPshPotential.max hψ hχ
  have hbound : convexComb t B ρ ≤ A := by
    have hχA : convexComb t χ ρ ≤ A := by
      have h := convexComb_mono ht0.le ht1.le (fun x => le_max_right (φ x) (χ x))
        (fun x => (hρφ x).trans (le_max_left (φ x) (χ x)))
      simpa only [ThetaCapacity.convexComb_self ht0 ht1] using h
    intro x
    by_cases hx : ψ x ≤ χ x
    · simpa only [convexComb, B, max_eq_right hx] using hχA x
    · have h := (hbar' x).trans (le_max_left (φ x) (χ x))
      simpa only [convexComb, B, max_eq_left (le_of_not_ge hx)] using h
  have hW : IsThetaPshPotential θ.val (convexComb t B ρ) :=
    isThetaPshPotential_convexComb hB hρ ht0 ht1
  have hlow := globalMixedMeasure_diagonal_convexComb_le hB hρ ht0 ht1 univ
  have hhigh := globalMixedMass_mono_of_isThetaPshPotential omega
    (fun _ : Fin n => hW) (fun _ : Fin n => hA)
    (fun _ => MoreSingularOn.of_le fun x _ => hbound x)
  exact hlow.trans hhigh

end
end SGPT.Foundations.Analysis.Pending.ActualMaximumMassAdmissibleBarrier
