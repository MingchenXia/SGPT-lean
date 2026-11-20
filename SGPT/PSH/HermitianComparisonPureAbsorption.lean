import SGPT.PSH.HermitianComparisonPureErrorAbsorption
import SGPT.PSH.HermitianComparisonPureTraces
import SGPT.PSH.HermitianComparisonPureRecurrence
import SGPT.PSH.HermitianVolumePositive

/-! The concrete small-gap pure-trace absorption used for Global Josefson.
Only constant competitors are needed for bounded positive total mass. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparison

open Set TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianExtremal HermitianComparisonPureTraces
  HermitianComparisonPureErrorAbsorption

/-- The gap is fixed by geometry and dimension before all potentials. -/
def constantComparisonGap (B : ℝ) (N : ℕ) : ℝ := 1 / (2 * (B+1) * (N : ℝ)^2)

theorem constantComparisonGap_pos {B : ℝ} {N : ℕ} (hB : 0 ≤ B) (hN : 0 < N) :
    0 < constantComparisonGap B N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold constantComparisonGap
  positivity

theorem constantComparisonGap_small {B : ℝ} {N : ℕ} (hB : 0 ≤ B) (hN : 0 < N) :
    constantComparisonGap B N * B * (N : ℝ)^2 ≤ (1/2 : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hBp : 0 < B+1 := by linarith
  have he : constantComparisonGap B N * B * (N : ℝ)^2 = B / (2*(B+1)) := by
    unfold constantComparisonGap
    field_simp
  rw [he]
  apply (div_le_iff₀ (show 0 < 2*(B+1) by positivity)).mpr
  linarith

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

/-- The literal source strict-set gap is a global positive-part bound,
using the genuine everywhere finite representatives supplied by boundedness. -/
theorem positivePart_gap_of_strict_gap {omega : Background (m+1) M}
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (c δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ x ∈ {x | u x < (c : EReal)}, c - (u x).toReal ≤ δ) :
    ∀ x, max (c - (u x).toReal) 0 ≤ δ := by
  obtain ⟨a,b,hab⟩ := hb
  intro x
  by_cases hx : u x < (c : EReal)
  · exact max_le (hgap x hx) hδ
  · have hbot : u x ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab x).1)
    have he : (c : EReal) ≤ (((u x).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal (hu.ne_top x) hbot]
      exact le_of_not_gt hx
    have hr : c ≤ (u x).toReal := EReal.coe_le_coe_iff.mp he
    rw [max_eq_right (by linarith : c - (u x).toReal ≤ 0)]
    exact hδ

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The concrete comparison needed for positive bounded total mass. Its
gap is chosen uniformly from the actual background geometry. The full
pure-trace recurrence and all analytic estimates are produced internally. -/
theorem exists_constant_comparison_gap (omega : Background (m+1) M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (u : M → EReal) (hu : IsHermitianPSH omega u)
        (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
        (c : ℝ),
        (∀ x ∈ {x | u x < (c : EReal)}, c - (u x).toReal ≤ δ) →
        (globalMixedMeasure omega (fun _ _ => (0 : EReal))
          (fun _ => isHermitianPSH_zero omega)
          (fun _ => ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩)
          {x | u x < (c : EReal)}).toReal ≤
        (4 : ℝ) ^ (m+1) *
          (globalMixedMeasure omega (fun _ => u) (fun _ => hu) (fun _ => hb)
            {x | u x < (c : EReal)}).toReal := by
  obtain ⟨B, hB, hrec⟩ := exists_uniform_pure_recurrence omega
  let δ := constantComparisonGap B (m+1)
  have hδ : 0 < δ := constantComparisonGap_pos hB (Nat.succ_pos m)
  refine ⟨δ, hδ, ?_⟩
  intro u hu hb c hgap
  have hglobal := positivePart_gap_of_strict_gap hu hb c δ hδ.le hgap
  have h := zero_le_four_pow_mul_top (Nat.succ_pos m)
    (a := fun k => pureTraceMass omega hu hb {x | u x < (c : EReal)} k)
    (ε := δ * B)
    (fun k _ => pureTraceMass_nonneg hu hb _ k)
    (mul_nonneg hδ.le hB)
    (constantComparisonGap_small hB (Nat.succ_pos m))
    (hrec u hu hb c δ hδ.le hglobal)
  simpa only [pureTraceMass, pureTraceMeasure_zero, pureTraceMeasure_top] using h

end SGPT.PSH.HermitianComparison
