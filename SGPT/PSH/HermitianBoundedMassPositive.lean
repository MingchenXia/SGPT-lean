import SGPT.PSH.HermitianConstantComparison
import SGPT.PSH.HermitianComparisonPureAbsorption

/-!
# Positive mass of every actual bounded Hermitian PSH potential

The concrete pure-trace comparison is applied on a manufactured nonempty
open sublevel. The original smooth background measure has positive mass
there, forcing positivity of the bounded potential's canonical mass.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianComparisonSublevel

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- Every actual bounded Hermitian PSH potential has strictly positive real
canonical Monge--Ampère mass. Only original class membership and real
bounds are assumed. -/
theorem globalMixedMeasure_diagonal_mass_toReal_pos
    (omega : Background (m + 1) M) {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    0 < (globalMixedMeasure omega (fun _ => u) (fun _ => hu) (fun _ => hb) univ).toReal := by
  obtain ⟨δ, hδ, hcompare⟩ := HermitianComparison.exists_constant_comparison_gap omega
  obtain ⟨c, hEopen, hEne, hgap⟩ := exists_small_hermitian_sublevel hu hb hδ
  let E := {x | u x < (c : EReal)}
  let μ := globalMixedMeasure omega (fun _ => u) (fun _ => hu) (fun _ => hb)
  have hvol := zero_globalMixedMeasure_open_toReal_pos omega hEopen hEne
  have hle := hcompare u hu hb c (fun x hx => (hgap x hx).2)
  have hproduct : 0 < (4 : ℝ) ^ (m + 1) * (μ E).toReal := hvol.trans_le hle
  have hEpos : 0 < (μ E).toReal := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (4 : ℝ) ^ (m + 1) by positivity) (le_of_not_gt hn)
    exact (not_lt_of_ge hnonpos) hproduct
  let _ := globalMixedMeasure_isFiniteMeasure (omega := omega)
    (fun _ => u) (fun _ => hu) (fun _ => hb)
  exact hEpos.trans_le (ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ E)))

/-- Every actual bounded Hermitian PSH potential has strictly positive
canonical global Monge--Ampère mass. -/
theorem globalMixedMeasure_diagonal_mass_pos
    (omega : Background (m + 1) M) {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    0 < globalMixedMeasure omega (fun _ => u) (fun _ => hu) (fun _ => hb) univ := by
  by_contra hn
  have hzero : globalMixedMeasure omega (fun _ => u) (fun _ => hu) (fun _ => hb) univ = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  have hpos := globalMixedMeasure_diagonal_mass_toReal_pos omega hu hb
  rw [hzero, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

end SGPT.PSH.HermitianGlobalProducts
