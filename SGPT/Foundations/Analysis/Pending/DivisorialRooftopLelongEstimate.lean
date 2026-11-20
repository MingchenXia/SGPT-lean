import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.LelongNumberAdditivity
import SGPT.Foundations.Analysis.Pending.UniformLelongBound
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Uniform actual generic Lelong estimates from genuine Rooftop barriers -/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DivisorialRooftopLelongEstimate

open FirstPass FirstPass.NonKahlerLocus DemaillyApproximantDivisorialLelong
  ActualLelongPositiveScaling

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

private theorem point_estimate {θ : ClosedRealOneOneForm (m + 1) Y}
    {h u ψ : Y → EReal} (hh : IsThetaPshPotential θ.val h)
    (hψ : IsThetaPshPotential θ.val ψ) {B : ℝ}
    (hB : ∀ x, lelongNumber (n := m + 1) h x ≤ ENNReal.ofReal B)
    {C : ℕ} (hC : 2 ≤ C)
    (hbar : ∀ x, h x + (((C - 1 : ℕ) : ℝ) : EReal) * ψ x ≤ ((C : ℝ) : EReal) * u x)
    (x : Y) :
    ENNReal.ofReal (C : ℝ) * lelongNumber (n := m + 1) u x ≤
      ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * lelongNumber (n := m + 1) ψ x := by
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (by omega : 0 < C)
  have hCm1 : 0 < ((C - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < C - 1)
  have hs := RestrictedApproximantComparison.isThetaPshPotential_smul hψ hCm1
  have ho : lelongNumber (n := m + 1) (fun y => ((C : ℝ) : EReal) * u y) x ≤
      lelongNumber (n := m + 1) (fun y => h y + (((C - 1 : ℕ) : ℝ) : EReal) * ψ y) x :=
    KahlerCurrentMax.lelongNumber_le_of_eventually_le (Eventually.of_forall hbar)
  rw [lelongNumber_smul_eq hCpos] at ho
  have hadd := LelongNumberAdditivity.lelongNumber_add_le
    hh.1.quasiPlurisubharmonic hs.1.quasiPlurisubharmonic x
  rw [lelongNumber_smul_eq hCm1] at hadd
  exact ho.trans (hadd.trans (add_le_add (hB x) le_rfl))

/-- The compact uniform Lelong constant is selected before all genuine
barriers and all sets; the generic infimum transport uses no common minimizer. -/
theorem exists_uniform_divisorial_rooftop_estimate [CompactSpace Y]
    (θ : ClosedRealOneOneForm (m + 1) Y) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {h u ψ : Y → EReal}, IsThetaPshPotential θ.val h →
        IsThetaPshPotential θ.val ψ → ∀ {C : ℕ}, 2 ≤ C →
        (∀ x, h x + (((C - 1 : ℕ) : ℝ) : EReal) * ψ x ≤ ((C : ℝ) : EReal) * u x) →
        ∀ E : Set Y,
          ENNReal.ofReal (C : ℝ) * divisorialLelongNumber m u E ≤
            ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * divisorialLelongNumber m ψ E := by
  obtain ⟨N, hN⟩ := UniformLelongBound.hasUniformLelongBound (Nat.succ_pos m) θ
  refine ⟨max N 0, le_max_right _ _, ?_⟩
  intro h u ψ hh hψ C hC hbar E
  have hBh (x : Y) : lelongNumber (n := m + 1) h x ≤ ENNReal.ofReal (max N 0) :=
    (hN h hh x).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hpoint := point_estimate hh hψ hBh hC hbar
  have hCm1 : 0 < ((C - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < C - 1)
  have hDm0 : ENNReal.ofReal ((C - 1 : ℕ) : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hCm1).ne'
  change ENNReal.ofReal (C : ℝ) * divisorialLelongNumber m u E ≤
    ENNReal.ofReal (max N 0) + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) *
      (⨅ x ∈ E, lelongNumber (n := m + 1) ψ x)
  simp_rw [ENNReal.mul_iInf_of_ne hDm0 ENNReal.ofReal_ne_top, ENNReal.add_iInf]
  refine le_iInf fun x => le_iInf fun hx => ?_
  calc ENNReal.ofReal (C : ℝ) * divisorialLelongNumber m u E ≤
      ENNReal.ofReal (C : ℝ) * lelongNumber (n := m + 1) u x := by
        gcongr
        exact divisorialLelongNumber_le hx
    _ ≤ _ := hpoint x

end
end SGPT.Foundations.Analysis.Pending.DivisorialRooftopLelongEstimate
