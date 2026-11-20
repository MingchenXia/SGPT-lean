import SGPT.Foundations.Analysis.Pending.LelongNumberAdditivity
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

set_option autoImplicit false

/-! # Literal pointwise arithmetic of the actual logarithmic Lelong exponent -/

open Set Filter
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLelongAdditivity

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem exists_eventually_le_const {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (x : M) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x, u y ≤ (C : EReal) := by
  obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr (hu.ne_top x))
  exact ⟨C, ((hu.upperSemicontinuous x _ hC).mono fun _ hy => hy.le).filter_mono
    nhdsWithin_le_nhds⟩

/-- Actual local upper bounds internally make both exponent sets nonempty;
two true logarithmic bounds then add before either supremum is taken. -/
theorem lelongNumber_add_ge {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : M) :
    lelongNumber (n := n) u x + lelongNumber (n := n) v x ≤
      lelongNumber (n := n) (fun y => u y + v y) x := by
  let P (w : M → EReal) (a : ℝ≥0) : Prop :=
    ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x, w y ≤
      (((a : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal)
  obtain ⟨Cu, hCu⟩ := exists_eventually_le_const hu x
  obtain ⟨Cv, hCv⟩ := exists_eventually_le_const hv x
  have hPu : ∃ a, P u a := ⟨0, Cu, by simpa only [P, NNReal.coe_zero, zero_mul,
    zero_add] using hCu⟩
  have hPv : ∃ a, P v a := ⟨0, Cv, by simpa only [P, NNReal.coe_zero, zero_mul,
    zero_add] using hCv⟩
  change (⨆ a : ℝ≥0, ⨆ _ : P u a, (a : ℝ≥0∞)) +
    (⨆ b : ℝ≥0, ⨆ _ : P v b, (b : ℝ≥0∞)) ≤ _
  apply ENNReal.biSup_add_biSup_le' hPu hPv
  intro a ha b hb
  obtain ⟨C, hC⟩ := ha
  obtain ⟨D, hD⟩ := hb
  have hab : P (fun y => u y + v y) (a + b) := by
    refine ⟨C + D, ?_⟩
    filter_upwards [hC, hD] with y hy hz
    calc
      u y + v y ≤
          (((a : ℝ) * Real.log
            ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal) +
          (((b : ℝ) * Real.log
            ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + D : ℝ) : EReal) :=
        add_le_add hy hz
      _ = _ := by rw [← EReal.coe_add]; congr 1; simp only [NNReal.coe_add]; ring
  change (a : ℝ≥0∞) + (b : ℝ≥0∞) ≤
    ⨆ c : ℝ≥0, ⨆ _ : P (fun y => u y + v y) c, (c : ℝ≥0∞)
  simpa only [ENNReal.coe_add] using
    (le_iSup₂_of_le (f := fun (c : ℝ≥0) (_ : P (fun y => u y + v y) c) =>
      (c : ℝ≥0∞)) (a + b) hab le_rfl)

/-- The actual point Lelong value is exactly additive, including all
infinite values and the zero-dimensional punctured-filter branch. -/
theorem lelongNumber_add_eq {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : M) :
    lelongNumber (n := n) (fun y => u y + v y) x =
      lelongNumber (n := n) u x + lelongNumber (n := n) v x :=
  le_antisymm (LelongNumberAdditivity.lelongNumber_add_le hu hv x)
    (lelongNumber_add_ge hu hv x)

end
end SGPT.Foundations.Analysis.Pending.ActualLelongAdditivity
