import SGPT.Foundations.Analysis.Pending.SingularModelNormalizedMixedCutoff
import SGPT.Foundations.Analysis.FirstPass.PotentialL1

set_option autoImplicit false

/-! # Genuine chart local L1 continuity of varying finite real cutoffs -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularRealCutoffLocalLone

open FirstPass SingularModelNormalizedMixedCutoff

noncomputable section

/-- Genuine finite real cutoffs have a canonical extended difference bounded by the real parameter error, including common poles. -/
theorem canonicalAbs_realCutoff_le {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (C D : ℝ) :
    canonicalERealAbsDiff (max a (b - (C : EReal))) (max a (b - (D : EReal))) ≤
      ENNReal.ofReal |C - D| := by
  cases b with
  | bot =>
      simp only [EReal.bot_sub, max_bot_right,
        canonicalERealAbsDiff_self_of_ne_top ha]
      exact zero_le
  | top => exact (hb rfl).elim
  | coe b =>
      have hdiff : (b - C) - (b - D) = D - C := by ring
      cases a with
      | bot =>
          rw [← EReal.coe_sub, ← EReal.coe_sub, max_bot_left, max_bot_left,
            canonicalERealAbsDiff_coe_coe, hdiff, abs_sub_comm]
      | top => exact (ha rfl).elim
      | coe a =>
          have hmax (x y : ℝ) : max (x : EReal) (y : EReal) = ((max x y : ℝ) : EReal) := by
            simp only [max_def, EReal.coe_le_coe_iff]
            split_ifs <;> rfl
          rw [← EReal.coe_sub, ← EReal.coe_sub, hmax, hmax,
            canonicalERealAbsDiff_coe_coe]
          apply ENNReal.ofReal_le_ofReal
          calc
            |max a (b - C) - max a (b - D)| ≤ max |a - a| |(b - C) - (b - D)| :=
              abs_max_sub_max_le_max _ _ _ _
            _ = |C - D| := by rw [hdiff, sub_self, abs_zero, max_eq_right (abs_nonneg _), abs_sub_comm]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] {φ u : M → EReal}

/-- The actual canonical local L1 chart distance of finite real cutoffs is bounded by the scalar parameter error times the actual chart-set Haar volume. -/
theorem chartL1EDistance_realCutoff_le (hφ : ∀ x, φ x ≠ ⊤) (hu : ∀ x, u x ≠ ⊤)
    (C D : ℝ) (e : ComplexChart n M) (K : Set (ComplexModel n)) :
    chartL1EDistance (realCutoff φ u C) (realCutoff φ u D) e K ≤
      ENNReal.ofReal |C - D| * volume K := by
  rw [chartL1EDistance]
  calc
    (∫⁻ z in K, canonicalERealAbsDiff (chartFunction (realCutoff φ u C) e z)
        (chartFunction (realCutoff φ u D) e z) ∂volume) ≤
        ∫⁻ _z in K, ENNReal.ofReal |C - D| ∂volume := by
      apply lintegral_mono
      intro z
      exact canonicalAbs_realCutoff_le (hu (e.val.symm z)) (hφ (e.val.symm z)) C D
    _ = ENNReal.ofReal |C - D| * volume K := by
      rw [lintegral_const]
      simp

/-- Every genuinely convergent finite real parameter family produces actual chart local L1 convergence of its genuine cutoffs, without a cutoff-limit or integrability premise. -/
theorem manifoldL1LocallyTendsto_realCutoff {α : Type*} {l : Filter α}
    (hφ : ∀ x, φ x ≠ ⊤) (hu : ∀ x, u x ≠ ⊤) {c : α → ℝ} {D : ℝ}
    (hc : Tendsto c l (𝓝 D)) :
    ManifoldL1LocallyTendsto (n := n) (fun i => realCutoff φ u (c i)) l (realCutoff φ u D) := by
  intro e K hK _
  have hreal : Tendsto (fun i => |c i - D|) l (𝓝 0) := by
    simpa using (hc.sub_const D).abs
  have hscalar : Tendsto (fun i => ENNReal.ofReal |c i - D|) l (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hbound : Tendsto (fun i => ENNReal.ofReal |c i - D| * volume K) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hscalar (Or.inr hK.measure_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) (fun i => chartL1EDistance_realCutoff_le hφ hu (c i) D e K)

end

end SGPT.Foundations.Analysis.Pending.SingularRealCutoffLocalLone
