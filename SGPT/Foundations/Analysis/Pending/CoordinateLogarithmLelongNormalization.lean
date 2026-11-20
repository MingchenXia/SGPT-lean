import SGPT.Foundations.Analysis.Pending.LelongNumberScaling
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities

set_option autoImplicit false

/-! # Literal coordinate logarithms and bounded real remainder invariance

Direct computations in the actual logarithmic-growth reader. A coordinate
index supplies positive dimension; bounded real perturbations need no
plurisubharmonicity or finite-value assumption.
Reference: Xia, singularity comparison; Demailly, CADG, logarithmic growth.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization

open FirstPass FirstPass.NonKahlerLocus LelongNumberChartTransport

noncomputable section

/-- Any bounded real germ preserves the actual logarithmic-growth reader,
including all infinite values and the zero-dimensional punctured filter. -/
theorem lelongNumber_add_bounded_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {u : M → EReal} {b : M → ℝ} {x : M}
    (hb : BoundedRealGermAt b x) :
    lelongNumber (n := n) (fun y => u y + (b y : EReal)) x =
      lelongNumber (n := n) u x := by
  obtain ⟨C, _, hC⟩ := hb
  have hplus : ∀ᶠ y in 𝓝[≠] x, (b y : EReal) ≤ (C : EReal) :=
    (hC.mono fun y hy => EReal.coe_le_coe_iff.mpr (abs_le.mp hy).2).filter_mono
      nhdsWithin_le_nhds
  have hminus : ∀ᶠ y in 𝓝[≠] x, ((-b y : ℝ) : EReal) ≤ (C : EReal) :=
    (hC.mono fun y hy => EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp hy).1])).filter_mono
      nhdsWithin_le_nhds
  have hcancel : (fun y => (u y + (b y : EReal)) + ((-b y : ℝ) : EReal)) = u := by
    funext y
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  exact le_antisymm
    (by simpa only [hcancel] using
      (LelongNumberScaling.lelongNumber_le_add_of_eventually_le_const (n := n)
        (u := fun y => u y + (b y : EReal)) (x := x) hminus))
    (LelongNumberScaling.lelongNumber_le_add_of_eventually_le_const (n := n) (u := u) hplus)

/-- A genuine coordinate supplies its own positive-dimensional axis and
has exact coefficient one in the literal logarithmic-growth reader. -/
theorem lelongNumber_coordinate_log_eq_one {n : ℕ} (j : Fin n) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z j‖)) 0 = 1 := by
  classical
  apply le_antisymm
  · have hup : lelongNumber (n := n)
        (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z j‖)) 0 ≤
        ENNReal.ofReal (1 : ℝ) := by
      apply lelongNumber_le_ofReal
      intro γ hγ
      by_contra hnot
      have hγpos : 0 < (γ : ℝ) - 1 := sub_pos.mpr (lt_of_not_ge hnot)
      obtain ⟨C, hC⟩ := hγ
      obtain ⟨ρ, hρ, hbound⟩ := exists_chart_radius_of_eventually (n := n) hC
      let T : ℝ := |C| / ((γ : ℝ) - 1) + |Real.log ρ| + 1
      let t : ℝ := Real.exp (-T)
      have hTC : C < ((γ : ℝ) - 1) * T := by
        have habs : C ≤ |C| := le_abs_self C
        have hdiv : ((γ : ℝ) - 1) * (|C| / ((γ : ℝ) - 1)) = |C| := by
          field_simp
        dsimp only [T]
        nlinarith [abs_nonneg (Real.log ρ)]
      have hTρ : -T < Real.log ρ := by
        have hdiv : 0 ≤ |C| / ((γ : ℝ) - 1) := div_nonneg (abs_nonneg _) hγpos.le
        have hlog := neg_abs_le (Real.log ρ)
        dsimp only [T]
        linarith
      have ht : 0 < t := Real.exp_pos _
      have htρ : t < ρ := by
        rw [← Real.exp_log hρ]
        exact Real.exp_lt_exp.mpr hTρ
      let v : ComplexModel n := PiLp.single 2 j (t : ℂ)
      have hnorm : ‖v‖ = t := by
        simp [v, Complex.norm_real, abs_of_pos ht]
      have hvj : v j = (t : ℂ) := by simp [v]
      have hv0 : 0 < ‖v - (complexChartAt (n := n) (0 : ComplexModel n)).val 0‖ := by
        simpa [complexChartAt, chartAt_self_eq, hnorm] using ht
      have hvρ : ‖v - (complexChartAt (n := n) (0 : ComplexModel n)).val 0‖ < ρ := by
        simpa [complexChartAt, chartAt_self_eq, hnorm] using htρ
      have h := (hbound v hv0 hvρ).2
      have hreal : Real.log t ≤ (γ : ℝ) * Real.log t + C := by
        have he : ENNReal.log (ENNReal.ofReal t) ≤
            (((γ : ℝ) * Real.log t + C : ℝ) : EReal) := by
          simpa [complexChartAt, chartAt_self_eq, hvj, hnorm,
            Complex.norm_real, abs_of_pos ht] using h
        rwa [ENNReal.log_ofReal_of_pos ht, EReal.coe_le_coe_iff] at he
      have hlogt : Real.log t = -T := Real.log_exp _
      rw [hlogt] at hreal
      nlinarith
    simpa only [ENNReal.ofReal_one] using hup
  · have hlo : ENNReal.ofReal (1 : ℝ) ≤ lelongNumber (n := n)
        (fun z : ComplexModel n => ENNReal.log (ENNReal.ofReal ‖z j‖)) 0 := by
      apply ofReal_le_lelongNumber (by norm_num : (0 : ℝ) ≤ 1) (C := 0)
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z j = 0
      · simp [hz]
      have hzpos : 0 < ‖z j‖ := norm_pos_iff.mpr hz
      have hlog := Real.log_le_log hzpos (PiLp.norm_apply_le z j)
      simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq,
        sub_zero, one_mul, add_zero]
      change ENNReal.log (ENNReal.ofReal ‖z j‖) ≤ (Real.log ‖z‖ : EReal)
      rw [ENNReal.log_ofReal_of_pos hzpos]
      exact EReal.coe_le_coe_iff.mpr hlog
    simpa only [ENNReal.ofReal_one] using hlo

end
end SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
