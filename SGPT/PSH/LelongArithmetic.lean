import SGPT.PSH.VariableLelong
import SGPT.Okounkov.LocalLelong
import SGPT.Okounkov.FlagLelong
import SGPT.Foundations.Analysis.Pending.DivisorialSliceBound

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization

/-- Genuine logarithmic bounds manufacture the maximum reader, without any analytic certificate. -/
theorem lelongNumber_max_eq {m : ℕ} (u v : ComplexModel (m + 1) → EReal)
    (x : ComplexModel (m + 1)) :
    lelongNumber (n := m + 1) (fun y => max (u y) (v y)) x =
      min (lelongNumber (n := m + 1) u x) (lelongNumber (n := m + 1) v x) := by
  apply le_antisymm
  · exact le_min
      (KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall fun y => le_max_left (u y) (v y)))
      (KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall fun y => le_max_right (u y) (v y)))
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    obtain ⟨a, ha, C, hC⟩ := DivisorialSliceBound.exists_admissible_of_lt_lelongNumber
      ((lt_min_iff.mp hr).1)
    obtain ⟨b, hb, D, hD⟩ := DivisorialSliceBound.exists_admissible_of_lt_lelongNumber
      ((lt_min_iff.mp hr).2)
    have hO : IsOpen {y : ComplexModel (m + 1) | ‖y - x‖ < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have hx : x ∈ {y : ComplexModel (m + 1) | ‖y - x‖ < 1} := by simp
    have hbound : ∀ᶠ y in 𝓝[≠] x,
        max (u y) (v y) ≤ (((r : ℝ) * Real.log ‖y - x‖ + max C D : ℝ) : EReal) := by
      filter_upwards [hC, hD, eventually_nhdsWithin_of_eventually_nhds (hO.mem_nhds hx)]
        with y hyu hyv hyr
      have hlog := Real.log_nonpos (norm_nonneg (y - x)) hyr.le
      apply max_le
      · exact hyu.trans (EReal.coe_le_coe (by
          linarith [mul_le_mul_of_nonpos_right ha.le hlog, le_max_left C D]))
      · exact hyv.trans (EReal.coe_le_coe (by
          linarith [mul_le_mul_of_nonpos_right hb.le hlog, le_max_right C D]))
    have h := LelongNumberChartTransport.ofReal_le_lelongNumber
      (n := m + 1) (x := x) (u := fun y => max (u y) (v y)) (r.coe_nonneg)
      (C := max C D) (by
        simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
          using hbound)
    simpa only [ENNReal.ofReal_coe_nnreal] using h

/-- Source maximum arithmetic includes its literal zero-dimensional branch. -/
theorem squaredLogLelongNumber_max_eq {n : ℕ} (u v : ComplexModel n → EReal)
    (x : ComplexModel n) :
    squaredLogLelongNumber (n := n) (fun y => max (u y) (v y)) x =
      min (squaredLogLelongNumber (n := n) u x) (squaredLogLelongNumber (n := n) v x) := by
  cases n with
  | zero => simp only [squaredLogLelongNumber, ite_true, min_self]
  | succ m =>
      apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
      have hmin (a b : ℝ≥0∞) : 2 * min a b = min (2 * a) (2 * b) := by
        rcases le_total a b with h | h
        · have hm : 2 * a ≤ 2 * b := by gcongr
          rw [min_eq_left h, min_eq_left hm]
        · have hm : 2 * b ≤ 2 * a := by gcongr
          rw [min_eq_right h, min_eq_right hm]
      rw [hmin, ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
        ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
        ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
      exact lelongNumber_max_eq u v x

/-- Genuine open-submanifold restriction preserves the independently defined source reader. -/
theorem squaredLogLelongNumber_opens_restrict {n : ℕ} {Ω : Opens (ComplexModel n)}
    (u : ComplexModel n → EReal) (x : Ω) :
    squaredLogLelongNumber (n := n) (fun y : Ω => u y) x =
      squaredLogLelongNumber (n := n) u x := by
  by_cases hn : n = 0
  · simp only [squaredLogLelongNumber, hn, ite_true]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, ← lelongNumber_eq_two_mul_squaredLog hn]
  exact SGPT.Okounkov.lelongNumber_opens_restrict u x

/-- Actual source PSH germs supply the genuine subtype hypotheses of existing native additivity. -/
theorem squaredLogLelongNumber_add_eq_on {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v Ω) (x : Ω) :
    squaredLogLelongNumber (n := n) (fun y => u y + v y) x =
      squaredLogLelongNumber (n := n) u x + squaredLogLelongNumber (n := n) v x := by
  have hu' := SGPT.Okounkov.manifoldQuasiPlurisubharmonic_opens_restrict
    (fun y hy => (hu y hy).quasiPlurisubharmonicAt)
  have hv' := SGPT.Okounkov.manifoldQuasiPlurisubharmonic_opens_restrict
    (fun y hy => (hv y hy).quasiPlurisubharmonicAt)
  have h := SGPT.Okounkov.squaredLogLelongNumber_add_eq hu' hv' x
  rw [squaredLogLelongNumber_opens_restrict (fun y => u y + v y) x,
    squaredLogLelongNumber_opens_restrict u x,
    squaredLogLelongNumber_opens_restrict v x] at h
  exact h

/-- The original point reader of a maximum is the minimum, in every true source chart. -/
theorem sourceLelong_max_eq {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u v : X → EReal) (x : X) :
    A.sourceLelong (fun y => max (u y) (v y)) x =
      min (A.sourceLelong u x) (A.sourceLelong v x) := by
  obtain ⟨i, hi⟩ := A.cover x
  rw [A.sourceLelong_eq_chart _ x i hi, A.sourceLelong_eq_chart u x i hi,
    A.sourceLelong_eq_chart v x i hi]
  exact squaredLogLelongNumber_max_eq (A.coordinate u i) (A.coordinate v i) (A.chart i x)

/-- Source PSH functions supply all local conditions internally; no global background is needed. -/
theorem sourceLelong_add_eq {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) {u v : X → EReal}
    (hu : A.IsPSH u) (hv : A.IsPSH v) (x : X) :
    A.sourceLelong (fun y => u y + v y) x = A.sourceLelong u x + A.sourceLelong v x := by
  obtain ⟨i, hi⟩ := A.cover x
  rw [A.sourceLelong_eq_chart _ x i hi, A.sourceLelong_eq_chart u x i hi,
    A.sourceLelong_eq_chart v x i hi]
  let Ω : Opens (ComplexModel (A.dimension i)) := ⟨(A.chart i).target, (A.chart i).open_target⟩
  let z : Ω := ⟨A.chart i x, (A.chart i).map_source hi⟩
  exact squaredLogLelongNumber_add_eq_on (Ω := Ω)
    (hu.chartPlurisubharmonic i) (hv.chartPlurisubharmonic i) z

/-- Existing genuine source scaling supplies every nonnegative scalar, including zero and poles. -/
theorem sourceLelong_nonneg_smul_eq {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (u : X → EReal) (x : X) {c : ℝ} (hc : 0 ≤ c) :
    A.sourceLelong (fun y => (c : EReal) * u y) x = ENNReal.ofReal c * A.sourceLelong u x := by
  obtain ⟨i, hi⟩ := A.cover x
  rw [A.sourceLelong_eq_chart _ x i hi, A.sourceLelong_eq_chart u x i hi]
  exact SGPT.Okounkov.squaredLogLelongNumber_nonneg_smul_eq (A.coordinate u i) (A.chart i x) hc

end SGPT.PSH.VariableComplexAtlas
