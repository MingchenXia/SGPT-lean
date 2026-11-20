import SGPT.Foundations.Analysis.Pending.AnalyticCoefficientLocalization
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

set_option autoImplicit false

/-! # Genuine compact analytic type supplies a uniform bounded multiplier gap -/

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.CompactAnalyticBoundedMultiplierInclusion

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.QuasiEquisingularApproximation
  AnalyticBoundedMultiplierIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine chartwise analytic type and actual compactness internally
produce a positive floor for available preferred-chart coefficients. -/
theorem exists_pos_uniform_preferred_chart_coefficient_floor
    {P : M → EReal} (hP : HasManifoldAnalyticSingularityType (n := n) P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : M, ∃ (c : ℝ) (N : ℕ) (g : Fin N → ComplexModel n → ℂ),
      δ ≤ c ∧ LogarithmicTypeAt (chartFunction P (complexChartAt (n := n) x)) c g
        ((complexChartAt (n := n) x).val x) := by
  classical
  have hlocal : ∀ x : M, ∃ c : ℝ, 0 < c ∧ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ),
        LogarithmicTypeAt (chartFunction P (complexChartAt (n := n) y)) c g
          ((complexChartAt (n := n) y).val y) := by
    intro x
    let e := complexChartAt (n := n) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    obtain ⟨c, N, g, htype⟩ := hP e (e.val x) (e.val.map_source hx)
    obtain ⟨U, hU, hxU, _, htypes⟩ :=
      AnalyticCoefficientLocalization.exists_open_preferred_chart_same_coefficient_types e hx htype
    exact ⟨(c : ℝ), htype.1, U, hU, hxU,
      fun y hy => by obtain ⟨f, hf⟩ := htypes y hy; exact ⟨N, f, hf⟩⟩
  choose c hc U hU hxU htypes using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hfinite : ∀ t : Finset M, ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ t, δ ≤ c i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i t hi ih =>
      obtain ⟨δ, hδ, hδi⟩ := ih
      refine ⟨min (c i) δ, lt_min (hc i) hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδi j hj)
  obtain ⟨δ, hδ, hδi⟩ := hfinite s
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨his, hx⟩ := mem_iUnion.mp hi
  obtain ⟨N, g, htype⟩ := htypes i x hx
  exact ⟨c i, N, g, hδi i his, htype⟩

/-- A genuinely analytic compact weight internally supplies one gap,
uniform in both the stalk and the positive target multiplier. -/
theorem exists_pos_uniform_bounded_multiplier_gap
    {P : M → EReal} (hP : HasManifoldAnalyticSingularityType (n := n) P) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : ℝ, 0 < p → ∀ q : ℝ, p + R ≤ q →
      (multiplierIdeal (n := n) q P).Le
        (boundedMultiplierIdeal (n := n) (fun y => (p : EReal) * P y)) := by
  obtain ⟨δ, hδ, htypes⟩ := exists_pos_uniform_preferred_chart_coefficient_floor hP
  let R : ℝ := (n : ℝ) / δ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro p hp q hq x h hf
  obtain ⟨c, N, g, hδc, htype⟩ := htypes x
  have hgap : R ≤ q - p := by linarith
  have hRδ : (n : ℝ) ≤ R * δ := by
    dsimp [R]
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul]
    linarith
  have hqc : (n : ℝ) ≤ (q - p) * c := by
    calc (n : ℝ) ≤ R * δ := hRδ
      _ ≤ (q - p) * δ := mul_le_mul_of_nonneg_right hgap hδ.le
      _ ≤ (q - p) * c := mul_le_mul_of_nonneg_left hδc (hR.le.trans hgap)
  exact AnalyticBoundedMultiplierChartTransfer.mem_boundedMultiplierIdeal_of_preferred_chart_analytic_type
    htype hp hqc hf

end

end SGPT.Foundations.Analysis.Pending.CompactAnalyticBoundedMultiplierInclusion
