import SGPT.Foundations.Analysis.Pending.SingularBoundaryCompetitor
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

set_option autoImplicit false

/-! # Actual chart maximum modification of singular Perron curves -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPerronChartModification

open FirstPass FiniteGeodesicMaximality SingularBoundaryCompetitor

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The actual manifold-point modification by an actual extended-real chart competitor. -/
def boundaryModification (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (D : Set (ComplexModel n × ℂ))
    (v : ComplexModel n × ℂ → EReal) : M → ℂ → EReal := by
  classical
  exact fun x τ => if x ∈ e.val.source ∧ (e.val x, τ) ∈ D then
    max (curve τ.re x) (v (e.val x, τ) - (ρ (e.val x) : EReal))
    else curve τ.re x

/-- The actual maximum modification dominates the actual original complexified curve, including poles. -/
theorem boundaryModification_ge (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (D : Set (ComplexModel n × ℂ))
    (v : ComplexModel n × ℂ → EReal) (x : M) (τ : ℂ) :
    curve τ.re x ≤ boundaryModification curve e ρ D v x τ := by
  classical
  by_cases hx : x ∈ e.val.source ∧ (e.val x, τ) ∈ D
  · simp only [boundaryModification, if_pos hx]
    exact le_max_left _ _
  · simp only [boundaryModification, if_neg hx, le_refl]

/-- Outside the actual chart modification condition, the actual function agrees with the original curve. -/
theorem boundaryModification_eq_outside (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (D : Set (ComplexModel n × ℂ))
    (v : ComplexModel n × ℂ → EReal) {x : M} {τ : ℂ}
    (hx : ¬ (x ∈ e.val.source ∧ (e.val x, τ) ∈ D)) :
    boundaryModification curve e ρ D v x τ = curve τ.re x := by
  simp only [boundaryModification, if_neg hx]

/-- The corrected actual chart modification is precisely actual boundary maximum pasting; finite translations retain pole values. -/
theorem corrected_boundaryModification_apply (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (D : Set (ComplexModel n × ℂ))
    (v : ComplexModel n × ℂ → EReal) (p : ComplexModel n × ℂ)
    (hp : p.1 ∈ e.val.target) :
    stripChartFunction (boundaryModification curve e ρ D v) e ρ p =
      gluedMax D v (subgeodesicChartFunction curve e ρ) p := by
  classical
  have hx := e.val.map_target hp
  have hex := e.val.right_inv hp
  simp only [stripChartFunction, boundaryModification, hx, hex, true_and, Prod.mk.eta]
  by_cases hpD : p ∈ D
  · rw [if_pos hpD, gluedMax_eq_max hpD]
    rw [← max_add_add_right, EReal.sub_add_cancel, max_comm]
    rfl
  · rw [if_neg hpD]
    simp only [gluedMax, if_neg hpD, subgeodesicChartFunction, chartFunction]

/-- The actual pointwise-boundary competitor produces genuine PSH of the actual corrected chart modification. -/
theorem plurisubharmonicOn_corrected_boundaryModification
    (curve : ℝ → M → EReal) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} (hW : IsOpen W) (hWt : W ⊆ e.val.target)
    (ρ : ComplexModel n → ℝ) {D : Set (ComplexModel n × ℂ)} (hD : IsOpen D)
    {v : ComplexModel n × ℂ → EReal}
    (hcurve : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ) (geodesicChartDomain W))
    (hv : PlurisubharmonicOn v D) (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ p ∈ geodesicChartDomain W ∩ frontier D,
      v p ≤ subgeodesicChartFunction curve e ρ p) :
    PlurisubharmonicOn (stripChartFunction (boundaryModification curve e ρ D v) e ρ)
      (geodesicChartDomain W) := by
  have hΩ : IsOpen (geodesicChartDomain W) := isOpen_geodesicChartDomain hW
  have hG := plurisubharmonicOn_gluedMax_of_boundary_le hΩ hD hcurve hv hvusc hvu
  intro p hp
  apply (hG p hp).congr
  filter_upwards [hΩ.mem_nhds hp] with q hq
  exact (corrected_boundaryModification_apply curve e ρ D v q (hWt hq.1)).symm

end

end SGPT.Foundations.Analysis.Pending.SingularPerronChartModification
