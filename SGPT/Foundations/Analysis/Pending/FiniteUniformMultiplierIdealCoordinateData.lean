import SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealControl

set_option autoImplicit false

/-!
# Coordinate representatives for finite uniform Bergman patches

The Demailly patch retains a fixed integration ball in its chart target.  This
file packages the elementary transport from functions on that ball to global
functions on the manifold: extend a coordinate representative by zero outside
the chart source, and use the retained target containment to recover the
original representative after composing with the chart inverse.  The weighted
`L²` and differentiability evidence on the fixed ball remain explicit inputs.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealCoordinateData

open FirstPass
open FirstPass.HolomorphicIdealSheaves
open QuasiEquisingularBergmanAtlas
open FiniteUniformMultiplierIdealControl

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A coordinate function, extended by zero outside the source of its chart. -/
noncomputable def coordinateZeroExtension
    (e : ComplexChart n M) (f : ComplexModel n → ℂ) : M → ℂ := by
  classical
  exact fun x => if x ∈ e.val.source then f (e.val x) else 0

omit [IsComplexManifold n M] in
theorem coordinateZeroExtension_apply_of_mem_chart_source
    (e : ComplexChart n M) (f : ComplexModel n → ℂ) {x : M}
    (hx : x ∈ e.val.source) :
    coordinateZeroExtension e f x = f (e.val x) := by
  simp [coordinateZeroExtension, hx]

/-- On the retained double-radius ball, the zero extension recovers the
coordinate function after chart inversion. -/
theorem coordinateZeroExtension_chart_symm_of_mem_double_radius
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) (f : ComplexModel n → ℂ)
    {z : ComplexModel n} (hz : z ∈ ball D.center (2 * D.radius)) :
    coordinateZeroExtension D.patch.chart f (D.patch.chart.val.symm z) = f z := by
  rw [coordinateZeroExtension_apply_of_mem_chart_source _ _
    (D.chart_symm_mem_chart_source_of_mem_double_radius hz),
    D.chart_apply_symm_of_mem_double_radius hz]

/-- Fixed-ball coordinate representatives with explicit ideal membership at
the centre produce exactly the control data required by the finite uniform
Bergman atlas.  The hypotheses retain, rather than derive, the ballwise
holomorphic and weighted `L²` evidence. -/
theorem finiteUniformMultiplierIdealControlData_of_coordinate_ball_data
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m)
    {q : Fin A.count → ℕ}
    (f : ∀ i, Fin (q i) → ComplexModel n → ℂ)
    (hmember : ∀ i j,
      (multiplierIdeal (n := n) (m : ℝ) u).mem
        ((A.patch i).patch.chart.val.symm (A.patch i).center)
        (coordinateZeroExtension (A.patch i).patch.chart (f i j)))
    (hdiff : ∀ i j, DifferentiableOn ℂ (f i j)
      (ball (A.patch i).center (2 * (A.patch i).radius)))
    (hL2 : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ i j, WeightedL2On (A.patch i).weight (m : ℝ) (f i j)
        (ball (A.patch i).center (2 * (A.patch i).radius)) volume) :
    FiniteUniformMultiplierIdealControlData A q
      (fun i j => coordinateZeroExtension (A.patch i).patch.chart (f i j)) := by
  refine {
    center_mem_domain := fun i => (A.patch i).center_mem_domain
    germ_member := hmember
    coordinate_differentiable := ?_
    coordinate_weighted := ?_ }
  · intro i j
    refine (hdiff i j).congr fun z hz => ?_
    exact coordinateZeroExtension_chart_symm_of_mem_double_radius (A.patch i) (f i j) hz
  · let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    intro i j
    refine (hL2 i j).congr isOpen_ball.measurableSet (fun _ _ => rfl) fun z hz => ?_
    symm
    exact coordinateZeroExtension_chart_symm_of_mem_double_radius (A.patch i) (f i j) hz

end
end SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealCoordinateData
