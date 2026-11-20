import SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanCollarGluing
import SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealCoordinateData

set_option autoImplicit false

/-!
# Coordinate multiplier-ideal control through shifted finite collar gluing

This composes the retained double-radius coordinate data with the shifted
finite collar recursion.  The normalization data comes from the fixed
Bergman balls, while the collar data and later-core separation remain explicit.
In particular, this does not claim that the lower and outer comparisons select
one compatible shift automatically.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanCoordinateIdealGluing

open FirstPass
open FirstPass.HolomorphicIdealSheaves
open BergmanGenerators
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open FiniteShiftedBergmanCollarGluing
open FiniteUniformMultiplierIdealCoordinateData
open FiniteUniformMultiplierIdealControl
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Explicit avoidance of later shifted cores, exactly as needed to preserve a
patch stage as a germ through the rest of the finite recursion. -/
def ShiftedLaterCoreSeparation
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    {A : FiniteUniformLocalBergmanAtlas θ u m} {offset : Fin A.count → ℝ}
    {g : M → EReal} (H : FiniteShiftedBergmanCollarData A offset g) : Prop :=
  ∀ i j : Fin A.count, i.val < j.val → H.inner i ⊆ (closure (H.inner j))ᶜ

/-- Coordinate zero extensions with centre ideal membership and actual
fixed double-radius differentiability and weighted `L²` witnesses give every
shifted finite glued core its normalized generator control, a shifted-branch
lower germ comparison, and its analytic singularity type.  Both the outer
collar inequalities and the common-offset compatibility remain premises in
`H`; the theorem does not manufacture them. -/
theorem exists_finiteShiftedBergmanCoordinateIdealGluing_control
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g₀ : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g₀)
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
        (ball (A.patch i).center (2 * (A.patch i).radius)) volume)
    (hsep : ShiftedLaterCoreSeparation H) :
    ∀ i : Fin A.count, ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∀ j, (fun z => (s : ℂ) *
          coordinateZeroExtension (A.patch i).patch.chart (f i j)
            ((A.patch i).patch.chart.val.symm z)) ∈
          bergmanUnitBall (A.patch i).center (A.patch i).radius
            (fun z => multiplierWeight (m : ℝ) ((A.patch i).weight z))) ∧
      (∀ x ∈ H.inner i,
        generatorLog (fun j z => (s : ℂ) *
          coordinateZeroExtension (A.patch i).patch.chart (f i j)
            ((A.patch i).patch.chart.val.symm z))
            ((A.patch i).patch.chart.val x) ≤
          generatorLog (A.patch i).patch.generator ((A.patch i).patch.chart.val x) +
            (Real.log C : EReal)) ∧
      (∀ x ∈ H.inner i,
        ∀ᶠ y in 𝓝 x,
          shiftedBergmanBranch (A.patch i).patch (offset i) y ≤
            finiteShiftedBergmanGlued A offset g₀ A.count y) ∧
      ∀ x ∈ H.inner i,
        HasAnalyticSingularityTypeAt
          (chartFunction (finiteShiftedBergmanGlued A offset g₀ A.count)
            (A.patch i).patch.chart)
          ((A.patch i).patch.chart.val x) := by
  obtain hpatch := exists_patchwise_normalized_multiplierIdeal_control A
    (finiteUniformMultiplierIdealControlData_of_coordinate_ball_data A f hmember hdiff hL2)
  intro i
  obtain ⟨s, C, hs, hC, hunit, hlog, _htype⟩ := hpatch i
  refine ⟨s, C, hs, hC, hunit, ?_, ?_, ?_⟩
  · intro x hx
    have hxsource : x ∈ (A.patch i).patch.source :=
      H.closure_inner_subset i (subset_closure hx)
    exact hlog ((A.patch i).patch.chart.val x) hxsource.2
  · intro x hx
    exact finiteShiftedBergmanGlued_eventually_lowerBound_core_final A offset g₀ H i
      (q := shiftedBergmanBranch (A.patch i).patch (offset i)) (fun _ _ => le_rfl) hx
      (fun j hij => hsep i j hij)
  · intro x hx
    have hxsource : x ∈ (A.patch i).patch.source :=
      H.closure_inner_subset i (subset_closure hx)
    have htarget : (A.patch i).patch.chart.val x ∈ (A.patch i).patch.chart.val.target :=
      (A.patch i).patch.chart.val.map_source hxsource.1
    have hcore :
        (A.patch i).patch.chart.val.symm ((A.patch i).patch.chart.val x) ∈ H.inner i := by
      rw [(A.patch i).patch.chart.val.left_inv hxsource.1]
      exact hx
    exact finiteShiftedBergmanGlued_analyticTypeAt_core_final A offset g₀ H i htarget hcore
      (fun j hij => hsep i j hij)

end

end SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanCoordinateIdealGluing
