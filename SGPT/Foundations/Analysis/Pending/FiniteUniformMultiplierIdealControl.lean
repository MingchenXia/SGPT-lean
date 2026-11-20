import SGPT.Foundations.Analysis.Pending.UniformLocalBergmanFiniteAtlas
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalizationBranch
import SGPT.Foundations.Analysis.Pending.KahlerCurrentRegularizationBergmanBranch

set_option autoImplicit false

/-!
# Finite local multiplier-ideal control for a uniform Bergman atlas

An existing finite atlas has fixed, patch-dependent coordinate balls. A
multiplier-ideal germ at the centre alone only supplies an unspecified smaller
neighborhood, so this module records the exact additional local evidence needed
to apply the fixed patch's universal Bergman estimate: actual holomorphic and
weighted `L²` data on that patch's own integration ball. From it we obtain a
callable finite-family logarithmic comparison and the analytic type of every
patch branch, with no claim that a common global comparator exists.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealControl

open FirstPass
open FirstPass.HolomorphicIdealSheaves
open BergmanGenerators
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open KahlerCurrentRegularizationBergmanBranch
open MultiplierIdealBergmanNormalization

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Explicit patchwise data for a finite family of preferred multiplier-ideal
germs. The last two fields deliberately use the actual radius of each
pre-existing atlas patch. They cannot be recovered merely from germ membership,
since the atlas does not record containment of that fixed ball in the germ's
arbitrary witness neighborhood. -/
structure FiniteUniformMultiplierIdealControlData
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m)
    (q : Fin A.count → ℕ) (g : ∀ i, Fin (q i) → M → ℂ) where
  center_mem_domain : ∀ i, (A.patch i).center ∈ (A.patch i).patch.domain
  germ_member : ∀ i j,
    (multiplierIdeal (n := n) (m : ℝ) u).mem
      ((A.patch i).patch.chart.val.symm (A.patch i).center) (g i j)
  coordinate_differentiable : ∀ i j,
    DifferentiableOn ℂ (fun z => g i j ((A.patch i).patch.chart.val.symm z))
      (ball (A.patch i).center (2 * (A.patch i).radius))
  coordinate_weighted : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ i j,
      WeightedL2On (A.patch i).weight (m : ℝ)
        (fun z => g i j ((A.patch i).patch.chart.val.symm z))
        (ball (A.patch i).center (2 * (A.patch i).radius)) volume

/-- The chart inverse of an admitted patch centre lies in its actual source.
This makes `germ_member` a statement at a genuine point of the corresponding
local branch rather than at an unconstrained chart inverse. -/
theorem FiniteUniformMultiplierIdealControlData.centerPoint_mem_source
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    {A : FiniteUniformLocalBergmanAtlas θ u m}
    {q : Fin A.count → ℕ} {g : ∀ i, Fin (q i) → M → ℂ}
    (H : FiniteUniformMultiplierIdealControlData A q g) (i : Fin A.count) :
    (A.patch i).patch.chart.val.symm (A.patch i).center ∈ (A.patch i).patch.source := by
  have htarget : (A.patch i).center ∈ (A.patch i).patch.chart.val.target :=
    (A.patch i).patch.domain_le_target (H.center_mem_domain i)
  change (A.patch i).patch.chart.val.symm (A.patch i).center ∈
    (A.patch i).patch.chart.val.source ∩
      (A.patch i).patch.chart.val ⁻¹' (A.patch i).patch.domain
  refine ⟨(A.patch i).patch.chart.val.map_target htarget, ?_⟩
  change (A.patch i).patch.chart.val
    ((A.patch i).patch.chart.val.symm (A.patch i).center) ∈ (A.patch i).patch.domain
  rw [(A.patch i).patch.chart.val.right_inv htarget]
  exact H.center_mem_domain i

/-- Every patch of a fixed finite uniform atlas controls its own finite family
of normalized multiplier-ideal representatives on its own domain. The
constants and domains remain indexed by the patch; no uniformity across
different radii or any global patch comparison is asserted. -/
theorem exists_patchwise_normalized_multiplierIdeal_control
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m)
    {q : Fin A.count → ℕ} {g : ∀ i, Fin (q i) → M → ℂ}
    (H : FiniteUniformMultiplierIdealControlData A q g) :
    ∀ i : Fin A.count, ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∀ j, (fun z => (s : ℂ) * g i j ((A.patch i).patch.chart.val.symm z)) ∈
          bergmanUnitBall (A.patch i).center (A.patch i).radius
            (fun z => multiplierWeight (m : ℝ) ((A.patch i).weight z))) ∧
      (∀ y ∈ (A.patch i).patch.domain,
        generatorLog (fun j z => (s : ℂ) * g i j ((A.patch i).patch.chart.val.symm z)) y ≤
          generatorLog (A.patch i).patch.generator y + (Real.log C : EReal)) ∧
      ∀ y ∈ (A.patch i).patch.domain,
        HasAnalyticSingularityTypeAt
          (chartFunction (bergmanBranch (A.patch i).patch) (A.patch i).patch.chart) y := by
  intro i
  obtain ⟨s, C, hs, hC, hunit, hlog⟩ :=
    UniformLocalBergmanPatch.exists_normalized_generatorLog_domination (A.patch i)
      (fun j => H.coordinate_differentiable i j) (H.coordinate_weighted i)
  refine ⟨s, C, hs, hC, hunit, hlog, fun y hy => ?_⟩
  exact bergmanBranch_analyticTypeAt_ownChart (A.patch i).patch hy

end
end SGPT.Foundations.Analysis.Pending.FiniteUniformMultiplierIdealControl
