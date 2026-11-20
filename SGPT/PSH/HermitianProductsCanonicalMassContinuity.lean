import SGPT.PSH.HermitianProductsMassContinuity
import SGPT.PSH.HermitianGlobalMeasure

/-!
# Canonical Hermitian mass readback and actual monotone limits

The canonical global product has the original trace on every genuine
background patch. Multiplication by the supported partition weights and
their literal sum one identify the independently partitioned measure
with this canonical global measure on every set. The actual total-mass
limits therefore transfer to the canonical product, with the partition
chosen internally from the original background.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian
open scoped Topology ENNReal

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : Background (m + 1) M}

namespace MixedCurrentPartition

/-- Every genuine supported partition reconstructs the actual canonical
global mixed measure, on every set, from the already proved arbitrary
patch readback. No overlap or measure-equality premise is supplied. -/
theorem topMeasure_eq_globalMixedMeasure (D : MixedCurrentPartition omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    D.topMeasure u hu hb = globalMixedMeasure omega u hu hb := by
  let μ : Measure M := globalMixedMeasure omega u hu hb
  let f : Fin D.count → M → ℝ≥0∞ := fun j x => ENNReal.ofReal (D.weight j x)
  have hf (j : Fin D.count) : Measurable (f j) :=
    ENNReal.measurable_ofReal.comp (ProductTestForms.ChartSmooth.continuous (D.smooth j)).measurable
  have hweight (j : Fin D.count) :
      (D.patch j).geometry.weightedTraceMeasure ((D.patch j).current u)
        ((D.patch j).current_isPositive u hu hb) (D.weight j) = μ.withDensity (f j) := by
    rw [CoordinatePatch.weightedTraceMeasure,
      ← globalMixedMeasure_restrict_patch u hu hb (D.patch j)]
    rw [← withDensity_indicator (D.patch j).geometry.source.isOpen.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ (D.patch j).geometry.source
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hzero : D.weight j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (D.supported j h))
      simp only [f, hzero, ENNReal.ofReal_zero]
  have hsum : (∑' j, f j) = 1 := by
    funext x
    rw [tsum_fintype]
    rw [Finset.sum_apply]
    change (∑ j, ENNReal.ofReal (D.weight j x)) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => D.nonneg j x), D.sum_one x,
      ENNReal.ofReal_one]
  calc D.topMeasure u hu hb = Measure.sum (fun j => μ.withDensity (f j)) := by
        unfold topMeasure
        congr 1
        funext j
        exact hweight j
    _ = μ.withDensity (∑' j, f j) := (withDensity_tsum hf).symm
    _ = μ := by rw [hsum, withDensity_one]

/-- Exact real total-mass readback for the actual canonical global product. -/
theorem realTopMass_eq_globalMixedMeasure (D : MixedCurrentPartition omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    D.realTopMass u hu hb = (globalMixedMeasure omega u hu hb univ).toReal := by
  rw [realTopMass, D.topMeasure_eq_globalMixedMeasure u hu hb]

end MixedCurrentPartition

/-- The actual canonical global mixed masses converge along bounded
increasing Hermitian tuples to their literal USC-supremum mass. The
partition, limiting class, bounds and every current limit are internal. -/
theorem tendsto_globalMixedMeasure_real_mass_increasing_uscSup
    (omega : Background (m + 1) M)
    (u : ℕ → Fin (m + 1) → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hmono : ∀ i, Monotone fun j => u j i) :
    let u₀ : Fin (m + 1) → M → EReal := fun i => uscRegularization (fun x => ⨆ j, u j i x)
    let hu₀ : ∀ i, IsHermitianPSH omega (u₀ i) := fun i =>
      isHermitianPSH_uscRegularization_iSup_of_uniform_bound omega (fun j => u j i)
        (fun j => hu j i) b (fun j x => (hb j i x).2)
    let hb₀ : ∀ i, ∃ c d : ℝ, ∀ x, (c : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (d : EReal) :=
      fun i => ⟨a, b, uscRegularization_iSup_bounds (fun j => u j i) a b (fun j x => hb j i x)⟩
    Tendsto (fun j => (globalMixedMeasure omega (u j) (hu j)
      (fun i => ⟨a, b, hb j i⟩) univ).toReal) atTop
      (𝓝 (globalMixedMeasure omega u₀ hu₀ hb₀ univ).toReal) := by
  dsimp only
  obtain ⟨D⟩ := nonempty_mixedCurrentPartition omega
  have h := D.tendsto_realTopMass_increasing_uscSup u hu a b hb hmono
  simpa only [D.realTopMass_eq_globalMixedMeasure] using h

/-- The actual canonical global mixed masses converge along bounded
decreasing Hermitian tuples to their literal infimum mass. Original bounds
produce noncollapse and the limit class; no mass-convergence premise occurs. -/
theorem tendsto_globalMixedMeasure_real_mass_decreasing_iInf
    (omega : Background (m + 1) M)
    (u : ℕ → Fin (m + 1) → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hanti : ∀ i, Antitone fun j => u j i) :
    let u₀ : Fin (m + 1) → M → EReal := fun i x => ⨅ j, u j i x
    let hu₀ : ∀ i, IsHermitianPSH omega (u₀ i) := fun i =>
      (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
        (fun j x => hb j i x) (hanti i)).1
    let hb₀ : ∀ i, ∃ c d : ℝ, ∀ x, (c : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (d : EReal) :=
      fun i => ⟨a, b, (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
        (fun j x => hb j i x) (hanti i)).2⟩
    Tendsto (fun j => (globalMixedMeasure omega (u j) (hu j)
      (fun i => ⟨a, b, hb j i⟩) univ).toReal) atTop
      (𝓝 (globalMixedMeasure omega u₀ hu₀ hb₀ univ).toReal) := by
  dsimp only
  obtain ⟨D⟩ := nonempty_mixedCurrentPartition omega
  have h := D.tendsto_realTopMass_decreasing_iInf u hu a b hb hanti
  simpa only [D.realTopMass_eq_globalMixedMeasure] using h

end SGPT.PSH.HermitianGlobalProducts
