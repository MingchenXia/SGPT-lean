import SGPT.PSH.HermitianPartitionedMeasure
import SGPT.PSH.HermitianProductsIncreasingPotentials
import SGPT.PSH.HermitianProductsDecreasingPotentials
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts

/-!
# Actual partitioned Hermitian total mass and continuity

The supported smooth partition weights are transported to actual compact
coordinate tests. The literal weighted trace measures evaluate on the
whole manifold by the original top-degree currents on these tests. Thus
finite total mass is an actual finite sum of native current coefficients;
no overlap law or total-mass convergence certificate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere LocalProductCurrents LocalBedfordTaylorContinuity
  FiniteGeodesicStripCharts
open Hermitian HermitianProducts
open scoped Topology Distributions

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal chart reading of a genuine supported smooth weight is
an actual test function on the smaller coordinate patch. -/
def CoordinatePatch.weightTest (P : CoordinatePatch n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hχc : IsCompact (tsupport χ))
    (hχs : tsupport χ ⊆ P.source) : 𝓓(P.domain, ℝ) where
  toFun := chartRead P.chart χ
  contDiff' := contDiff_chartRead hχ hχc (fun x hx => (hχs hx).1)
  hasCompactSupport' := hasCompactSupport_chartRead hχc (fun x hx => (hχs hx).1)
  tsupport_subset' := (tsupport_chartRead_subset hχc (fun x hx => (hχs hx).1)).trans
    (by rintro z ⟨x, hx, rfl⟩; exact P.map_source (hχs hx))

theorem CoordinatePatch.weightTest_apply_of_mem (P : CoordinatePatch n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hχc : IsCompact (tsupport χ))
    (hχs : tsupport χ ⊆ P.source) {z : ComplexModel n} (hz : z ∈ P.domain) :
    P.weightTest χ hχ hχc hχs z = χ (P.chart.val.symm z) :=
  chartRead_of_mem (P.domain_le_target hz)

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual entire-manifold mass of the weighted transported trace
is the native top-degree current on its actual coordinate weight test. -/
theorem CoordinatePatch.weightedTraceMeasure_real_mass (P : CoordinatePatch n M)
    (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hχc : IsCompact (tsupport χ))
    (hχs : tsupport χ ⊆ P.source) (hχ0 : ∀ x, 0 ≤ χ x) :
    (P.weightedTraceMeasure T hT χ univ).toReal =
      T (kahlerPower n 0) (P.weightTest χ hχ hχc hχs) := by
  let φ : 𝓓(P.domain, ℝ) := P.weightTest χ hχ hχc hχs
  have hφ0 : ∀ z, 0 ≤ φ z := by
    intro z
    by_cases hz : z ∈ P.chart.val.target
    · change 0 ≤ chartRead P.chart χ z
      rw [chartRead_of_mem hz]
      exact hχ0 _
    · change 0 ≤ chartRead P.chart χ z
      rw [chartRead_of_notMem hz]
  have hL : (∫⁻ x, ENNReal.ofReal (χ x) ∂P.pushTraceMeasure T hT) =
      ∫⁻ z, ENNReal.ofReal (φ z) ∂hT.traceMeasure := by
    rw [CoordinatePatch.pushTraceMeasure, CoordinatePatch.pushMeasure,
      P.measurableEmbedding_toManifold.lintegral_map]
    change (∫⁻ z : P.domain, ENNReal.ofReal (χ (P.chart.val.symm z))
      ∂hT.traceMeasure.comap (Subtype.val : P.domain → ComplexModel n)) = _
    have ht := lintegral_subtype_comap (μ := hT.traceMeasure) P.domain.isOpen.measurableSet
      (fun z => ENNReal.ofReal (χ (P.chart.val.symm z)))
    refine ht.trans ?_
    have heq : (fun z => ENNReal.ofReal (χ (P.chart.val.symm z))) =ᵐ[
        hT.traceMeasure.restrict P.domain] fun z => ENNReal.ofReal (φ z) := by
      filter_upwards [ae_restrict_mem P.domain.isOpen.measurableSet] with z hz
      rw [P.weightTest_apply_of_mem χ hχ hχc hχs hz]
    rw [lintegral_congr_ae heq]
    rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hT.traceMeasure_compl)]
  rw [CoordinatePatch.weightedTraceMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [hL, ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφ0)
    φ.contDiff.continuous.aestronglyMeasurable, hT.integral_traceMeasure φ]

section PartitionMass

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {omega : Background (m + 1) X}

namespace MixedCurrentPartition

/-- This coordinate test depends only on the original partition and
patch, before any potential tuple. -/
def weightTest (D : MixedCurrentPartition omega) (j : Fin D.count) :
    𝓓((D.patch j).geometry.domain, ℝ) :=
  (D.patch j).geometry.weightTest (D.weight j) (D.smooth j)
    (isClosed_tsupport (D.weight j)).isCompact (D.supported j)

/-- Literal real total mass of the internally finite positive measure. -/
def realTopMass (D : MixedCurrentPartition omega) (u : Fin (m + 1) → X → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) : ℝ :=
  (D.topMeasure u hu hb univ).toReal

/-- The actual entire-manifold mass is a finite sum of original native
current coefficients on the fixed, internally manufactured compact tests. -/
theorem realTopMass_eq_sum (D : MixedCurrentPartition omega) (u : Fin (m + 1) → X → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    D.realTopMass u hu hb =
      ∑ j, (D.patch j).current u (kahlerPower (m + 1) 0) (D.weightTest j) := by
  have hfin (j : Fin D.count) :
      ((D.patch j).geometry.weightedTraceMeasure ((D.patch j).current u)
        ((D.patch j).current_isPositive u hu hb) (D.weight j)) univ ≠ ⊤ := by
    let := (D.patch j).geometry.weightedTraceMeasure_isFiniteMeasure
      ((D.patch j).current u) ((D.patch j).current_isPositive u hu hb) (D.weight j)
      (isClosed_tsupport (D.weight j)).isCompact (D.supported j) (D.weight_le_one j)
    exact measure_ne_top _ _
  rw [realTopMass, topMeasure, Measure.sum_apply_of_countable, tsum_fintype,
    ENNReal.toReal_sum (fun j _ => hfin j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (D.patch j).geometry.weightedTraceMeasure_real_mass ((D.patch j).current u)
    ((D.patch j).current_isPositive u hu hb) (D.weight j) (D.smooth j)
    (isClosed_tsupport (D.weight j)).isCompact (D.supported j) (D.nonneg j)

/-- Actual native weak-current convergence passes to the internally
finite total masses by the proved compact-test evaluation formula. -/
theorem tendsto_realTopMass_of_patchWeakTendsto (D : MixedCurrentPartition omega)
    (u : ℕ → Fin (m + 1) → X → EReal) (u₀ : Fin (m + 1) → X → EReal)
    (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (hb : ∀ j i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hu₀ : ∀ i, IsHermitianPSH omega (u₀ i))
    (hb₀ : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (b : EReal))
    (hweak : ∀ k, WeakTendsto (fun j => (D.patch k).current (u j)) ((D.patch k).current u₀)) :
    Tendsto (fun j => D.realTopMass (u j) (hu j) (hb j)) atTop
      (𝓝 (D.realTopMass u₀ hu₀ hb₀)) := by
  simp_rw [D.realTopMass_eq_sum]
  exact tendsto_finsetSum _ fun k _ => hweak k _ (D.weightTest k)

/-- Actual compact total masses converge along bounded increasing
Hermitian tuples to the mass of the literal USC supremum. The limiting
class, real bounds and all native weak limits are manufactured internally. -/
theorem tendsto_realTopMass_increasing_uscSup (D : MixedCurrentPartition omega)
    (u : ℕ → Fin (m + 1) → X → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hmono : ∀ i, Monotone fun j => u j i) :
    let u₀ : Fin (m + 1) → X → EReal := fun i => uscRegularization (fun x => ⨆ j, u j i x)
    let hu₀ : ∀ i, IsHermitianPSH omega (u₀ i) := fun i =>
      isHermitianPSH_uscRegularization_iSup_of_uniform_bound omega (fun j => u j i)
        (fun j => hu j i) b (fun j x => (hb j i x).2)
    let hb₀ : ∀ i, ∃ c d : ℝ, ∀ x, (c : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (d : EReal) :=
      fun i => ⟨a, b, uscRegularization_iSup_bounds (fun j => u j i) a b (fun j x => hb j i x)⟩
    Tendsto (fun j => D.realTopMass (u j) (hu j) (fun i => ⟨a, b, hb j i⟩)) atTop
      (𝓝 (D.realTopMass u₀ hu₀ hb₀)) := by
  dsimp only
  exact D.tendsto_realTopMass_of_patchWeakTendsto u _ hu
    (fun j i => ⟨a, b, hb j i⟩)
    (fun i => isHermitianPSH_uscRegularization_iSup_of_uniform_bound omega (fun j => u j i)
      (fun j => hu j i) b (fun j x => (hb j i x).2))
    (fun i => ⟨a, b, uscRegularization_iSup_bounds (fun j => u j i) a b (fun j x => hb j i x)⟩)
    (fun k => (D.patch k).current_increasing_uscSup u hu a b hb hmono)

/-- Actual compact total masses converge along bounded decreasing
Hermitian tuples to the literal infimum mass. Original bounds produce
noncollapse, the limiting class and every corrected-current limit. -/
theorem tendsto_realTopMass_decreasing_iInf (D : MixedCurrentPartition omega)
    (u : ℕ → Fin (m + 1) → X → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hanti : ∀ i, Antitone fun j => u j i) :
    let u₀ : Fin (m + 1) → X → EReal := fun i x => ⨅ j, u j i x
    let hu₀ : ∀ i, IsHermitianPSH omega (u₀ i) := fun i =>
      (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
        (fun j x => hb j i x) (hanti i)).1
    let hb₀ : ∀ i, ∃ c d : ℝ, ∀ x, (c : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (d : EReal) :=
      fun i => ⟨a, b, (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
        (fun j x => hb j i x) (hanti i)).2⟩
    Tendsto (fun j => D.realTopMass (u j) (hu j) (fun i => ⟨a, b, hb j i⟩)) atTop
      (𝓝 (D.realTopMass u₀ hu₀ hb₀)) := by
  dsimp only
  exact D.tendsto_realTopMass_of_patchWeakTendsto u _ hu
    (fun j i => ⟨a, b, hb j i⟩)
    (fun i => (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
      (fun j x => hb j i x) (hanti i)).1)
    (fun i => ⟨a, b, (isHermitianPSH_iInf_of_uniform_bounds omega (fun j => hu j i) a b
      (fun j x => hb j i x) (hanti i)).2⟩)
    (fun k => (D.patch k).current_decreasing_iInf u hu a b hb hanti)

end MixedCurrentPartition

end PartitionMass

end SGPT.PSH.HermitianGlobalProducts
