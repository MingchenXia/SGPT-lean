import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SGPT.Bergman.SourceWeightedSubset
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.FirstPass.MultiplierIdeals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- PORT-SOURCE bergman-quantization/SourceBergmanNorms.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.QuantizationDraft

open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- ALL native holomorphic sections of an actual complex holomorphic line bundle. -/
abbrev HolomorphicSections := ContMDiffSection (𝓘(ℂ, ComplexModel n)) ℂ ∞ V

/-- The actual zero set in the SAME native fibers. -/
def sectionZeroSet (s : HolomorphicSections (n := n) V) : Set X := {x | s x = 0}

/-- Genuine bundle coordinates give a one-function analytic presentation. -/
theorem sectionZeroSet_isComplexAnalytic (s : HolomorphicSections (n := n) V) :
    IsComplexAnalyticSubset (n := n) (sectionZeroSet (n := n) V s) := by
  intro x
  let e := trivializationAt ℂ V x
  let c := complexChartAt (n := n) x
  let g : X → ℂ := fun y => (e ⟨y, s y⟩).2
  let D := c.val.target ∩ c.val.symm ⁻¹' e.baseSet
  have hD : IsOpen D := c.val.isOpen_inter_preimage_symm e.open_baseSet
  refine ⟨{
    generatorCount := 1
    generator := fun _ => g ∘ c.val.symm
    coordinateNeighborhood := D
    isOpen_coordinateNeighborhood := hD
    center_mem_coordinateNeighborhood := ?_
    coordinateNeighborhood_subset_target := fun _ hz => hz.1
    generator_holomorphic := ?_
    zeroLocus := ?_ }⟩
  · refine ⟨c.val.map_source (mem_complexChartAt_source x), ?_⟩
    change c.val.symm (c.val x) ∈ e.baseSet
    rw [c.val.left_inv (mem_complexChartAt_source x)]
    exact mem_baseSet_trivializationAt ℂ V x
  · intro i z hz
    have hg : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞ g (c.val.symm z) :=
      (e.contMDiffAt_section_iff hz.2).mp (s.contMDiff (c.val.symm z))
    have hc : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞
        c.val.symm z := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hz.1
    exact ((hg.comp z hc).contDiffAt.differentiableAt (by simp)).differentiableWithinAt
  · intro y hy hyD
    have hybase : y ∈ e.baseSet := by
      have h := hyD.2
      change c.val.symm (c.val y) ∈ e.baseSet at h
      rwa [c.val.left_inv hy] at h
    have hread : g (c.val.symm (c.val y)) = e.linearEquivAt ℂ y hybase (s y) := by
      rw [c.val.left_inv hy]
      rfl
    change s y = 0 ↔ ∀ i : Fin 1, g (c.val.symm (c.val y)) = 0
    rw [hread]
    constructor
    · intro hs i
      rw [hs, map_zero]
    · intro h
      exact (e.linearEquivAt ℂ y hybase).map_eq_zero_iff.mp (h 0)

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- A nonzero genuine holomorphic section has a proper actual zero set. -/
theorem sectionZeroSet_ne_univ (s : HolomorphicSections (n := n) V) (hs : s ≠ 0) :
    sectionZeroSet (n := n) V s ≠ Set.univ := by
  intro h
  apply hs
  apply ContMDiffSection.ext
  intro x
  have hx : x ∈ sectionZeroSet (n := n) V s := h.symm ▸ Set.mem_univ x
  exact hx

/-- Nonzero section zero sets are pluripolar in the original source sense. -/
theorem sectionZeroSet_locallyPluripolar [ConnectedSpace X]
    (s : HolomorphicSections (n := n) V) (hs : s ≠ 0) :
    (ofFixedModel n X).LocallyPluripolar (sectionZeroSet (n := n) V s) := by
  have ha := sectionZeroSet_isComplexAnalytic V s
  have hi := SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    ha (sectionZeroSet_ne_univ V s hs)
  have hp := SGPT.Foundations.Analysis.Pending.ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    ha hi
  apply locallyPluripolar_of_in_chart
  intro e
  exact hp e

/-- Non-pluripolar restriction faithfully detects EVERY actual holomorphic section. -/
theorem eq_zero_of_vanishesOn_nonPluripolar [ConnectedSpace X]
    (s : HolomorphicSections (n := n) V) {K : Set X}
    (hK : (ofFixedModel n X).NonPluripolar K) (hsK : ∀ x ∈ K, s x = 0) : s = 0 := by
  by_contra hs
  exact hK ((sectionZeroSet_locallyPluripolar V s hs).mono hsK)

/-- The SAME original weighted subset is an actual consumer of section faithfulness. -/
theorem eq_zero_of_vanishesOn_weightedSubset [ConnectedSpace X]
    (W : WeightedSubset.WeightedSubset n X) (s : HolomorphicSections (n := n) V)
    (hsW : ∀ x : W.carrier, s x.val = 0) : s = 0 := by
  apply eq_zero_of_vanishesOn_nonPluripolar V s W.nonPluripolar_carrier
  exact fun x hx => hsW ⟨x, hx⟩

/-- Actual squared fiber norm times the SAME original extended-real obstacle weight. -/
def weightedSectionDensity {K : Set X} (k : ℕ) (v : K → EReal)
    (s : HolomorphicSections (n := n) V) (x : K) : ℝ≥0∞ :=
  ENNReal.ofReal (‖s x.val‖ ^ 2) * multiplierWeight (k : ℝ) (v x)

/-- The original supremum over the EXACT complement of the minus-infinity locus. -/
def weightedSupNorm {K : Set X} (k : ℕ) (v : K → EReal)
    (s : HolomorphicSections (n := n) V) : ℝ≥0∞ :=
  ⨆ x : K, ⨆ (_ : v x ≠ ⊥), (weightedSectionDensity V k v s x) ^ (1 / 2 : ℝ)

/-- The original integral norm on the SAME subtype K; infinity is retained. -/
def weightedL2Norm {K : Set X} [MeasurableSpace K] (k : ℕ) (v : K → EReal)
    (μ : MeasureTheory.Measure K) (s : HolomorphicSections (n := n) V) : ℝ≥0∞ :=
  (∫⁻ x, weightedSectionDensity V k v s x ∂μ) ^ (1 / 2 : ℝ)

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- Pointwise actual section densities are antitone in the original obstacle. -/
theorem weightedSectionDensity_antitone {K : Set X} (k : ℕ) {v₁ v₂ : K → EReal}
    (hv : v₁ ≤ v₂) (s : HolomorphicSections (n := n) V) (x : K) :
    weightedSectionDensity V k v₂ s x ≤ weightedSectionDensity V k v₁ s x := by
  exact mul_le_mul_right ((multiplierWeight_antitone (Nat.cast_nonneg k)) (hv x)) _

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- WHOLE original lma:mononorm, with the exact equal-pole-set hypothesis. -/
theorem weightedSupNorm_antitone {K : Set X} (k : ℕ) {v₁ v₂ : K → EReal}
    (hv : v₁ ≤ v₂) (hpoles : {x | v₁ x = ⊥} = {x | v₂ x = ⊥})
    (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k v₂ s ≤ weightedSupNorm V k v₁ s := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hx₁ : v₁ x ≠ ⊥ := by
    intro h
    have hm : x ∈ {x | v₁ x = ⊥} := h
    rw [hpoles] at hm
    exact hx hm
  exact (ENNReal.rpow_le_rpow (weightedSectionDensity_antitone V k hv s x) (by positivity)).trans
    (le_iSup_of_le x (le_iSup_of_le hx₁ le_rfl))

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- The integral norms are antitone even without equal pole sets. -/
theorem weightedL2Norm_antitone {K : Set X} [MeasurableSpace K] (k : ℕ)
    {v₁ v₂ : K → EReal} (hv : v₁ ≤ v₂) (μ : MeasureTheory.Measure K)
    (s : HolomorphicSections (n := n) V) :
    weightedL2Norm V k v₂ μ s ≤ weightedL2Norm V k v₁ μ s := by
  exact ENNReal.rpow_le_rpow
    (MeasureTheory.lintegral_mono (weightedSectionDensity_antitone V k hv s)) (by positivity)

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- The actual zero section has zero supremum, including poles and an empty domain. -/
theorem weightedSupNorm_zero {K : Set X} (k : ℕ) (v : K → EReal) :
    weightedSupNorm V (n := n) k v 0 = 0 := by
  simp [weightedSupNorm, weightedSectionDensity]

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- Finite real weights make pointwise density-zero equivalent to SAME fiber-value zero. -/
theorem weightedSectionDensity_real_eq_zero_iff {K : Set X} (k : ℕ) (v : K → ℝ)
    (s : HolomorphicSections (n := n) V) (x : K) :
    weightedSectionDensity V k (fun x => (v x : EReal)) s x = 0 ↔ s x.val = 0 := by
  rw [weightedSectionDensity, multiplierWeight_coe, mul_eq_zero]
  have he : ENNReal.ofReal (Real.exp (-((k : ℝ) * v x))) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  simp only [he, or_false, ENNReal.ofReal_eq_zero, sq_nonpos_iff, norm_eq_zero]

/-- Full nondegeneracy on ALL actual sections, for any finite real weight on nonPP K. -/
theorem weightedSupNorm_real_eq_zero_iff [ConnectedSpace X] {K : Set X}
    (hK : (ofFixedModel n X).NonPluripolar K) (k : ℕ) (v : K → ℝ)
    (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k (fun x => (v x : EReal)) s = 0 ↔ s = 0 := by
  constructor
  · intro hz
    apply eq_zero_of_vanishesOn_nonPluripolar V s hK
    intro x hx
    let y : K := ⟨x, hx⟩
    have hle : (weightedSectionDensity V k (fun x => (v x : EReal)) s y) ^ (1 / 2 : ℝ) ≤
        weightedSupNorm V k (fun x => (v x : EReal)) s :=
      le_iSup_of_le y (le_iSup_of_le (EReal.coe_ne_bot (v y)) le_rfl)
    rw [hz] at hle
    have hd := (ENNReal.rpow_eq_zero_iff_of_pos (by positivity : (0 : ℝ) < 1 / 2)).mp
      (le_antisymm hle bot_le)
    exact (weightedSectionDensity_real_eq_zero_iff V k v s y).mp hd
  · rintro rfl
    exact weightedSupNorm_zero V k _

/-- The canonical weighted subset feeds its SAME real continuous obstacle to the actual norm. -/
theorem weightedSupNorm_weightedSubset_eq_zero_iff [ConnectedSpace X]
    (W : WeightedSubset.WeightedSubset n X) (k : ℕ) (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight s = 0 ↔ s = 0 :=
  weightedSupNorm_real_eq_zero_iff V W.nonPluripolar_carrier k W.weight s

end SGPT.Bergman.QuantizationDraft
