import SGPT.BBJ.ProjectiveCantor
import SGPT.Toric.ProjectiveLineNativePotential
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Support

/-! The actual fair-product probability and its pushforward to the concrete Cantor set.
No nonatomicity or support property is supplied as an assumption. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open scoped Topology ENNReal
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The literal half-Dirac Bernoulli marginal. -/
def fairBitMeasure : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure false true ⟨1 / 2, by constructor <;> norm_num⟩

instance fairBitMeasure_probability : IsProbabilityMeasure fairBitMeasure := by
  unfold fairBitMeasure
  infer_instance

lemma fairBitMeasure_singleton (b : Bool) : fairBitMeasure {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> rw [fairBitMeasure, ProbabilityTheory.bernoulliMeasure_apply _
    (measurableSet_singleton _)] <;>
    norm_num [unitInterval.toNNReal, unitInterval.symm]
  all_goals
    change ((1 / 2 : NNReal) : ℝ≥0∞) = _
    norm_num

/-- The existing genuine infinite product, with the explicit fair marginal in every coordinate. -/
def cantorBitProbability : Measure (ℕ → Bool) := Measure.infinitePi (fun _ => fairBitMeasure)

instance cantorBitProbability_probability : IsProbabilityMeasure cantorBitProbability := by
  unfold cantorBitProbability
  infer_instance

/-- An actual finite-coordinate cylinder, for arbitrary finite coordinate sets. -/
def cantorCylinder (I : Finset ℕ) (b : ℕ → Bool) : Set (ℕ → Bool) :=
  Set.pi (I : Set ℕ) (fun k => {b k})

lemma cantorBitProbability_cylinder (I : Finset ℕ) (b : ℕ → Bool) :
    cantorBitProbability (cantorCylinder I b) = (1 / 2 : ℝ≥0∞) ^ I.card := by
  rw [cantorBitProbability, cantorCylinder,
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [fairBitMeasure_singleton]

lemma cantorBitProbability_singleton (b : ℕ → Bool) : cantorBitProbability {b} = 0 := by
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num :
    (1 / 2 : ℝ≥0∞) < 1))
  intro n
  rw [← Finset.card_range n, ← cantorBitProbability_cylinder]
  apply measure_mono
  intro d hd
  have hdb : d = b := mem_singleton_iff.mp hd
  subst d
  intro k _
  exact mem_singleton _

/-- Only now, after proving every singleton null, install the derived atom-free instance. -/
instance cantorBitProbability_noAtoms : NullSingletonClass cantorBitProbability :=
  ⟨cantorBitProbability_singleton⟩

/-- The actual pushforward to the unchanged original projective quotient. -/
def projectiveCantorProbability : Measure P1 :=
  cantorBitProbability.map projectiveCantorCode

instance projectiveCantorProbability_probability :
    IsProbabilityMeasure projectiveCantorProbability where
  measure_univ := by
    rw [projectiveCantorProbability, Measure.map_apply
      continuous_projectiveCantorCode.measurable MeasurableSet.univ,
      preimage_univ, measure_univ]

lemma projectiveCantorProbability_singleton (p : P1) :
    projectiveCantorProbability {p} = 0 := by
  rw [projectiveCantorProbability, Measure.map_apply
    continuous_projectiveCantorCode.measurable (measurableSet_singleton p)]
  by_cases hp : p ∈ projectiveCantorSet
  · obtain ⟨b, rfl⟩ := hp
    have he : projectiveCantorCode ⁻¹' {projectiveCantorCode b} = {b} := by
      ext d
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => projectiveCantorCode_injective h, congrArg projectiveCantorCode⟩
    rw [he, cantorBitProbability_singleton]
  · have he : projectiveCantorCode ⁻¹' {p} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hp ⟨b, mem_singleton_iff.mp hb⟩
    rw [he, measure_empty]

instance projectiveCantorProbability_noAtoms : NullSingletonClass projectiveCantorProbability :=
  ⟨projectiveCantorProbability_singleton⟩

lemma projectiveCantorProbability_compl :
    projectiveCantorProbability projectiveCantorSetᶜ = 0 := by
  rw [projectiveCantorProbability, Measure.map_apply
    continuous_projectiveCantorCode.measurable isClosed_projectiveCantorSet.measurableSet.compl]
  have he : projectiveCantorCode ⁻¹' projectiveCantorSetᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hb ⟨b, rfl⟩
  rw [he, measure_empty]

/-- Every cylinder in the actual product has positive mass, so every neighborhood
of a coded point has positive pushforward mass. This also proves exact support. -/
lemma projectiveCantorProbability_support :
    projectiveCantorProbability.support = projectiveCantorSet := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_projectiveCantorSet
    exact projectiveCantorProbability_compl
  · rintro p ⟨b, rfl⟩
    apply (Measure.mem_support_iff_forall _).mpr
    intro U hU
    have hpre : projectiveCantorCode ⁻¹' U ∈ 𝓝 b :=
      continuous_projectiveCantorCode.continuousAt hU
    rw [nhds_pi] at hpre
    obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hpre
    have hcy : cantorCylinder I b ⊆ projectiveCantorCode ⁻¹' U := by
      intro d hd
      apply hsub
      intro i hi
      have hdi : d i = b i := hd i hi
      rw [hdi]
      exact mem_of_mem_nhds (ht i)
    have hpos : 0 < cantorBitProbability (cantorCylinder I b) := by
      rw [cantorBitProbability_cylinder]
      exact ENNReal.pow_pos (by norm_num) _
    exact hpos.trans_le ((measure_mono hcy).trans
      (Measure.le_map_apply continuous_projectiveCantorCode.measurable.aemeasurable U))

end SGPT.BBJ
