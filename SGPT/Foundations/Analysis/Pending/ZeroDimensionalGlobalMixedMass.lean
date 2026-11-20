import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass

open FirstPass FirstPass.MixedMongeAmpere FirstPass.GlobalPotentialPatches
  LocalBedfordTaylorSmoothTraceMeasure LocalBedfordTaylorCanonicalTraceMeasure

private theorem discreteTopology_zero_dim {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  let e : ComplexChart 0 M := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have he : e.val.source = {x} := by
    ext y
    constructor
    · intro hy
      exact e.val.injOn hy hx (Subsingleton.elim _ _)
    · intro hy
      exact (mem_singleton_iff.mp hy) ▸ hx
  rw [← he]
  exact e.val.open_source

/-- Compactness and the actual zero-dimensional charts supply both conclusions. -/
theorem compact_zero_dim_finite_discrete {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [CompactSpace M] :
    DiscreteTopology M ∧ Finite M := by
  let : DiscreteTopology M := discreteTopology_zero_dim
  exact ⟨inferInstance, finite_of_compact_of_discrete⟩

private theorem volume_zero_dim_eq_count :
    (volume : Measure (ComplexModel 0)) = Measure.count := by
  let b := stdOrthonormalBasis ℝ (ComplexModel 0)
  have hb : parallelepiped b = Set.univ := by
    apply eq_univ_of_forall
    intro x
    apply (mem_parallelepiped_iff b x).mpr
    refine ⟨0, ?_, ?_⟩
    · simp only [mem_Icc, le_refl, true_and]
      exact Pi.le_def.mpr (fun _ => zero_le_one)
    · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      exact Subsingleton.elim _ _
  have hv : (volume : Measure (ComplexModel 0)) Set.univ = 1 := by
    rw [← hb]
    exact b.volume_parallelepiped
  rw [Subsingleton.count_eq_dirac (0 : ComplexModel 0)]
  apply Measure.ext
  intro s hs
  by_cases h0 : (0 : ComplexModel 0) ∈ s
  · have he : s = Set.univ := eq_univ_of_forall fun x =>
      (Subsingleton.elim (0 : ComplexModel 0) x) ▸ h0
    simp only [he, hv, Measure.dirac_apply_of_mem (mem_univ _)]
  · have he : s = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
      h0 ((Subsingleton.elim x (0 : ComplexModel 0)) ▸ hx)
    simp only [he, measure_empty]

private theorem mixedDensity_zero_dim (v : Fin 0 → ComplexModel 0 → ℝ)
    (z : ComplexModel 0) : mixedDensity v z = 1 := by
  unfold mixedDensity
  have he : (fun i : Fin 0 => MongeAmpere.complexHessian (v i) z) =
      fun _ => (0 : Matrix (Fin 0) (Fin 0) ℂ) := funext (fun i => Fin.elim0 i)
  rw [he, mixedCoefficient_diagonal, Matrix.det_isEmpty]
  norm_num

/-- Actual unit-product trace and canonical measure, with the original empty density. -/
theorem local_empty_mixed_product_eq_count (Ω : Opens (ComplexModel 0))
    (v : Fin 0 → ComplexModel 0 → ℝ) (hv : IsLocallyBoundedMixedPshOn Ω v) :
    ((∀ z, mixedDensity v z = 1) ∧
      ∀ β : Fin 0 → StronglyPositiveForms.RealForm 0 2,
        TopDegreeDensity.topDensity (TopDegreeDensity.wedgeProd 0 β) = 1) ∧
      MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω v hv =
        (Measure.count : Measure (ComplexModel 0)).restrict Ω ∧
      recursiveMixedTraceMeasure Ω v hv =
        (Measure.count : Measure (ComplexModel 0)).restrict Ω := by
  have hg : ∀ i, ContDiffOn ℝ ∞ (v i) Ω := fun i => Fin.elim0 i
  have hp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) Ω :=
    fun i => Fin.elim0 i
  have hs := recursiveMixedTraceMeasure_eq_smoothMixedMeasure hg hp
  dsimp only at hs
  have hrec : recursiveMixedTraceMeasure Ω v hv =
      (Measure.count : Measure (ComplexModel 0)).restrict Ω := by
    rw [hs, smoothMixedMeasure]
    simp only [mixedDensity_zero_dim, ENNReal.ofReal_one, volume_zero_dim_eq_count]
    exact withDensity_one
  refine ⟨⟨mixedDensity_zero_dim v, fun _ => rfl⟩, ?_, hrec⟩
  rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hv, hrec]

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
  {θ : Fin 0 → ClosedRealOneOneForm 0 M} {u : Fin 0 → M → EReal}

/-- The genuine coordinate push/comap of each original empty patch is counting measure. -/
theorem patch_empty_mixed_measure_eq_count (P : Patch θ u) :
    GlobalNonPluripolar.patchMeasure P = (Measure.count : Measure M).restrict P.source := by
  let : DiscreteTopology M := discreteTopology_zero_dim
  let v : Fin 0 → ComplexModel 0 → ℝ := fun i => Fin.elim0 i
  have hv : IsLocallyBoundedMixedPshOn P.domain v := fun i => Fin.elim0 i
  have hl := MixedNonPluripolar.mixedTruncationLimitMeasure_zero_dim
    P.domain P.corrected P.plurisubharmonic v hv
  rw [(local_empty_mixed_product_eq_count P.domain v hv).2.1] at hl
  unfold GlobalNonPluripolar.patchMeasure
  rw [hl]
  apply Measure.ext
  intro s hs
  rw [P.pushMeasure_apply_image, Measure.restrict_apply (isOpen_discrete _).measurableSet]
  have hsub : P.chart.val '' (s ∩ (P.source : Set M)) ⊆ P.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact P.map_source hx.2
  rw [inter_eq_left.mpr hsub, Measure.count_apply (isOpen_discrete _).measurableSet,
    Measure.restrict_apply hs, Measure.count_apply (isOpen_discrete _).measurableSet]
  congr 1
  exact (P.chart.val.injOn.mono
    (inter_subset_right.trans P.source_subset)).encard_image

/-- The actual global constructor has the original finite empty-wedge mass, even for empty M. -/
theorem global_empty_mixed_measure_eq_count [CompactSpace M]
    (θ : Fin 0 → ClosedRealOneOneForm 0 M) (u : Fin 0 → M → EReal)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    GlobalNonPluripolar.globalMixedMeasure θ u hu = Measure.count ∧
      GlobalNonPluripolar.globalMixedMeasure θ u hu Set.univ = (Nat.card M : ℝ≥0∞) ∧
      GlobalNonPluripolar.globalMixedMeasure θ u hu Set.univ < ⊤ ∧
      (∫ _ : M, (1 : ℝ) ∂GlobalNonPluripolar.globalMixedMeasure θ u hu) =
        (Nat.card M : ℝ) := by
  have hm := compact_zero_dim_finite_discrete (M := M)
  let : DiscreteTopology M := hm.1
  let : Finite M := hm.2
  have he : GlobalNonPluripolar.globalMixedMeasure θ u hu = Measure.count :=
    (GlobalNonPluripolar.globalMixedMeasure_unique hu Measure.count
      (fun P => (patch_empty_mixed_measure_eq_count P).symm)).symm
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [he, Measure.count_univ, ENat.card_eq_coe_natCard]
    simp
  · rw [he]
    exact measure_lt_top _ _
  · rw [he, integral_const, Measure.count_real_univ]
    simp

end SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass
