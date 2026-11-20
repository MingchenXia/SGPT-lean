import SGPT.Foundations.Analysis.Pending.FilterCalibratedCurrentACLimit
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure

set_option autoImplicit false

/-! SAME original full positive global currents: genuine calibrated weak
family under an arbitrary nontrivial filter internally yields complete canonical AC measure lower bound.
Full BP before Lean. No atlas, overlap, limit-density or mass certificate. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.GlobalFilterCalibratedCurrentACLimit
open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  GlobalCurrents GlobalCurrentPotentials
  LocalProductCurrents LocalCurrentDeterminant PositiveCurrentACTopMeasure
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  FilterCalibratedCurrentACLimit ActualAnalyticCurrentLocalDensity

private theorem measure_le_of_finite_restrictions {X : Type*} [MeasurableSpace X]
    {k : ℕ} (U : Fin k → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ⋃ i, U i = univ) {μ ν : Measure X}
    (hlocal : ∀ i, μ.restrict (U i) ≤ ν.restrict (U i)) : μ ≤ ν := by
  have hμ := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => μ) hU hcover μ (fun _ => rfl)
  have hν := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => ν) hU hcover ν (fun _ => rfl)
  have hdi (i : Fin k) : μ.restrict (disjointed U i) ≤ ν.restrict (disjointed U i) := by
    have h := Measure.restrict_mono_measure (hlocal i) (disjointed U i)
    simpa only [Measure.restrict_restrict_of_subset (disjointed_subset U i)] using h
  apply Measure.le_iff.mpr
  intro A hA
  rw [← hμ, ← hν]
  change (Measure.sum (fun i => μ.restrict (disjointed U i))) A ≤
    (Measure.sum (fun i => ν.restrict (disjointed U i))) A
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  exact ENNReal.tsum_le_tsum fun i => Measure.le_iff'.mp (hdi i) A


variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

private theorem chart_measure_apply
    (T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))) (hT : IsFullPositive T)
    (e : ComplexChart (m+1) M) (s : Set M) :
    chartACMeasure T hT e s =
      acTopMeasure (isPositive_chartSpanCurrent T hT e) (e.val.target ∩ e.val.symm ⁻¹' s) := by
  let j : e.val.target → M := fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m+1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  change ((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
    (Subtype.val : e.val.target → ComplexModel (m+1))).map j s = _
  rw [hj.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hz,hzs⟩
    exact ⟨⟨z,hz⟩,hzs,rfl⟩

/-- A natural calibration of actual original chart densities, not an
inequality for the desired limit, gives the complete global AC measure order. -/
theorem globalACtopMeasure_le_of_calibrated_filter [CompactSpace M]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (T : ι → GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (T₀ R : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (hT : ∀ k, IsFullPositive (T k)) (hT₀ : IsFullPositive T₀) (hR : IsFullPositive R)
    (hconv : ∀ (e : ComplexChart (m+1) M) γ φ,
      Tendsto (fun k => chartSpanCurrent (T k) e γ φ) l
        (𝓝 (chartSpanCurrent T₀ e γ φ)))
    {c : ι → ℝ} {a : ℝ} (hc : ∀ k, 0 ≤ c k) (hca : Tendsto c l (𝓝 a))
    (hcal : ∀ k (e : ComplexChart (m+1) M), ∀ᵐ x ∂volume.restrict (chartTarget e),
      actualTopPowerDensity (acForm (isPositive_chartSpanCurrent (T k) (hT k) e) x) =
        c k * actualTopPowerDensity (acForm (isPositive_chartSpanCurrent R hR e) x)) :
    ENNReal.ofReal a • globalACtopMeasure R hR ≤ globalACtopMeasure T₀ hT₀ := by
  classical
  have hlocal (e : ComplexChart (m+1) M) :
      (ENNReal.ofReal a • globalACtopMeasure R hR).restrict e.val.source ≤
        (globalACtopMeasure T₀ hT₀).restrict e.val.source := by
    have hcomparison := acTopMeasure_le_of_calibrated_filter
      (fun i => isPositive_chartSpanCurrent (T i) (hT i) e)
      (isPositive_chartSpanCurrent T₀ hT₀ e)
      (isPositive_chartSpanCurrent R hR e) (hconv e) hc hca (fun i => hcal i e)
    rw [Measure.restrict_smul,globalACtopMeasure_restrict_chart,
      globalACtopMeasure_restrict_chart]
    apply Measure.le_iff'.mpr
    intro A
    rw [Measure.smul_apply,chart_measure_apply,chart_measure_apply]
    have hA := Measure.le_iff'.mp hcomparison (e.val.target ∩ e.val.symm ⁻¹' A)
    simpa only [Measure.smul_apply] using hA
  let U : M → Set M := fun x => (complexChartAt (n := m+1) x).val.source
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (complexChartAt (n := m+1) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x,mem_complexChartAt_source x⟩)
  let E : Fin (Fintype.card t) → ComplexChart (m+1) M :=
    fun i => complexChartAt ((Fintype.equivFin t).symm i).val
  have hcover : ⋃ i, (E i).val.source = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨y,hyt,hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    refine mem_iUnion.mpr ⟨(Fintype.equivFin t) ⟨y,hyt⟩,?_⟩
    simpa only [E,Equiv.symm_apply_apply] using hxy
  exact measure_le_of_finite_restrictions (fun i => (E i).val.source)
    (fun i => (E i).val.open_source.measurableSet) hcover (fun i => hlocal (E i))

end SGPT.Foundations.Analysis.Pending.GlobalFilterCalibratedCurrentACLimit
