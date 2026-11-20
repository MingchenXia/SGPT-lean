import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.FirstPass.ManifoldPluripolar

set_option autoImplicit false

/-! The original canonical global AC top measure is genuinely noncharging.
ENTIRE BP statement/proof before Lean; no finite determinant or closedness
assumption, no selected atlas/nullity certificate. All actual mass may be infinity. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.GlobalACTopPluripolarNull
open FirstPass GlobalCurrents GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity
  PositiveCurrentACTopMeasure LocalCurrentDeterminant

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem chartACMeasure_apply
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M) (S : Set M) :
    chartACMeasure T hT e S =
      acTopMeasure (isPositive_chartSpanCurrent T hT e) (pluripolarChartSet S e) := by
  have hInv : MeasurableEmbedding (fun z : e.val.target => e.val.symm z) :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m + 1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  change (((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
      (Subtype.val : e.val.target → ComplexModel (m + 1))).map
        (fun z : e.val.target => e.val.symm z)) S = _
  rw [hInv.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · intro hz
    exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩

/-- Every original chart's actual AC top measure has zero outer mass on every
natural manifold-locally pluripolar set, without Compact/closed/finite input. -/
theorem chartACMeasure_pluripolar_eq_zero
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) {S : Set M}
    (hS : ManifoldLocallyPluripolar (n := m + 1) S) (e : ComplexChart (m + 1) M) :
    chartACMeasure T hT e S = 0 := by
  rw [chartACMeasure_apply]
  have hac : acTopMeasure (isPositive_chartSpanCurrent T hT e) ≪
      (volume : Measure (ComplexModel (m + 1))) :=
    Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _)
  exact hac (hS.chart_measure_eq_zero e volume)

omit [MeasurableSpace M] [BorelSpace M] [IsComplexManifold (m + 1) M] in
private theorem exists_finite_original_charts [CompactSpace M] :
    ∃ k : ℕ, ∃ E : Fin k → ComplexChart (m + 1) M,
      ∀ x : M, ∃ i, x ∈ (E i).val.source := by
  classical
  let U : M → Set M := fun x => (complexChartAt (n := m + 1) x).val.source
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (complexChartAt (n := m + 1) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  let a := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun i => complexChartAt (a i).val, fun x => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  refine ⟨a.symm ⟨y, hyt⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hxy

/-- The SAME original atlas-independent AC top measure does not charge any
natural manifold-locally pluripolar set. Compactness internally supplies its
finite original cover; no atlas, finite mass or nullity certificate is input. -/
theorem globalACtopMeasure_doesNotCharge_pluripolar [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) :
    DoesNotChargeManifoldPluripolar (n := m + 1) (globalACtopMeasure T hT) := by
  intro S hS
  have hlocal (e : ComplexChart (m + 1) M) :
      globalACtopMeasure T hT (S ∩ e.val.source) = 0 := by
    have he := congrArg (fun μ : Measure M => μ S) (globalACtopMeasure_restrict_chart T hT e)
    rw [Measure.restrict_apply' e.val.open_source.measurableSet] at he
    exact he.trans (chartACMeasure_pluripolar_eq_zero T hT hS e)
  obtain ⟨k, E, hcover⟩ := exists_finite_original_charts (m := m) (M := M)
  have hsub : S ⊆ ⋃ i : Fin k, S ∩ (E i).val.source := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  exact measure_mono_null hsub (measure_iUnion_null (fun i => hlocal (E i)))

end SGPT.Foundations.Analysis.Pending.GlobalACTopPluripolarNull
