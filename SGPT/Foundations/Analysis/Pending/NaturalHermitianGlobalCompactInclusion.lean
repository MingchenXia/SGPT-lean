import SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalNormReconstruction
import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakResolvent

/-! # Actual compact graph inclusion and original shifted weak resolvent -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalCompactInclusion

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2 NaturalHermitianGraphEnergy
  NaturalHermitianWeakResolvent NaturalHermitianFiniteChartLocalizers
  NaturalHermitianGlobalNormReconstruction NaturalHermitianSmoothFormMetric
  NaturalCoefficientSobolevRellich

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

local instance graphNormedAddCommGroup (w : KahlerBackground n M) (k : ℕ) :
    NormedAddCommGroup (GraphEnergy w k) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w k)

local instance graphInnerProductSpace (w : KahlerBackground n M) (k : ℕ) :
    InnerProductSpace ℝ (GraphEnergy w k) :=
  Submodule.innerProductSpace (graphEnergySubmodule w k)

/-- The literal finite tuple is compact because every actual full-graph chart value is genuinely compact. -/
theorem finiteChartValueTupleCLM_isCompactOperator {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) : IsCompactOperator (finiteChartValueTupleCLM D) := by
  change (∑ i, (finiteChartValueSingleCLM D i).comp (finiteChartValueCLM D i)) ∈
    compactOperator (RingHom.id ℝ) (GraphEnergy w q)
      (PiLp 2 (fun _ : Fin D.card => CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)))
  apply Submodule.sum_mem
  intro i _
  exact (finiteChartValueCLM_isCompactOperator D i).clm_comp (finiteChartValueSingleCLM D i)

/-- The actual closed linear range closure in the same original finite native Hilbert product. -/
def finiteValueRangeClosure {w : KahlerBackground n M} (D : FiniteChartLocalization w q) :
    Submodule ℝ (PiLp 2 (fun _ : Fin D.card =>
      CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q))) :=
  (finiteChartValueTupleCLM D).toLinearMap.range.topologicalClosure

/-- The genuine continuous linear codomain restriction into that actual range closure. -/
def finiteValueRangeCLM {w : KahlerBackground n M} (D : FiniteChartLocalization w q) :
    GraphEnergy w q →L[ℝ] finiteValueRangeClosure D :=
  (finiteChartValueTupleCLM D).codRestrict (finiteValueRangeClosure D)
    (fun u => (finiteChartValueTupleCLM D).toLinearMap.range.le_topologicalClosure ⟨u, rfl⟩)

/-- The whole actual finite native value tuple is the literal subtype value. -/
theorem finiteValueRangeCLM_apply {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (u : GraphEnergy w q) :
    (finiteValueRangeCLM D u).val = finiteChartValueTupleCLM D u := rfl

theorem finiteValueRangeClosure_isClosed {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) :
    IsClosed (finiteValueRangeClosure D : Set (PiLp 2 (fun _ : Fin D.card =>
      CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q)))) :=
  (finiteChartValueTupleCLM D).toLinearMap.range.isClosed_topologicalClosure

/-- Dense range is proved from the literal closure construction, without closed range of the original tuple. -/
theorem finiteValueRangeCLM_denseRange {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) : DenseRange (finiteValueRangeCLM D) := by
  change Dense (range (finiteValueRangeCLM D))
  rw [Subtype.dense_iff]
  have himage : (Subtype.val : finiteValueRangeClosure D →
      PiLp 2 (fun _ : Fin D.card => CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q))) ''
      range (finiteValueRangeCLM D) = range (finiteChartValueTupleCLM D) := by
    ext x
    constructor
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨finiteValueRangeCLM D u, ⟨u, rfl⟩, rfl⟩
  intro x hx
  change x ∈ closure (range (finiteChartValueTupleCLM D)) at hx
  exact (congrArg closure himage).symm ▸ hx

/-- Actual compactness survives codomain restriction to the genuine closed range closure. -/
theorem finiteValueRangeCLM_isCompactOperator {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) : IsCompactOperator (finiteValueRangeCLM D) :=
  (finiteChartValueTupleCLM_isCompactOperator D).codRestrict
    (fun u => (finiteChartValueTupleCLM D).toLinearMap.range.le_topologicalClosure ⟨u, rfl⟩)
    (finiteValueRangeClosure_isClosed D)

/-- Bounded range reconstruction uses the literal original graph inclusion and actual dense codomain restriction. -/
def finiteValueReconstructionCLM {w : KahlerBackground n M} (D : FiniteChartLocalization w q) :
    finiteValueRangeClosure D →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  (energyInclusion w q).toLinearMap.extendOfNorm (finiteValueRangeCLM D).toLinearMap

/-- The earlier internally proved whole-graph bound eliminates the fallback and gives exact original inclusion readback. -/
theorem finiteValueReconstructionCLM_readback {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) (u : GraphEnergy w q) :
    finiteValueReconstructionCLM D (finiteValueRangeCLM D u) = energyInclusion w q u := by
  obtain ⟨B, hB, hbound⟩ := whole_graph_finite_value_norm_reconstruction D
  let H := HilbertFormL2 w.form.val w.isKahler.1 q
  let _ : NormedSpace ℝ H := inferInstance
  let f : GraphEnergy w q →ₗ[ℝ] H := (energyInclusion w q).toLinearMap
  let j : GraphEnergy w q →ₗ[ℝ] finiteValueRangeClosure D := (finiteValueRangeCLM D).toLinearMap
  change f.extendOfNorm j (j u) = f u
  exact LinearMap.extendOfNorm_eq (f := f) (e := j)
    (finiteValueRangeCLM_denseRange D) ⟨Real.sqrt B, hbound⟩ u

/-- The actual entire reconstruction inherits an internally positive full norm bound. -/
theorem finiteValueReconstructionCLM_norm_le {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q) :
    ∃ B > 0, ∀ v : finiteValueRangeClosure D,
      ‖finiteValueReconstructionCLM D v‖ ≤ Real.sqrt B * ‖v‖ := by
  obtain ⟨B, hB, hbound⟩ := whole_graph_finite_value_norm_reconstruction D
  let H := HilbertFormL2 w.form.val w.isKahler.1 q
  let _ : NormedSpace ℝ H := inferInstance
  let f : GraphEnergy w q →ₗ[ℝ] H := (energyInclusion w q).toLinearMap
  let j : GraphEnergy w q →ₗ[ℝ] finiteValueRangeClosure D := (finiteValueRangeCLM D).toLinearMap
  refine ⟨B, hB, ?_⟩
  change ∀ v, ‖f.extendOfNorm j v‖ ≤ Real.sqrt B * ‖v‖
  exact LinearMap.norm_extendOfNorm_apply_le (f := f) (e := j)
    (finiteValueRangeCLM_denseRange D) (Real.sqrt B) hbound

/-- Continuous linear reconstruction is genuinely unique on the actual range closure. -/
theorem finiteValueReconstructionCLM_unique {w : KahlerBackground n M}
    (D : FiniteChartLocalization w q)
    (K : finiteValueRangeClosure D →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q)
    (hK : ∀ u : GraphEnergy w q, K (finiteValueRangeCLM D u) = energyInclusion w q u) :
    K = finiteValueReconstructionCLM D := by
  obtain ⟨B, hB, hbound⟩ := whole_graph_finite_value_norm_reconstruction D
  symm
  apply LinearMap.extendOfNorm_unique (finiteValueRangeCLM_denseRange D) (Real.sqrt B) hbound K
  apply LinearMap.ext
  intro u
  exact hK u

/-- Genuine compactness of the literal original graph inclusion, with only the original background and degree supplied. -/
theorem isCompactOperator_energyInclusion (w : KahlerBackground n M) (q : ℕ) :
    IsCompactOperator (energyInclusion w q) := by
  obtain ⟨D⟩ := exists_finiteChartLocalization w q
  have hfactor : (finiteValueReconstructionCLM D).comp (finiteValueRangeCLM D) =
      energyInclusion w q := by
    apply ContinuousLinearMap.ext
    intro u
    exact finiteValueReconstructionCLM_readback D u
  have hcompact : IsCompactOperator
      ((finiteValueReconstructionCLM D).comp (finiteValueRangeCLM D)) :=
    (finiteValueRangeCLM_isCompactOperator D).clm_comp (finiteValueReconstructionCLM D)
  rw [hfactor] at hcompact
  exact hcompact

/-- The literal original shifted weak resolvent is compact on the entire original form Hilbert completion. -/
theorem isCompactOperator_shiftedWeakResolvent (w : KahlerBackground n M) (q : ℕ) :
    IsCompactOperator (shiftedWeakResolvent w q) :=
  (isCompactOperator_energyInclusion w q).comp_clm (energySolution w q)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalCompactInclusion
