import SGPT.PSH.HermitianProducts
import SGPT.Foundations.Analysis.FirstPass.FiniteMeasureGluing
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Gluing genuine local top-degree product traces

Coordinate transport and measure gluing require no local potential for a
background form. The local inputs are actual positive coefficient-distribution
currents, and overlap hypotheses are ordinary equalities of measures.
The constructor below is the measure-theoretic part of the nonclosed product;
producing its overlap equalities for the background expansion is a separate
analytic theorem, not an assumption hidden in a global-product definition.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A coordinate patch contains geometric chart data only. In particular,
there is no closed background or local exact potential in this structure. -/
structure CoordinatePatch (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] where
  chart : ComplexChart n M
  domain : Opens (ComplexModel n)
  domain_le_target : (domain : Set (ComplexModel n)) ⊆ chart.val.target

namespace CoordinatePatch

/-- The actual manifold domain corresponding to the coordinate patch. -/
def source (P : CoordinatePatch n M) : Opens M :=
  ⟨P.chart.val.source ∩ P.chart.val ⁻¹' P.domain,
    P.chart.val.isOpen_inter_preimage P.domain.isOpen⟩

theorem map_source (P : CoordinatePatch n M) {x : M} (hx : x ∈ P.source) :
    P.chart.val x ∈ P.domain := hx.2

theorem map_target (P : CoordinatePatch n M) {z : ComplexModel n} (hz : z ∈ P.domain) :
    P.chart.val.symm z ∈ P.source := by
  refine ⟨P.chart.val.map_target (P.domain_le_target hz), ?_⟩
  change P.chart.val (P.chart.val.symm z) ∈ P.domain
  rwa [P.chart.val.right_inv (P.domain_le_target hz)]

/-- The ordinary homeomorphism between the source and coordinate domain. -/
def homeomorph (P : CoordinatePatch n M) : P.source ≃ₜ P.domain where
  toFun x := ⟨P.chart.val x, P.map_source x.property⟩
  invFun z := ⟨P.chart.val.symm z, P.map_target z.property⟩
  left_inv x := Subtype.ext (P.chart.val.left_inv x.property.1)
  right_inv z := Subtype.ext (P.chart.val.right_inv (P.domain_le_target z.property))
  continuous_toFun := (P.chart.val.continuousOn.mono inter_subset_left).mapsToRestrict
    (fun _ hx => P.map_source hx)
  continuous_invFun := (P.chart.val.symm.continuousOn.mono
    P.domain_le_target).mapsToRestrict (fun _ hz => P.map_target hz)

/-- Only the inverse chart on its genuine domain is used. -/
def toManifold (P : CoordinatePatch n M) : P.domain → M :=
  fun z => (P.homeomorph.symm z : M)

@[simp] theorem toManifold_apply (P : CoordinatePatch n M) (z : P.domain) :
    P.toManifold z = P.chart.val.symm z := rfl

variable [MeasurableSpace M] [BorelSpace M]

theorem measurableEmbedding_toManifold (P : CoordinatePatch n M) :
    MeasurableEmbedding P.toManifold :=
  (MeasurableEmbedding.subtype_coe P.source.isOpen.measurableSet).comp
    P.homeomorph.symm.measurableEmbedding

/-- Transport a coordinate measure and extend it by zero outside the patch.
Neither of the arbitrary chart extensions is asserted globally measurable. -/
def pushMeasure (P : CoordinatePatch n M) (μ : Measure (ComplexModel n)) : Measure M :=
  (μ.comap (Subtype.val : P.domain → ComplexModel n)).map P.toManifold

/-- The exact evaluation identity, including nonmeasurable sets. -/
theorem pushMeasure_apply (P : CoordinatePatch n M) (μ : Measure (ComplexModel n))
    (s : Set M) :
    P.pushMeasure μ s = μ ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' s) := by
  have hsub : MeasurableEmbedding (Subtype.val : P.domain → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe P.domain.isOpen.measurableSet
  rw [pushMeasure, P.measurableEmbedding_toManifold.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hzs⟩
    exact ⟨⟨z, hz⟩, hzs, rfl⟩

theorem pushMeasure_apply_image (P : CoordinatePatch n M) (μ : Measure (ComplexModel n))
    (s : Set M) :
    P.pushMeasure μ s = μ (P.chart.val '' (s ∩ (P.source : Set M))) := by
  rw [P.pushMeasure_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hzs⟩
    exact ⟨P.chart.val.symm z, ⟨hzs, P.map_target hz⟩,
      P.chart.val.right_inv (P.domain_le_target hz)⟩
  · rintro ⟨x, ⟨hxs, hx⟩, rfl⟩
    refine ⟨P.map_source hx, ?_⟩
    change P.chart.val.symm (P.chart.val x) ∈ s
    rwa [P.chart.val.left_inv hx.1]

theorem pushMeasure_source_compl (P : CoordinatePatch n M) (μ : Measure (ComplexModel n)) :
    P.pushMeasure μ (P.source : Set M)ᶜ = 0 := by
  rw [P.pushMeasure_apply_image, compl_inter_self, image_empty, measure_empty]

theorem pushMeasure_restrict_source (P : CoordinatePatch n M) (μ : Measure (ComplexModel n)) :
    (P.pushMeasure μ).restrict P.source = P.pushMeasure μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr (P.pushMeasure_source_compl μ)

/-- A positive top-degree current supplies its actual Riesz trace measure. -/
def pushTraceMeasure (P : CoordinatePatch n M)
    (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T) : Measure M :=
  P.pushMeasure hT.traceMeasure

/-- Local finite mass is produced from the Riesz measure of the current,
not supplied as a separate mass certificate. -/
theorem pushTraceMeasure_finiteAtNhds (P : CoordinatePatch n M)
    (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T)
    {x : M} (hx : x ∈ P.source) :
    (P.pushTraceMeasure T hT).FiniteAtFilter (𝓝 x) := by
  obtain ⟨K, hK, hxK, hKP⟩ := exists_compact_subset P.domain.isOpen (P.map_source hx)
  let V : Set M := P.chart.val.source ∩ P.chart.val ⁻¹' interior K
  have hV : IsOpen V := P.chart.val.isOpen_inter_preimage isOpen_interior
  have hxV : x ∈ V := ⟨hx.1, hxK⟩
  refine ⟨V, hV.mem_nhds hxV, ?_⟩
  rw [pushTraceMeasure, P.pushMeasure_apply_image]
  refine lt_of_le_of_lt (measure_mono ?_) (hT.traceMeasure_lt_top hK hKP)
  rintro _ ⟨y, ⟨hyV, _⟩, rfl⟩
  exact interior_subset hyV.2

end CoordinatePatch

variable [MeasurableSpace M] [BorelSpace M] {a : ℕ}

/-- Glue the actual transported current traces by a disjoint finite sum.
No compatibility or finiteness hypothesis enters the constructor. -/
def glueTraceMeasure (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i)) : Measure M :=
  FiniteMeasureGluing.glue (fun i => ((P i).source : Set M))
    (fun i => (P i).pushTraceMeasure (T i) (hT i))

/-- Genuine equality of the transported measures on pairwise overlaps. -/
def TraceMeasuresAgree (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i)) : Prop :=
  ∀ i j, ((P i).pushTraceMeasure (T i) (hT i)).restrict
      ((P i).source ∩ (P j).source : Set M) =
    ((P j).pushTraceMeasure (T j) (hT j)).restrict
      ((P i).source ∩ (P j).source : Set M)

/-- Ordinary overlap equalities identify each genuine local trace. -/
theorem glueTraceMeasure_restrict (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i))
    (hagree : TraceMeasuresAgree P T hT) (j : Fin a) :
    (glueTraceMeasure P T hT).restrict (P j).source =
      (P j).pushTraceMeasure (T j) (hT j) := by
  rw [glueTraceMeasure, FiniteMeasureGluing.glue_restrict_member _ _
    (fun i => (P i).source.isOpen.measurableSet) hagree j]
  exact (P j).pushMeasure_restrict_source (hT j).traceMeasure

/-- Local finiteness follows from actual current traces and a covering,
without a prescribed global mass bound. -/
theorem glueTraceMeasure_isLocallyFiniteMeasure (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i))
    (hcover : ∀ x : M, ∃ i, x ∈ (P i).source)
    (hagree : TraceMeasuresAgree P T hT) :
    IsLocallyFiniteMeasure (glueTraceMeasure P T hT) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨V, hV, hfinite⟩ := (P i).pushTraceMeasure_finiteAtNhds (T i) (hT i) hxi
  refine ⟨V ∩ ((P i).source : Set M),
    inter_mem hV ((P i).source.isOpen.mem_nhds hxi), ?_⟩
  calc
    glueTraceMeasure P T hT (V ∩ ((P i).source : Set M)) =
        (glueTraceMeasure P T hT).restrict (P i).source V :=
      (Measure.restrict_apply' (P i).source.isOpen.measurableSet).symm
    _ = (P i).pushTraceMeasure (T i) (hT i) V := congrArg (fun μ : Measure M => μ V)
      (glueTraceMeasure_restrict P T hT hagree i)
    _ < ⊤ := hfinite

/-- Compactness upgrades the proved local finite mass to finite total mass. -/
theorem glueTraceMeasure_isFiniteMeasure [CompactSpace M]
    (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i))
    (hcover : ∀ x : M, ∃ i, x ∈ (P i).source)
    (hagree : TraceMeasuresAgree P T hT) :
    IsFiniteMeasure (glueTraceMeasure P T hT) := by
  let := glueTraceMeasure_isLocallyFiniteMeasure P T hT hcover hagree
  infer_instance

/-- The global measure is uniquely determined by its genuine patch traces. -/
theorem glueTraceMeasure_unique (P : Fin a → CoordinatePatch n M)
    (T : ∀ i, LocalProductCurrent n (P i).domain 0) (hT : ∀ i, IsPositive (T i))
    (hcover : ∀ x : M, ∃ i, x ∈ (P i).source)
    (hagree : TraceMeasuresAgree P T hT) (ν : Measure M)
    (hν : ∀ i, ν.restrict (P i).source = (P i).pushTraceMeasure (T i) (hT i)) :
    glueTraceMeasure P T hT = ν := by
  apply FiniteMeasureGluing.ext_of_restrict_eq (fun i => ((P i).source : Set M))
    (fun i => (P i).source.isOpen.measurableSet) ?_
    (fun i => (glueTraceMeasure_restrict P T hT hagree i).trans (hν i).symm)
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact hcover x

end SGPT.PSH.HermitianGlobalProducts
