import SGPT.Trace.BertiniFamilyChartMeasure
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Order.Disjointed

/-! Actual matched positive volume on the original noncompact full family. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

private theorem actualCountableGlue_restrict {Y : Type} [MeasurableSpace Y]
    (V : ℕ → Set Y) (μ : ℕ → Measure Y) (hV : ∀ j, MeasurableSet (V j))
    {W : Set Y} (hW : MeasurableSet W) (hcover : W ⊆ ⋃ j, V j)
    (ν : Measure Y) (hcompat : ∀ j, (μ j).restrict (V j ∩ W) = ν.restrict (V j ∩ W)) :
    (Measure.sum (fun j => (μ j).restrict (disjointed V j))).restrict W = ν.restrict W := by
  have hD (j : ℕ) : MeasurableSet (disjointed V j) :=
    disjointedRec (p := MeasurableSet) (fun {_t k} ht => ht.diff (hV k)) (hV j)
  have hpiece (j : ℕ) : ((μ j).restrict (disjointed V j)).restrict W =
      ν.restrict (W ∩ disjointed V j) := by
    rw [Measure.restrict_restrict hW]
    have hsub : W ∩ disjointed V j ⊆ V j ∩ W :=
      fun _ hx => ⟨disjointed_subset V j hx.2, hx.1⟩
    have h := congrArg (fun κ : Measure Y => κ.restrict (W ∩ disjointed V j)) (hcompat j)
    simpa only [Measure.restrict_restrict_of_subset hsub] using h
  have hd : Pairwise (fun j k => Disjoint (W ∩ disjointed V j) (W ∩ disjointed V k)) := by
    intro j k hjk
    exact (disjoint_disjointed V hjk).mono inter_subset_right inter_subset_right
  rw [Measure.restrict_sum _ hW]
  simp_rw [hpiece]
  rw [← Measure.restrict_iUnion hd (fun j => hW.inter (hD j))]
  congr 1
  rw [← inter_iUnion, iUnion_disjointed]
  exact inter_eq_left.mpr hcover

private theorem actualCountablePreferredCover {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [Nonempty Y] :
    ∃ c : ℕ → Y, (⋃ j, (complexChartAt (n := n) (c j)).val.source) = univ := by
  classical
  let V : Y → Set Y := fun y => (complexChartAt (n := n) y).val.source
  have hV : ∀ y, IsOpen (V y) := fun y => (complexChartAt (n := n) y).val.open_source
  have hcover : (univ : Set Y) ⊆ ⋃ y, V y := by
    intro y _
    exact mem_iUnion.mpr ⟨y, mem_complexChartAt_source y⟩
  obtain ⟨A, hAc, hA⟩ := isLindelof_univ.elim_countable_subcover V hV hcover
  let c := enumerateCountable hAc (Classical.choice (inferInstance : Nonempty Y))
  refine ⟨c, eq_univ_of_forall fun y => ?_⟩
  obtain ⟨x, hxA, hyx⟩ := mem_iUnion₂.mp (hA (mem_univ y))
  obtain ⟨j, hj⟩ := subset_range_enumerate hAc (Classical.choice (inferInstance : Nonempty Y)) hxA
  exact mem_iUnion.mpr ⟨j, by simpa only [c, hj] using hyx⟩

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem exists_familyMatchedVolume :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ μ : Measure (familyIncidence p i a v U),
      ∀ e : ComplexChart (d + 1) (familyIncidence p i a v U),
      Measure.map e.val (μ.restrict e.val.source) = (volume.restrict e.val.target).withDensity
        (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z)) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  by_cases hne : Nonempty (familyIncidence p i a v U)
  · let := hne
    obtain ⟨c, hc⟩ := actualCountablePreferredCover (n := d + 1) (Y := familyIncidence p i a v U)
    let e := fun j => complexChartAt (n := d + 1) (c j)
    let V := fun j => (e j).val.source
    let μ := fun j => familyMatchedLocalMeasure p i a v U hsm (e j)
    let ν := Measure.sum (fun j => (μ j).restrict (disjointed V j))
    refine ⟨ν, ?_⟩
    intro f
    have hrestrict : ν.restrict f.val.source =
        (familyMatchedLocalMeasure p i a v U hsm f).restrict f.val.source := by
      apply actualCountableGlue_restrict V μ (fun j => (e j).val.open_source.measurableSet)
        f.val.open_source.measurableSet
      · change f.val.source ⊆ ⋃ j, (complexChartAt (n := d + 1) (c j)).val.source
        rw [hc]
        exact subset_univ _
      · intro j
        exact familyMatchedLocalMeasure_overlap p i a v U hsm (e j) f
    rw [hrestrict]
    exact familyMatchedLocalMeasure_map p i a v U hsm f
  · have htarget (e : ComplexChart (d + 1) (familyIncidence p i a v U)) : e.val.target = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z _hz
      exact hne ⟨e.val.symm z⟩
    refine ⟨0, ?_⟩
    intro e
    simp [htarget e]

def familyMatchedVolume : Measure (familyIncidence p i a v U) :=
  (exists_familyMatchedVolume p i a v U hsm).choose

theorem familyMatchedVolume_chart :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ e : ComplexChart (d + 1) (familyIncidence p i a v U),
      Measure.map e.val ((familyMatchedVolume p i a v U hsm).restrict e.val.source) =
        (volume.restrict e.val.target).withDensity
          (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z)) := by
  exact (exists_familyMatchedVolume p i a v U hsm).choose_spec

theorem familyMatchedVolume_smoothPositive :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    IsSmoothPositiveVolume (n := d + 1) (familyMatchedVolume p i a v U hsm) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e
  exact ⟨familyMatchedCoordinateDensity p i a v U hsm e,
    familyMatchedCoordinateDensity_smooth p i a v U hsm e,
    familyMatchedCoordinateDensity_pos p i a v U hsm e,
    familyMatchedVolume_chart p i a v U hsm e⟩

end SGPT.Trace.BertiniFamilyCanonical
