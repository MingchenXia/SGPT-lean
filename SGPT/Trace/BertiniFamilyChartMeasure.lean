import SGPT.Trace.BertiniFamilyDensityTransport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Genuine inverse-chart measures for the actual matched family density. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

private def actualChartInverse {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (e : ComplexChart n Y) : e.val.target → Y :=
  fun z => e.val.symm z.val

private theorem actualChartInverse_measurableEmbedding {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : ComplexChart n Y) : MeasurableEmbedding (actualChartInverse e) :=
  (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
    e.val.toHomeomorphSourceTarget.symm.measurableEmbedding

private theorem actualChartImage_measurable {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : ComplexChart n Y) (A : Set Y) (hA : MeasurableSet A) (hs : A ⊆ e.val.source) :
    MeasurableSet (e.val '' A) := by
  let g : e.val.target → Y := actualChartInverse e
  have hg : Continuous g := e.val.continuousOn_symm.domRestrict
  have hm := e.val.open_target.measurableSet.subtype_image (hA.preimage hg.measurable)
  have hset : e.val '' A = (Subtype.val : e.val.target → ComplexModel n) '' (g ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨e.val x, e.val.map_source (hs hx)⟩, ?_, rfl⟩
      change e.val.symm (e.val x) ∈ A
      rw [e.val.left_inv (hs hx)]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.val.symm z.val, hz, e.val.right_inv z.property⟩
  rw [hset]
  exact hm

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyMatchedLocalMeasure :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → Measure (familyIncidence p i a v U) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e
  exact Measure.map (actualChartInverse e)
    ((volume.withDensity (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z))).comap
      (Subtype.val : e.val.target → ComplexModel (d + 1)))

theorem familyMatchedLocalMeasure_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (A : Set (familyIncidence p i a v U)),
      familyMatchedLocalMeasure p i a v U hsm e A =
        (volume.withDensity (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z)))
          (e.val '' (A ∩ e.val.source)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e A
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (d + 1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  rw [familyMatchedLocalMeasure, (actualChartInverse_measurableEmbedding e).map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨e.val.symm w.val, ⟨hw, e.val.map_target w.property⟩, e.val.right_inv w.property⟩
  · rintro ⟨x, ⟨hxA, hxs⟩, rfl⟩
    refine ⟨⟨e.val x, e.val.map_source hxs⟩, ?_, rfl⟩
    change e.val.symm (e.val x) ∈ A
    rwa [e.val.left_inv hxs]

theorem familyMatchedLocalMeasure_source :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)),
      (familyMatchedLocalMeasure p i a v U hsm e).restrict e.val.source =
        familyMatchedLocalMeasure p i a v U hsm e := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  change familyMatchedLocalMeasure p i a v U hsm e e.val.sourceᶜ = 0
  rw [familyMatchedLocalMeasure_apply p i a v U hsm e, compl_inter_self, image_empty, measure_empty]

theorem familyMatchedLocalMeasure_overlap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U)),
      (familyMatchedLocalMeasure p i a v U hsm e).restrict (e.val.source ∩ f.val.source) =
        (familyMatchedLocalMeasure p i a v U hsm f).restrict (e.val.source ∩ f.val.source) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  let B := A ∩ (e.val.source ∩ f.val.source)
  have hB : MeasurableSet B := hA.inter (e.val.open_source.measurableSet.inter f.val.open_source.measurableSet)
  have he : B ⊆ e.val.source := fun _ hx => hx.2.1
  have hf : B ⊆ f.val.source := fun _ hx => hx.2.2
  rw [familyMatchedLocalMeasure_apply p i a v U hsm e,
    familyMatchedLocalMeasure_apply p i a v U hsm f]
  change (volume.withDensity (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z)))
      (e.val '' (B ∩ e.val.source)) =
    (volume.withDensity (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm f z)))
      (f.val '' (B ∩ f.val.source))
  rw [inter_eq_left.mpr he, inter_eq_left.mpr hf,
    withDensity_apply _ (actualChartImage_measurable e B hB he),
    withDensity_apply _ (actualChartImage_measurable f B hB hf)]
  have hsub : f.val '' B ⊆ coordinateDomain id f e := by
    rintro z ⟨x, hx, rfl⟩
    exact mem_coordinateDomain (hf hx) (he hx)
  have hset : (coordinateMap id f e) '' (f.val '' B) = e.val '' B := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change e.val x = e.val (f.val.symm (f.val x))
      rw [f.val.left_inv (hf hx)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨f.val x, ⟨x, hx, rfl⟩, ?_⟩
      change e.val (f.val.symm (f.val x)) = e.val x
      rw [f.val.left_inv (hf hx)]
  have h := familyMatchedCoordinateIntegral_change p i a v U hsm e f (f.val '' B)
    (actualChartImage_measurable f B hB hf) hsub (fun _ => 1)
  rw [hset] at h
  simpa only [mul_one] using h

theorem familyMatchedLocalMeasure_map :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)),
      Measure.map e.val ((familyMatchedLocalMeasure p i a v U hsm e).restrict e.val.source) =
        (volume.restrict e.val.target).withDensity
          (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e
  have hm : AEMeasurable e.val (familyMatchedLocalMeasure p i a v U hsm e) := by
    have h := e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
      (μ := familyMatchedLocalMeasure p i a v U hsm e)
    rwa [familyMatchedLocalMeasure_source p i a v U hsm e] at h
  rw [familyMatchedLocalMeasure_source p i a v U hsm e]
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply_of_aemeasurable hm hA, familyMatchedLocalMeasure_apply p i a v U hsm e,
    ← restrict_withDensity e.val.open_target.measurableSet, Measure.restrict_apply hA]
  congr 1
  ext z
  constructor
  · rintro ⟨q, ⟨hqA, hqs⟩, rfl⟩
    exact ⟨hqA, e.val.map_source hqs⟩
  · rintro ⟨hzA, hzt⟩
    exact ⟨e.val.symm z, ⟨by
      change e.val (e.val.symm z) ∈ A
      rwa [e.val.right_inv hzt], e.val.map_target hzt⟩, e.val.right_inv hzt⟩

end SGPT.Trace.BertiniFamilyCanonical
