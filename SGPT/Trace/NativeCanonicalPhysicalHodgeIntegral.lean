import SGPT.Trace.NativeCanonicalPhysicalChartIntegral
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.EquivFin

/-! Global intrinsic physical canonical energy from PRODUCED actual chart covers.
No metric on K and no supplied global-Hodge output certificate is used. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [MeasurableSpace X] [BorelSpace X]

structure NativeCanonicalChartPartition (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [MeasurableSpace X] where
  size : ℕ
  chart : Fin size → ComplexChart n X
  piece : Fin size → Set X
  measurable_piece : ∀ i, MeasurableSet (piece i)
  piece_subset : ∀ i, piece i ⊆ (chart i).val.source
  disjoint_piece : Pairwise (fun i j => Disjoint (piece i) (piece j))
  cover : ⋃ i, piece i = univ

theorem exists_nativeCanonicalChartPartition [CompactSpace X] :
    Nonempty (NativeCanonicalChartPartition n X) := by
  classical
  let U : X → Set X := fun x => (complexChartAt (n := n) x).val.source
  have hU : ∀ x, IsOpen (U x) := fun x => (complexChartAt (n := n) x).val.open_source
  have hc : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover U hU hc
  let a : Fin A.card → X := fun k => (A.equivFin.symm k).val
  let V : Fin A.card → Set X := fun k => U (a k)
  have hV : ∀ k, MeasurableSet (V k) := fun k => (hU (a k)).measurableSet
  have hcover : ⋃ k, V k = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hyA, hxy⟩ := mem_iUnion₂.mp (hA (mem_univ x))
    refine mem_iUnion.mpr ⟨A.equivFin ⟨y, hyA⟩, ?_⟩
    simpa only [V, a, Equiv.symm_apply_apply] using hxy
  refine ⟨{ size := A.card
            chart := fun k => complexChartAt (n := n) (a k)
            piece := disjointed V
            measurable_piece := ?_
            piece_subset := disjointed_subset V
            disjoint_piece := disjoint_disjointed V
            cover := ?_ }⟩
  · intro k
    exact disjointedRec (fun {t j} ht => ht.diff (hV j)) (hV k)
  · rw [iUnion_disjointed, hcover]

private theorem actualNativeChart_image_measurable (e : ComplexChart n X)
    (A : Set X) (hA : MeasurableSet A) (hs : A ⊆ e.val.source) :
    MeasurableSet (e.val '' A) := by
  let g : e.val.target → X := fun z => e.val.symm z.val
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

variable [IsComplexManifold n X] [CompactSpace X]
  (L : HermitianHolomorphicLineBundle n X)
  (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)

private theorem actualPhysicalChart_overlap_integral (e f : ComplexChart n X)
    (A : Set X) (hA : MeasurableSet A) (he : A ⊆ e.val.source) (hf : A ⊆ f.val.source) :
    (∫⁻ z in e.val '' A, nativeCanonicalPhysicalCoordinateDensity L S w e z ∂volume) =
      ∫⁻ z in f.val '' A, nativeCanonicalPhysicalCoordinateDensity L S w f z ∂volume := by
  let F := coordinateMap id f e
  have hsub : f.val '' A ⊆ coordinateDomain id f e := by
    rintro z ⟨x, hx, rfl⟩
    exact mem_coordinateDomain (hf hx) (he hx)
  have hset : F '' (f.val '' A) = e.val '' A := by
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
  have h := nativeCanonicalPhysicalCoordinateIntegral_change L S w e f (f.val '' A)
    (actualNativeChart_image_measurable f A hA hf) hsub
  rw [hset] at h
  exact h

def nativeCanonicalPartitionEnergy (P : NativeCanonicalChartPartition n X) : ℝ≥0∞ :=
  ∑ i, ∫⁻ z in (P.chart i).val '' P.piece i,
    nativeCanonicalPhysicalCoordinateDensity L S w (P.chart i) z ∂volume


private theorem actualPartitionEnergy_refine (P Q : NativeCanonicalChartPartition n X) :
    nativeCanonicalPartitionEnergy L S w P =
      ∑ i, ∑ j, ∫⁻ z in (P.chart i).val '' (P.piece i ∩ Q.piece j),
        nativeCanonicalPhysicalCoordinateDensity L S w (P.chart i) z ∂volume := by
  classical
  unfold nativeCanonicalPartitionEnergy
  apply Finset.sum_congr rfl
  intro i _
  have hset : (P.chart i).val '' P.piece i =
      ⋃ j, (P.chart i).val '' (P.piece i ∩ Q.piece j) := by
    rw [← image_iUnion, ← inter_iUnion, Q.cover, inter_univ]
  have hm (j : Fin Q.size) : MeasurableSet ((P.chart i).val '' (P.piece i ∩ Q.piece j)) :=
    actualNativeChart_image_measurable (P.chart i) _
      ((P.measurable_piece i).inter (Q.measurable_piece j))
      (fun _ hx => P.piece_subset i hx.1)
  have hd : Pairwise (fun j k => Disjoint
      ((P.chart i).val '' (P.piece i ∩ Q.piece j))
      ((P.chart i).val '' (P.piece i ∩ Q.piece k))) := by
    intro j k hjk
    apply Set.disjoint_image_image
    intro x hx y hy heq
    have hxy := (P.chart i).val.injOn (P.piece_subset i hx.1) (P.piece_subset i hy.1) heq
    exact (Set.disjoint_left.mp (Q.disjoint_piece hjk)) hx.2 (hxy ▸ hy.2)
  rw [hset, lintegral_iUnion hm hd, tsum_fintype]

theorem nativeCanonicalPartitionEnergy_eq (P Q : NativeCanonicalChartPartition n X) :
    nativeCanonicalPartitionEnergy L S w P = nativeCanonicalPartitionEnergy L S w Q := by
  classical
  rw [actualPartitionEnergy_refine L S w P Q, actualPartitionEnergy_refine L S w Q P]
  calc
    (∑ i, ∑ j, ∫⁻ z in (P.chart i).val '' (P.piece i ∩ Q.piece j),
      nativeCanonicalPhysicalCoordinateDensity L S w (P.chart i) z ∂volume) =
        ∑ i, ∑ j, ∫⁻ z in (Q.chart j).val '' (Q.piece j ∩ P.piece i),
          nativeCanonicalPhysicalCoordinateDensity L S w (Q.chart j) z ∂volume := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Set.inter_comm (Q.piece j)]
      exact actualPhysicalChart_overlap_integral L S w (P.chart i) (Q.chart j)
        (P.piece i ∩ Q.piece j) ((P.measurable_piece i).inter (Q.measurable_piece j))
        (fun _ hx => P.piece_subset i hx.1) (fun _ hx => Q.piece_subset j hx.2)
    _ = ∑ j, ∑ i, ∫⁻ z in (Q.chart j).val '' (Q.piece j ∩ P.piece i),
          nativeCanonicalPhysicalCoordinateDensity L S w (Q.chart j) z ∂volume := Finset.sum_comm

def nativePhysicalHodgeEnergy : ℝ≥0∞ :=
  nativeCanonicalPartitionEnergy L S w
    (Classical.choice (exists_nativeCanonicalChartPartition (n := n) (X := X)))

theorem nativePhysicalHodgeEnergy_eq_partition (P : NativeCanonicalChartPartition n X) :
    nativePhysicalHodgeEnergy L S w = nativeCanonicalPartitionEnergy L S w P :=
  nativeCanonicalPartitionEnergy_eq L S w _ P

end SGPT.Trace.Bertini
