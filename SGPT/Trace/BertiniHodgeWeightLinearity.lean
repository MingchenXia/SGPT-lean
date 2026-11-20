import SGPT.Trace.BertiniHodgeSemicontinuity

/-! Actual finite linearity in the ORIGINAL weight of intrinsic physical Hodge energy. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (L : HermitianHolomorphicLineBundle.{0,0} n X)

omit [MeasurableSpace X] [BorelSpace X] in
theorem nativeCanonicalPhysicalCoordinateDensity_weight_sum {ι : Type} [Fintype ι]
    (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x)
    (w : ι → X → ℝ≥0∞) (e : ComplexChart n X) (z : ComplexModel n) :
    nativeCanonicalPhysicalCoordinateDensity L S (fun x => ∑ j, w j x) e z =
      ∑ j, nativeCanonicalPhysicalCoordinateDensity L S (w j) e z := by
  classical
  by_cases hz : z ∈ e.val.target
  · simp only [nativeCanonicalPhysicalCoordinateDensity,dif_pos hz,
      nativeCanonicalPhysicalChartDensity,Finset.mul_sum]
  · simp only [nativeCanonicalPhysicalCoordinateDensity,dif_neg hz,Finset.sum_const_zero]

omit [IsComplexManifold n X] [CompactSpace X] in
private theorem actualWeightChartImage_measurable (e : ComplexChart n X)
    (A : Set X) (hA : MeasurableSet A) (hs : A ⊆ e.val.source) : MeasurableSet (e.val '' A) := by
  let f : e.val.target → X := fun z => e.val.symm z.val
  have hf : Continuous f := e.val.continuousOn_symm.domRestrict
  have hm := e.val.open_target.measurableSet.subtype_image (hA.preimage hf.measurable)
  have hset : e.val '' A = (Subtype.val : e.val.target → ComplexModel n) '' (f ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨e.val x,e.val.map_source (hs hx)⟩,?_,rfl⟩
      change e.val.symm (e.val x) ∈ A
      rwa [e.val.left_inv (hs hx)]
    · rintro ⟨z,hz,rfl⟩
      exact ⟨e.val.symm z.val,hz,e.val.right_inv z.property⟩
  rw [hset]
  exact hm

theorem nativePhysicalHodgeEnergy_weight_sum {ι : Type} [Fintype ι]
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : ι → X → ℝ≥0∞) (hw : ∀ j, Measurable (w j)) :
    nativePhysicalHodgeEnergy L S (fun x => ∑ j, w j x) =
      ∑ j, nativePhysicalHodgeEnergy L S (w j) := by
  classical
  let P := Classical.choice (exists_nativePhysicalChartPartition L)
  rw [nativePhysicalHodgeEnergy_eq_partition L S _ P.partition]
  have henergy (j : ι) := nativePhysicalHodgeEnergy_eq_partition L S (w j) P.partition
  simp_rw [henergy]
  unfold nativeCanonicalPartitionEnergy
  simp_rw [nativeCanonicalPhysicalCoordinateDensity_weight_sum]
  have hpieces (i : Fin P.partition.size) :
      (∫⁻ z in (P.partition.chart i).val '' P.partition.piece i,
        ∑ j, nativeCanonicalPhysicalCoordinateDensity L S (w j) (P.partition.chart i) z ∂volume) =
      ∑ j, ∫⁻ z in (P.partition.chart i).val '' P.partition.piece i,
        nativeCanonicalPhysicalCoordinateDensity L S (w j) (P.partition.chart i) z ∂volume := by
    apply lintegral_finsetSum'
    intro j _
    let A := (P.partition.chart i).val '' P.partition.piece i
    have hA : MeasurableSet A := actualWeightChartImage_measurable (P.partition.chart i) _
      (P.partition.measurable_piece i) (P.partition.piece_subset i)
    have hAt : A ⊆ (complexChartAt (n := n) (P.anchor i)).val.target := by
      rintro _ ⟨x,hx,rfl⟩
      rw [← P.preferred i]
      exact (P.partition.chart i).val.map_source (P.partition.piece_subset i hx)
    have hAe : ∀ z ∈ A, (complexChartAt (n := n) (P.anchor i)).val.symm z ∈ (P.frame i).val.baseSet := by
      rintro _ ⟨x,hx,rfl⟩
      rw [← P.preferred i,(P.partition.chart i).val.left_inv (P.partition.piece_subset i hx)]
      exact P.piece_frame i hx
    rw [P.preferred i]
    simpa only [A,P.preferred i] using
      nativePhysicalCoordinateDensity_aemeasurable_on_frame L S (w j) (hw j) (P.anchor i) (P.frame i) A hA hAt hAe
  simp_rw [hpieces]
  exact Finset.sum_comm

theorem nativePhysicalHodgeEnergy_weight_partition {ι : Type} [Fintype ι]
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (hw : Measurable w) (α : ι → X → ℝ≥0∞) (hα : ∀ j, Measurable (α j))
    (hsum : ∀ x, ∑ j, α j x = 1) :
    nativePhysicalHodgeEnergy L S w = ∑ j, nativePhysicalHodgeEnergy L S (fun x => α j x * w x) := by
  have hweight : (fun x => ∑ j, α j x * w x) = w := by
    funext x
    rw [← Finset.sum_mul,hsum x,one_mul]
  have h := nativePhysicalHodgeEnergy_weight_sum L S (fun j x => α j x * w x) (fun j => (hα j).mul hw)
  rw [hweight] at h
  exact h

end SGPT.Trace.Bertini
