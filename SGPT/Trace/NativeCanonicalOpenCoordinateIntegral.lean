import SGPT.Trace.NativeCanonicalOpenCoordinateDerivative

/-! Actual compatible-coordinate physical Hodge integrals via original native partition pieces. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (D : TopologicalSpace.Opens (ComplexModel n))
  (g : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) D X ∞)
  (L : HermitianHolomorphicLineBundle n X)
  (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)

theorem nativeCanonicalPhysicalOpenIntegral_chart (e : ComplexChart n X)
    (A : Set (ComplexModel n)) (hA : MeasurableSet A) (hD : A ⊆ D)
    (he : ∀ z, ∀ hz : z ∈ A, g ⟨z,hD hz⟩ ∈ e.val.source) (hg : Function.Injective g) :
    (∫⁻ z in nativeOpenCoordinateMap D g e '' A,
      nativeCanonicalPhysicalCoordinateDensity L S w e z ∂volume) =
      ∫⁻ z in A, nativeCanonicalPhysicalOpenDensity D g L S w z ∂volume := by
  let F := nativeOpenCoordinateMap D g e
  have hderiv : ∀ z ∈ A, HasFDerivWithinAt F (fderiv ℝ F z) A z := by
    intro z hz
    have hc := (nativeOpenCoordinateMap_contDiffAt D g e ⟨z,hD hz⟩ (he z hz)).differentiableAt (by simp)
    exact (hc.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn F A := by
    intro z hz t ht hzt
    have hzt' : e.val (g ⟨z,hD hz⟩) = e.val (g ⟨t,hD ht⟩) := by
      simpa only [F, nativeOpenCoordinateMap_apply D g e ⟨z,hD hz⟩,
        nativeOpenCoordinateMap_apply D g e ⟨t,hD ht⟩] using hzt
    have h := hg (e.val.injOn (he z hz) (he t ht) hzt')
    exact congrArg Subtype.val h
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv hinj
    (nativeCanonicalPhysicalCoordinateDensity L S w e)
  apply h.trans
  apply setLIntegral_congr_fun hA
  intro z hz
  exact (nativeCanonicalPhysicalOpenDensity_change D g L S w e ⟨z,hD hz⟩ (he z hz)).symm

variable [MeasurableSpace X] [BorelSpace X]

omit [IsComplexManifold n X] [CompactSpace X] in
private theorem actualOpenIntegral_chartImage_measurable (e : ComplexChart n X)
    (A : Set X) (hA : MeasurableSet A) (hs : A ⊆ e.val.source) :
    MeasurableSet (e.val '' A) := by
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

omit D g in
theorem nativeCanonicalPhysicalCoordinateIntegral_indicator
    (e : ComplexChart n X) (A : Set X) (hA : MeasurableSet A) (hs : A ⊆ e.val.source)
    (V : TopologicalSpace.Opens X) :
    (∫⁻ z in e.val '' A, nativeCanonicalPhysicalCoordinateDensity L S ((V : Set X).indicator w) e z ∂volume) =
      ∫⁻ z in e.val '' (A ∩ V), nativeCanonicalPhysicalCoordinateDensity L S w e z ∂volume := by
  classical
  let B := e.val '' (A ∩ V)
  have hmA := actualOpenIntegral_chartImage_measurable e A hA hs
  have hmB : MeasurableSet B := actualOpenIntegral_chartImage_measurable e (A ∩ V)
    (hA.inter V.isOpen.measurableSet) (fun _ hx => hs hx.1)
  have hBA : B ⊆ e.val '' A := Set.image_mono inter_subset_left
  have hpoint : ∀ z ∈ e.val '' A,
      nativeCanonicalPhysicalCoordinateDensity L S ((V : Set X).indicator w) e z =
        B.indicator (nativeCanonicalPhysicalCoordinateDensity L S w e) z := by
    rintro z ⟨x,hx,rfl⟩
    have ht := e.val.map_source (hs hx)
    have hiff : e.val x ∈ B ↔ e.val.symm (e.val x) ∈ V := by
      rw [e.val.left_inv (hs hx)]
      constructor
      · rintro ⟨y,hy,hEq⟩
        have hxy := e.val.injOn (hs hy.1) (hs hx) hEq
        exact hxy ▸ hy.2
      · intro hV
        exact ⟨x,⟨hx,hV⟩,rfl⟩
    by_cases hb : e.val x ∈ B
    · rw [Set.indicator_of_mem hb]
      unfold nativeCanonicalPhysicalCoordinateDensity
      rw [dif_pos ht, dif_pos ht]
      unfold nativeCanonicalPhysicalChartDensity
      rw [Set.indicator_of_mem (hiff.mp hb)]
    · rw [Set.indicator_of_notMem hb]
      unfold nativeCanonicalPhysicalCoordinateDensity
      rw [dif_pos ht]
      unfold nativeCanonicalPhysicalChartDensity
      rw [Set.indicator_of_notMem (fun h => hb (hiff.mpr h)), mul_zero]
  calc
    _ = ∫⁻ z in e.val '' A, B.indicator (nativeCanonicalPhysicalCoordinateDensity L S w e) z ∂volume :=
      setLIntegral_congr_fun hmA hpoint
    _ = ∫⁻ z in B ∩ (e.val '' A), nativeCanonicalPhysicalCoordinateDensity L S w e z ∂volume :=
      setLIntegral_indicator hmB _
    _ = _ := by rw [inter_eq_left.mpr hBA]

theorem nativePhysicalHodgeEnergy_openCoordinates
    (V : TopologicalSpace.Opens X) (hg : Function.Injective g) (hrange : Set.range g = V) :
    nativePhysicalHodgeEnergy L S ((V : Set X).indicator w) =
      ∫⁻ z in D, nativeCanonicalPhysicalOpenDensity D g L S w z ∂volume := by
  classical
  let P := Classical.choice (exists_nativeCanonicalChartPartition (n := n) (X := X))
  let B : Fin P.size → Set (ComplexModel n) := fun j =>
    (Subtype.val : D → ComplexModel n) '' (g ⁻¹' P.piece j)
  have hm (j : Fin P.size) : MeasurableSet (B j) :=
    D.isOpen.measurableSet.subtype_image ((P.measurable_piece j).preimage g.contMDiff.continuous.measurable)
  have hD (j : Fin P.size) : B j ⊆ D := by
    rintro _ ⟨u,_,rfl⟩
    exact u.property
  have he (j : Fin P.size) : ∀ z, ∀ hz : z ∈ B j, g ⟨z,hD j hz⟩ ∈ (P.chart j).val.source := by
    rintro _ ⟨u,hu,rfl⟩
    exact P.piece_subset j hu
  have hcover : ⋃ j, B j = D := by
    apply Set.Subset.antisymm
    · exact iUnion_subset hD
    · intro z hz
      have hc : g ⟨z,hz⟩ ∈ ⋃ j, P.piece j := by rw [P.cover]; trivial
      obtain ⟨j,hj⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨j,⟨⟨z,hz⟩,hj,rfl⟩⟩
  have hd : Pairwise (fun j k => Disjoint (B j) (B k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,huEq⟩ ⟨v,hv,hvEq⟩
    have huv : u = v := Subtype.ext (huEq.trans hvEq.symm)
    exact Set.disjoint_left.mp (P.disjoint_piece hjk) hu (huv.symm ▸ hv)
  have himage (j : Fin P.size) : nativeOpenCoordinateMap D g (P.chart j) '' B j =
      (P.chart j).val '' (P.piece j ∩ V) := by
    ext z
    constructor
    · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
      have hv : g u ∈ (V : Set X) := by rw [← hrange]; exact ⟨u,rfl⟩
      exact ⟨g u,⟨hu,hv⟩,(nativeOpenCoordinateMap_apply D g (P.chart j) u).symm⟩
    · rintro ⟨x,⟨hx,hv⟩,rfl⟩
      have hxR : x ∈ Set.range g := by rw [hrange]; exact hv
      obtain ⟨u,rfl⟩ := hxR
      exact ⟨u.val,⟨u,hx,rfl⟩,nativeOpenCoordinateMap_apply D g (P.chart j) u⟩
  rw [nativePhysicalHodgeEnergy_eq_partition L S ((V : Set X).indicator w) P]
  unfold nativeCanonicalPartitionEnergy
  calc
    _ = ∑ j, ∫⁻ z in B j, nativeCanonicalPhysicalOpenDensity D g L S w z ∂volume := by
      apply Finset.sum_congr rfl
      intro j _
      rw [nativeCanonicalPhysicalCoordinateIntegral_indicator L S w (P.chart j) (P.piece j)
        (P.measurable_piece j) (P.piece_subset j) V]
      have h := nativeCanonicalPhysicalOpenIntegral_chart D g L S w (P.chart j) (B j)
        (hm j) (hD j) (he j) hg
      rw [himage j] at h
      exact h
    _ = _ := by rw [← hcover, lintegral_iUnion hm hd, tsum_fintype]

end SGPT.Trace.Bertini
