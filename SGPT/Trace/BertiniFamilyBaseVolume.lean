import SGPT.Trace.BertiniFamilyBaseDensity
import SGPT.Trace.BertiniFamilyMatchedVolume

/-! The actual smaller matched volume pushes to the SAME larger matched
volume restricted to the literal open tube. No volume compatibility input. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

private theorem actualBaseVolume_chartImage_measurable {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : ComplexChart n Y) (B : Set Y) (hB : MeasurableSet B) (hsub : B ⊆ e.val.source) :
    MeasurableSet (e.val '' B) := by
  let g : e.val.target → Y := fun z => e.val.symm z.val
  have hg : Continuous g := e.val.continuousOn_symm.domRestrict
  have hm := e.val.open_target.measurableSet.subtype_image (hB.preimage hg.measurable)
  have hset : e.val '' B = (Subtype.val : e.val.target → ComplexModel n) '' (g ⁻¹' B) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨e.val x,e.val.map_source (hsub hx)⟩,?_,rfl⟩
      change e.val.symm (e.val x) ∈ B
      rw [e.val.left_inv (hsub hx)]
      exact hx
    · rintro ⟨z,hz,rfl⟩
      exact ⟨e.val.symm z.val,hz,e.val.right_inv z.property⟩
  rw [hset]
  exact hm

private theorem actualBaseVolume_eq_of_countable_cover {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) (W : ℕ → Set Y) (hW : ∀ j, MeasurableSet (W j))
    (hcover : ⋃ j, W j = univ) (heq : ∀ j, μ.restrict (W j) = ν.restrict (W j)) : μ = ν := by
  have hD (j : ℕ) : MeasurableSet (disjointed W j) :=
    disjointedRec (p := MeasurableSet) (fun {_t k} ht => ht.diff (hW k)) (hW j)
  have hcD : ⋃ j, disjointed W j = univ := by rw [iUnion_disjointed,hcover]
  have hlocal (j : ℕ) : μ.restrict (disjointed W j) = ν.restrict (disjointed W j) := by
    have h := congrArg (fun κ : Measure Y => κ.restrict (disjointed W j)) (heq j)
    simpa only [Measure.restrict_restrict_of_subset (disjointed_subset W j)] using h
  calc
    μ = Measure.sum (fun j => μ.restrict (disjointed W j)) := by
      rw [← Measure.restrict_iUnion (disjoint_disjointed W) hD,hcD,Measure.restrict_univ]
    _ = Measure.sum (fun j => ν.restrict (disjointed W j)) := congrArg Measure.sum (funext hlocal)
    _ = ν := by rw [← Measure.restrict_iUnion (disjoint_disjointed W) hD,hcD,Measure.restrict_univ]

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem familyMatchedVolume_chartSubset :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U))
      (B : Set (familyIncidence p i a v U)) (_hB : MeasurableSet B) (_hsub : B ⊆ e.val.source),
      familyMatchedVolume p i a v U hsm B =
        ∫⁻ z in e.val '' B, ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e B hB hsub
  have hi := actualBaseVolume_chartImage_measurable e B hB hsub
  have ht : e.val '' B ⊆ e.val.target := by
    rintro z ⟨x,hx,rfl⟩
    exact e.val.map_source (hsub hx)
  have hpre : e.val ⁻¹' (e.val '' B) ∩ e.val.source = B := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,hyx⟩,hxs⟩
      exact (e.val.injOn (hsub hy) hxs hyx) ▸ hy
    · intro hx
      exact ⟨⟨x,hx,rfl⟩,hsub hx⟩
  have he : AEMeasurable e.val ((familyMatchedVolume p i a v U hsm).restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have h := congrArg (fun κ : Measure (ComplexModel (d + 1)) => κ (e.val '' B))
    (familyMatchedVolume_chart p i a v U hsm e)
  rw [Measure.map_apply_of_aemeasurable he hi,Measure.restrict_apply' e.val.open_source.measurableSet,
    hpre,withDensity_apply _ hi,Measure.restrict_restrict hi,inter_eq_left.mpr ht] at h
  exact h

theorem familyBaseMatchedVolume_map :
    Measure.map (familyBaseInclusion p i a v U V hVU)
      (familyMatchedVolume p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm)) =
      (familyMatchedVolume p i a v U hsm).restrict (familyBaseTube p i a v U V) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let I := familyBaseInclusion p i a v U V hVU
  let μ := familyMatchedVolume p i a v V hsV
  let ν := Measure.comap I (familyMatchedVolume p i a v U hsm)
  have hIc : Continuous I := continuous_subtype_val.comp
    (familyBaseTubeHomeomorph p i a v U V hVU).continuous
  have hI : MeasurableEmbedding I :=
    (MeasurableEmbedding.subtype_coe (familyBaseTube p i a v U V).isOpen.measurableSet).comp
      (familyBaseTubeHomeomorph p i a v U V hVU).measurableEmbedding
  have hlocal (q : familyIncidence p i a v V) :
      let e := complexChartAt (n := d + 1) q
      let f := complexChartAt (n := d + 1) (I q)
      μ.restrict (e.val.source ∩ I ⁻¹' f.val.source) = ν.restrict (e.val.source ∩ I ⁻¹' f.val.source) := by
    let e := complexChartAt (n := d + 1) q
    let f := complexChartAt (n := d + 1) (I q)
    let W := e.val.source ∩ I ⁻¹' f.val.source
    have hW : IsOpen W := e.val.open_source.inter (f.val.open_source.preimage hIc)
    apply Measure.ext
    intro A hA
    rw [Measure.restrict_apply hA,Measure.restrict_apply hA]
    let B := A ∩ W
    have hB : MeasurableSet B := hA.inter hW.measurableSet
    have he : B ⊆ e.val.source := fun _ hx => hx.2.1
    have hf : ∀ x ∈ B, I x ∈ f.val.source := fun x hx => hx.2.2
    have hIB : MeasurableSet (I '' B) := hI.measurableSet_image.mpr hB
    have hIBsub : I '' B ⊆ f.val.source := by
      rintro _ ⟨x,hx,rfl⟩
      exact hf x hx
    change μ B = (Measure.comap I (familyMatchedVolume p i a v U hsm)) B
    rw [hI.comap_apply]
    rw [familyMatchedVolume_chartSubset p i a v V hsV e B hB he,
      familyMatchedVolume_chartSubset p i a v U hsm f (I '' B) hIB hIBsub]
    have hcoord := actualBaseVolume_chartImage_measurable e B hB he
    have hsub : e.val '' B ⊆ coordinateDomain (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f := by
      rintro z ⟨x,hx,rfl⟩
      exact mem_coordinateDomain (he hx) (hf x hx)
    have hset : (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) '' (e.val '' B) =
        f.val '' (I '' B) := by
      ext z
      constructor
      · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
        refine ⟨I x,⟨x,hx,rfl⟩,?_⟩
        change f.val (I x) = f.val (I (e.val.symm (e.val x)))
        rw [e.val.left_inv (he hx)]
      · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
        refine ⟨e.val x,⟨x,hx,rfl⟩,?_⟩
        change f.val (I (e.val.symm (e.val x))) = f.val (I x)
        rw [e.val.left_inv (he hx)]
    have h := familyBaseMatchedCoordinateIntegral_change p i a v U V hVU hsm e f (e.val '' B)
      hcoord hsub (fun _ => 1)
    rw [hset] at h
    simpa only [mul_one] using h.symm
  have heq : μ = ν := by
    by_cases hne : Nonempty (familyIncidence p i a v V)
    · let := hne
      let W (q : familyIncidence p i a v V) :=
        (complexChartAt (n := d + 1) q).val.source ∩
          I ⁻¹' (complexChartAt (n := d + 1) (I q)).val.source
      have hW (q : familyIncidence p i a v V) : IsOpen (W q) :=
        (complexChartAt (n := d + 1) q).val.open_source.inter
          ((complexChartAt (n := d + 1) (I q)).val.open_source.preimage hIc)
      have hc : (univ : Set (familyIncidence p i a v V)) ⊆ ⋃ q, W q := by
        intro q _
        refine mem_iUnion.mpr ⟨q,mem_complexChartAt_source q,?_⟩
        change I q ∈ (complexChartAt (n := d + 1) (I q)).val.source
        exact mem_complexChartAt_source (I q)
      obtain ⟨A,hAc,hA⟩ := isLindelof_univ.elim_countable_subcover W hW hc
      let c := enumerateCountable hAc (Classical.choice hne)
      have hcover : ⋃ j : ℕ, W (c j) = univ := by
        apply eq_univ_of_forall
        intro q
        obtain ⟨x,hxA,hqx⟩ := mem_iUnion₂.mp (hA (mem_univ q))
        obtain ⟨j,hj⟩ := subset_range_enumerate hAc (Classical.choice hne) hxA
        exact mem_iUnion.mpr ⟨j,by simpa only [c,hj] using hqx⟩
      exact actualBaseVolume_eq_of_countable_cover μ ν (fun j => W (c j))
        (fun j => (hW (c j)).measurableSet) hcover (fun j => hlocal (c j))
    · let : IsEmpty (familyIncidence p i a v V) := not_nonempty_iff.mp hne
      exact Subsingleton.elim _ _
  have hrange : range I = (familyBaseTube p i a v U V : Set (familyIncidence p i a v U)) := by
    ext q
    constructor
    · rintro ⟨x,rfl⟩
      exact x.val.1.property
    · intro hq
      refine ⟨(familyBaseTubeHomeomorph p i a v U V hVU).symm ⟨q,hq⟩,?_⟩
      exact congrArg Subtype.val ((familyBaseTubeHomeomorph p i a v U V hVU).apply_symm_apply ⟨q,hq⟩)
  change Measure.map I μ = _
  rw [heq,hI.map_comap,hrange]

theorem familyBaseMatchedVolume_measurePreserving :
    MeasurePreserving (familyBaseInclusion p i a v U V hVU)
      (familyMatchedVolume p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm))
      ((familyMatchedVolume p i a v U hsm).restrict (familyBaseTube p i a v U V)) := by
  refine ⟨?_,familyBaseMatchedVolume_map p i a v U V hVU hsm⟩
  exact ((MeasurableEmbedding.subtype_coe (familyBaseTube p i a v U V).isOpen.measurableSet).comp
    (familyBaseTubeHomeomorph p i a v U V hVU).measurableEmbedding).measurable

theorem familyBaseMatchedVolume_lintegral
    (g : familyIncidence p i a v U → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ q, g (familyBaseInclusion p i a v U V hVU q)
      ∂familyMatchedVolume p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm)) =
      ∫⁻ q in (familyBaseTube p i a v U V : Set (familyIncidence p i a v U)),
        g q ∂familyMatchedVolume p i a v U hsm := by
  rw [← familyBaseMatchedVolume_map p i a v U V hVU hsm]
  exact (lintegral_map hg (familyBaseMatchedVolume_measurePreserving p i a v U V hVU hsm).measurable).symm

end SGPT.Trace.BertiniFamilyCanonical
