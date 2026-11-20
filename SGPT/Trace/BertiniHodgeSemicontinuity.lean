import SGPT.Trace.BertiniHodgeRawZeroDimensional
import Mathlib.Topology.Semicontinuity.Basic

/-! Actual preferred physical chart partitions, genuine coordinate
measurability, quadratic homogeneity, and lower semicontinuity on the
ENTIRE original native H0 with its produced supremum norm. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)

structure NativePhysicalChartPartition where
  partition : NativeCanonicalChartPartition n X
  anchor : Fin partition.size → X
  preferred : ∀ j, partition.chart j = complexChartAt (n := n) (anchor j)
  frame : Fin partition.size → AtlasFrame L
  piece_frame : ∀ j, partition.piece j ⊆ (frame j).val.baseSet

theorem exists_nativePhysicalChartPartition : Nonempty (NativePhysicalChartPartition L) := by
  classical
  let e (x : X) : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x,inferInstance⟩
  let W (x : X) : Set X := (complexChartAt (n := n) x).val.source ∩ (e x).val.baseSet
  have hW (x : X) : IsOpen (W x) :=
    (complexChartAt (n := n) x).val.open_source.inter (e x).val.open_baseSet
  have hcover : (univ : Set X) ⊆ ⋃ x, W x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,mem_complexChartAt_source _,mem_baseSet_trivializationAt ℂ _ _⟩
  obtain ⟨A,hA⟩ := isCompact_univ.elim_finite_subcover W hW hcover
  let a : Fin A.card → X := fun j => (A.equivFin.symm j).val
  let V (j : Fin A.card) := W (a j)
  have hV (j : Fin A.card) : MeasurableSet (V j) := (hW (a j)).measurableSet
  have hVcover : ⋃ j, V j = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y,hyA,hxy⟩ := mem_iUnion₂.mp (hA (mem_univ x))
    refine mem_iUnion.mpr ⟨A.equivFin ⟨y,hyA⟩,?_⟩
    simpa only [V,a,Equiv.symm_apply_apply] using hxy
  let P : NativeCanonicalChartPartition n X := {
    size := A.card
    chart := fun j => complexChartAt (n := n) (a j)
    piece := disjointed V
    measurable_piece := fun j => disjointedRec (fun {t k} ht => ht.diff (hV k)) (hV j)
    piece_subset := fun j x hx => (disjointed_subset V j hx).1
    disjoint_piece := disjoint_disjointed V
    cover := by rw [iUnion_disjointed,hVcover] }
  exact ⟨⟨P,a,fun _ => rfl,fun j => e (a j),
    fun j x hx => (disjointed_subset V j hx).2⟩⟩

omit [IsComplexManifold n X] [CompactSpace X] in
private theorem actualPhysicalChartImage_measurable (c : ComplexChart n X)
    (W : Set X) (hW : MeasurableSet W) (hsub : W ⊆ c.val.source) :
    MeasurableSet (c.val '' W) := by
  let g : c.val.target → X := fun z => c.val.symm z.val
  have hg : Continuous g := c.val.continuousOn_symm.domRestrict
  have hm := c.val.open_target.measurableSet.subtype_image (hW.preimage hg.measurable)
  have hset : c.val '' W = (Subtype.val : c.val.target → ComplexModel n) '' (g ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨c.val x,c.val.map_source (hsub hx)⟩,?_,rfl⟩
      change c.val.symm (c.val x) ∈ W
      rw [c.val.left_inv (hsub hx)]
      exact hx
    · rintro ⟨z,hz,rfl⟩
      exact ⟨c.val.symm z.val,hz,c.val.right_inv z.property⟩
  rw [hset]
  exact hm

theorem nativePhysicalCoordinateDensity_aemeasurable_on_frame
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (hw : Measurable w) (a : X) (e : AtlasFrame L)
    (K : Set (ComplexModel n)) (hK : MeasurableSet K)
    (hKt : K ⊆ (complexChartAt (n := n) a).val.target)
    (hKe : ∀ z ∈ K, (complexChartAt (n := n) a).val.symm z ∈ e.val.baseSet) :
    AEMeasurable (nativeCanonicalPhysicalCoordinateDensity L S w (complexChartAt (n := n) a))
      (volume.restrict K) := by
  classical
  let c := complexChartAt (n := n) a
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  let q := tensorAtlasFrame (nativeCanonicalFrame (n := n) a) e
  let := e.property
  let := q.property
  let F := sectionCoefficient B.Fiber q.val S ∘ c.val.symm
  have hcoef : ContinuousOn F K :=
    ((sectionCoefficient_chart_differentiable B.Fiber q.val a S).mono
      (fun z hz => ⟨hKt hz,c.val.map_target (hKt hz),hKe z hz⟩)).continuousOn
  have hframe : ContinuousOn (fun z => ‖e.val.symm (c.val.symm z) 1‖ ^ 2) K :=
    ((frameNorm_continuousOn L.Fiber e.val).comp
      (c.val.continuousOn_symm.mono hKt) hKe).pow 2
  have hweight : AEMeasurable (fun z => w (c.val.symm z)) (volume.restrict K) :=
    hw.comp_aemeasurable ((c.val.continuousOn_symm.mono hKt).aemeasurable hK)
  have hm : AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2) *
      ENNReal.ofReal (‖e.val.symm (c.val.symm z) 1‖ ^ 2)) (volume.restrict K) :=
    ((hcoef.aemeasurable hK).norm.pow_const 2).ennreal_ofReal.mul
    ((hframe.aemeasurable hK).ennreal_ofReal)
  apply (hm.mul hweight).congr
  filter_upwards [ae_restrict_mem hK] with z hz
  unfold nativeCanonicalPhysicalCoordinateDensity
  rw [dif_pos (hKt hz)]
  unfold nativeCanonicalPhysicalChartDensity
  rw [nativePhysicalPreferredChartValue_eq_coefficient L a _ _ e (hKe z hz),
    norm_smul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]
  rfl

theorem nativePhysicalHodgeEnergy_smul
    (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x)
    (w : X → ℝ≥0∞) (a : ℂ) :
    nativePhysicalHodgeEnergy L (a • S) w =
      ENNReal.ofReal (‖a‖ ^ 2) * nativePhysicalHodgeEnergy L S w := by
  classical
  let P := Classical.choice (exists_nativeCanonicalChartPartition (n := n) (X := X))
  rw [nativePhysicalHodgeEnergy_eq_partition L (a • S) w P,
    nativePhysicalHodgeEnergy_eq_partition L S w P]
  unfold nativeCanonicalPartitionEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro z
  unfold nativeCanonicalPhysicalCoordinateDensity
  split_ifs with hz
  · unfold nativeCanonicalPhysicalChartDensity
    change ENNReal.ofReal (‖nativeCanonicalPhysicalChartValue L (P.chart j) _ _ (a • S _)‖ ^ 2) * _ = _
    rw [map_smul,norm_smul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),mul_assoc]
  · exact (mul_zero _).symm

omit [MeasurableSpace X] [BorelSpace X] in
private theorem actualPhysicalCoordinateDensity_le_liminf
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (c : ComplexChart n X) (z : ComplexModel n) :
    nativeCanonicalPhysicalCoordinateDensity L S w c z ≤
      liminf (fun T : HolomorphicSections (n := n)
        (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber =>
          nativeCanonicalPhysicalCoordinateDensity L T w c z) (𝓝 S) := by
  classical
  unfold nativeCanonicalPhysicalCoordinateDensity
  by_cases hz : z ∈ c.val.target
  · simp only [dif_pos hz]
    let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
    let x := c.val.symm z
    let ev : HolomorphicSections (n := n) B.Fiber →ₗ[ℂ] B.Fiber x := {
      toFun T := T x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    let F := (nativeCanonicalPhysicalChartValue L c x (c.val.map_target hz)).comp ev
    let := holomorphicSections_finiteDimensional (n := n) B.Fiber
    have hF : Continuous F := F.continuous_of_finiteDimensional
    have hlim : Tendsto (fun T => ENNReal.ofReal (‖F T‖ ^ 2)) (𝓝 S)
        (𝓝 (ENNReal.ofReal (‖F S‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.comp (hF.norm.pow 2)).tendsto S
    unfold nativeCanonicalPhysicalChartDensity
    change ENNReal.ofReal (‖F S‖ ^ 2) * w x ≤
      liminf (fun T => ENNReal.ofReal (‖F T‖ ^ 2) * w x) (𝓝 S)
    calc
      _ = liminf (fun T => ENNReal.ofReal (‖F T‖ ^ 2)) (𝓝 S) *
        liminf (fun _ : HolomorphicSections (n := n) B.Fiber => w x) (𝓝 S) := by
          rw [hlim.liminf_eq,liminf_const]
      _ ≤ _ := ENNReal.le_liminf_mul
  · simp only [dif_neg hz,liminf_const,le_refl]

theorem nativePhysicalHodgeEnergy_lowerSemicontinuous
    (w : X → ℝ≥0∞) (hw : Measurable w) :
    LowerSemicontinuous (fun S : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber =>
        nativePhysicalHodgeEnergy L S w) := by
  classical
  let Q := Classical.choice (exists_nativePhysicalChartPartition L)
  let P := Q.partition
  have heq : (fun S : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber => nativePhysicalHodgeEnergy L S w) =
      fun S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber =>
        ∑ j : Fin P.size, ∫⁻ z in (P.chart j).val '' P.piece j,
        nativeCanonicalPhysicalCoordinateDensity L S w (P.chart j) z := by
    funext S
    exact nativePhysicalHodgeEnergy_eq_partition L S w P
  rw [heq]
  apply lowerSemicontinuous_sum
  intro j _
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro S
  let K := (P.chart j).val '' P.piece j
  have hK : MeasurableSet K := actualPhysicalChartImage_measurable (P.chart j) _
    (P.measurable_piece j) (P.piece_subset j)
  have hm (T : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber) :
      AEMeasurable (nativeCanonicalPhysicalCoordinateDensity L T w (P.chart j)) (volume.restrict K) := by
    have hc := Q.preferred j
    rw [hc]
    apply nativePhysicalCoordinateDensity_aemeasurable_on_frame L T w hw (Q.anchor j) (Q.frame j) K hK
    · rintro z ⟨x,hx,rfl⟩
      rw [← hc]
      exact (P.chart j).val.map_source (P.piece_subset j hx)
    · rintro z ⟨x,hx,rfl⟩
      rw [← hc,(P.chart j).val.left_inv (P.piece_subset j hx)]
      exact Q.piece_frame j hx
  exact (lintegral_mono (fun z => actualPhysicalCoordinateDensity_le_liminf L S w (P.chart j) z)).trans
    (lintegral_liminf_le' hm)

end SGPT.Trace.Bertini
