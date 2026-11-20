import SGPT.Trace.BertiniHodgeCoercivity

/-! True intrinsic extended-energy parallelogram; actual finite positive
real quadratic Hodge functional on the ENTIRE original multiplier H0. -/
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

omit [IsComplexManifold n X] [CompactSpace X] in
private theorem actualQuadraticChartImage_measurable (c : ComplexChart n X)
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

theorem nativePhysicalChartPartition_density_aemeasurable
    (Q : NativePhysicalChartPartition L)
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (hw : Measurable w) (j : Fin Q.partition.size) :
    AEMeasurable (nativeCanonicalPhysicalCoordinateDensity L S w (Q.partition.chart j))
      (volume.restrict ((Q.partition.chart j).val '' Q.partition.piece j)) := by
  let P := Q.partition
  let K := (P.chart j).val '' P.piece j
  have hK : MeasurableSet K := actualQuadraticChartImage_measurable (P.chart j) _
    (P.measurable_piece j) (P.piece_subset j)
  have hc := Q.preferred j
  change AEMeasurable (nativeCanonicalPhysicalCoordinateDensity L S w (P.chart j)) (volume.restrict K)
  rw [hc]
  apply nativePhysicalCoordinateDensity_aemeasurable_on_frame L S w hw (Q.anchor j) (Q.frame j) K hK
  · rintro z ⟨x,hx,rfl⟩
    rw [← hc]
    exact (P.chart j).val.map_source (P.piece_subset j hx)
  · rintro z ⟨x,hx,rfl⟩
    rw [← hc,(P.chart j).val.left_inv (P.piece_subset j hx)]
    exact Q.piece_frame j hx

omit [MeasurableSpace X] [BorelSpace X] in
private theorem actualPhysicalCoordinateDensity_parallelogram
    (S T : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (c : ComplexChart n X) (z : ComplexModel n) :
    nativeCanonicalPhysicalCoordinateDensity L (S + T) w c z +
      nativeCanonicalPhysicalCoordinateDensity L (S - T) w c z =
      2 * (nativeCanonicalPhysicalCoordinateDensity L S w c z +
        nativeCanonicalPhysicalCoordinateDensity L T w c z) := by
  classical
  unfold nativeCanonicalPhysicalCoordinateDensity
  by_cases hz : z ∈ c.val.target
  · simp only [dif_pos hz]
    unfold nativeCanonicalPhysicalChartDensity
    change ENNReal.ofReal (‖nativeCanonicalPhysicalChartValue L c _ _ (S _ + T _)‖ ^ 2) * _ +
      ENNReal.ofReal (‖nativeCanonicalPhysicalChartValue L c _ _ (S _ - T _)‖ ^ 2) * _ = _
    rw [map_add,map_sub,← add_mul,← add_mul,← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      parallelogram_law_with_norm ℂ,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · simp only [dif_neg hz,zero_add,mul_zero]

theorem nativePhysicalHodgeEnergy_parallelogram
    (S T : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (hw : Measurable w) :
    nativePhysicalHodgeEnergy L (S + T) w + nativePhysicalHodgeEnergy L (S - T) w =
      2 * (nativePhysicalHodgeEnergy L S w + nativePhysicalHodgeEnergy L T w) := by
  classical
  let Q := Classical.choice (exists_nativePhysicalChartPartition L)
  let P := Q.partition
  rw [nativePhysicalHodgeEnergy_eq_partition L (S + T) w P,
    nativePhysicalHodgeEnergy_eq_partition L (S - T) w P,
    nativePhysicalHodgeEnergy_eq_partition L S w P,nativePhysicalHodgeEnergy_eq_partition L T w P]
  unfold nativeCanonicalPartitionEnergy
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let D (R : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber) :=
    nativeCanonicalPhysicalCoordinateDensity L R w (P.chart j)
  change (∫⁻ z in (P.chart j).val '' P.piece j, D (S + T) z) +
    (∫⁻ z in (P.chart j).val '' P.piece j, D (S - T) z) =
    2 * ((∫⁻ z in (P.chart j).val '' P.piece j, D S z) +
      (∫⁻ z in (P.chart j).val '' P.piece j, D T z))
  have hm (R : HolomorphicSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber) :
      AEMeasurable (D R) (volume.restrict ((P.chart j).val '' P.piece j)) :=
    nativePhysicalChartPartition_density_aemeasurable L Q R w hw j
  rw [← lintegral_add_left' (hm (S + T)),← lintegral_add_left' (hm S),
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact lintegral_congr (actualPhysicalCoordinateDensity_parallelogram L S T w (P.chart j))

theorem nativePhysicalHodgeEnergy_add_le
    (S T : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (w : X → ℝ≥0∞) (hw : Measurable w) :
    nativePhysicalHodgeEnergy L (S + T) w ≤
      2 * (nativePhysicalHodgeEnergy L S w + nativePhysicalHodgeEnergy L T w) := by
  rw [← nativePhysicalHodgeEnergy_parallelogram L S T w hw]
  exact le_add_right le_rfl

abbrev NativePhysicalMultiplierH0 (φ : X → EReal) :=
  ↥(fullHolomorphicIdealSections (n := n)
    (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber
    (sourceDegreeMultiplierIdeal (n := n) 1 φ))

def nativePhysicalHodgeSquaredNorm (φ : X → EReal) (S : NativePhysicalMultiplierH0 L φ) : ℝ :=
  (nativePhysicalHodgeEnergy L S.val (fun x => multiplierWeight 1 (φ x))).toReal

theorem nativePhysicalHodgeSquaredNorm_exact {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (S : NativePhysicalMultiplierH0 L φ) :
    ENNReal.ofReal (nativePhysicalHodgeSquaredNorm L φ S) =
      nativePhysicalHodgeEnergy L S.val (fun x => multiplierWeight 1 (φ x)) := by
  exact ENNReal.ofReal_toReal
    ((nativePhysicalHodgeEnergy_finite_iff_full_originalIdeal_allDimensions L hφ S.val).mp S.property).ne

theorem nativePhysicalHodgeSquaredNorm_pos {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (S : NativePhysicalMultiplierH0 L φ) (hS : S ≠ 0) :
    0 < nativePhysicalHodgeSquaredNorm L φ S := by
  have hSval : S.val ≠ 0 := fun h => hS (Subtype.ext h)
  exact ENNReal.toReal_pos (nativePhysicalHodgeEnergy_pos L hφ S.val hSval).ne'
    ((nativePhysicalHodgeEnergy_finite_iff_full_originalIdeal_allDimensions L hφ S.val).mp S.property).ne

theorem nativePhysicalHodgeSquaredNorm_smul (φ : X → EReal)
    (S : NativePhysicalMultiplierH0 L φ) (a : ℂ) :
    nativePhysicalHodgeSquaredNorm L φ (a • S) = ‖a‖ ^ 2 * nativePhysicalHodgeSquaredNorm L φ S := by
  unfold nativePhysicalHodgeSquaredNorm
  change (nativePhysicalHodgeEnergy L (a • (S.val : ∀ x, _)) _).toReal = _
  rw [nativePhysicalHodgeEnergy_smul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)]

theorem nativePhysicalHodgeSquaredNorm_parallelogram {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (S T : NativePhysicalMultiplierH0 L φ) :
    nativePhysicalHodgeSquaredNorm L φ (S + T) + nativePhysicalHodgeSquaredNorm L φ (S - T) =
      2 * (nativePhysicalHodgeSquaredNorm L φ S + nativePhysicalHodgeSquaredNorm L φ T) := by
  let E (S : NativePhysicalMultiplierH0 L φ) :=
    nativePhysicalHodgeEnergy L S.val (fun x => multiplierWeight 1 (φ x))
  have hfin (S : NativePhysicalMultiplierH0 L φ) : E S ≠ ⊤ :=
    ((nativePhysicalHodgeEnergy_finite_iff_full_originalIdeal_allDimensions L hφ S.val).mp S.property).ne
  have h := congrArg ENNReal.toReal (nativePhysicalHodgeEnergy_parallelogram L S.val T.val
    (fun x => multiplierWeight 1 (φ x))
    ((measurable_originalMultiplierWeight measurable_id 1).comp hφ.upperSemicontinuous.measurable))
  change (E (S + T) + E (S - T)).toReal = ((2 : ℝ≥0∞) * (E S + E T)).toReal at h
  rw [ENNReal.toReal_add (hfin _) (hfin _),ENNReal.toReal_mul,
    ENNReal.toReal_add (hfin _) (hfin _)] at h
  norm_num at h
  exact h

end SGPT.Trace.Bertini
