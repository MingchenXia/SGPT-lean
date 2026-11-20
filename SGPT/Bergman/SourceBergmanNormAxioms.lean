import SGPT.Bergman.SourceTensorDictionary
import SGPT.Bergman.SourceVolumeBernsteinMarkov
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Normed.Group.Seminorm

-- PORT-SOURCE bergman-norm-axioms/WeightedSectionPointNorm.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NormAxioms
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (V : M → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (k : ℕ)

/-- The actual SAME-metric weighted point norm on the SAME original subtype. -/
def weightedPointNorm (s : HolomorphicSections (n := n) V) (x : W.carrier) : ℝ :=
  ‖s x.val‖ * Real.exp (-((k : ℝ) * W.weight x) / 2)

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedPointNorm_nonneg (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    0 ≤ weightedPointNorm V W k s x := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] in
theorem weightedPointNorm_continuous (s : HolomorphicSections (n := n) V) :
    Continuous (weightedPointNorm V W k s) :=
  ((sectionNormMap V s).continuous.comp continuous_subtype_val).mul
    (Real.continuous_exp.comp (((continuous_const.mul W.weight.continuous).neg).div_const 2))

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedPointNorm_zero (x : W.carrier) : weightedPointNorm V W k 0 x = 0 := by
  simp [weightedPointNorm]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedPointNorm_add_le (s t : HolomorphicSections (n := n) V) (x : W.carrier) :
    weightedPointNorm V W k (s + t) x ≤ weightedPointNorm V W k s x + weightedPointNorm V W k t x := by
  change ‖s x.val + t x.val‖ * _ ≤ ‖s x.val‖ * _ + ‖t x.val‖ * _
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedPointNorm_smul (c : ℂ) (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    weightedPointNorm V W k (c • s) x = ‖c‖ * weightedPointNorm V W k s x := by
  change ‖c • s x.val‖ * _ = _
  rw [norm_smul]
  exact mul_assoc _ _ _

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedPointNorm_neg (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    weightedPointNorm V W k (-s) x = weightedPointNorm V W k s x := by
  change ‖-s x.val‖ * _ = _
  rw [norm_neg]
  rfl

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
/-- Exact source density equals the square of the true continuous point norm. -/
theorem weightedSectionDensity_eq_pointNorm_sq (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    weightedSectionDensity V k W.erealWeight s x = ENNReal.ofReal (weightedPointNorm V W k s x ^ 2) := by
  have he : Real.exp (-((k : ℝ) * W.weight x) / 2) ^ 2 =
      Real.exp (-((k : ℝ) * W.weight x)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [weightedSectionDensity, SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight,
    multiplierWeight_coe, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  dsimp only [weightedPointNorm]
  rw [mul_pow, he]

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedSectionDensity_half_rpow (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    weightedSectionDensity V k W.erealWeight s x ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (weightedPointNorm V W k s x) := by
  rw [weightedSectionDensity_eq_pointNorm_sq,
    ENNReal.ofReal_pow (weightedPointNorm_nonneg V W k s x), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
/-- The original pole-deleted supremum is exactly the true point-norm supremum. -/
theorem weightedSupNorm_eq_iSup_pointNorm (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight s = ⨆ x : W.carrier, ENNReal.ofReal (weightedPointNorm V W k s x) := by
  unfold weightedSupNorm
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro _
    rw [weightedSectionDensity_half_rpow]
    exact le_iSup_of_le x le_rfl
  · apply iSup_le
    intro x
    rw [← weightedSectionDensity_half_rpow]
    exact le_iSup_of_le x (le_iSup_of_le (EReal.coe_ne_bot (W.weight x)) le_rfl)

variable [MeasurableSpace M] [BorelSpace M]

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] [BorelSpace M] in
/-- Exact actual L2 dictionary, with no integrability or finite-norm premise. -/
theorem weightedL2Norm_eq_eLpNorm (μ : Measure W.carrier) (s : HolomorphicSections (n := n) V) :
    weightedL2Norm V k W.erealWeight μ s = eLpNorm (weightedPointNorm V W k s) 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  unfold weightedL2Norm
  congr 1
  apply lintegral_congr
  intro x
  rw [weightedSectionDensity_eq_pointNorm_sq,
    Real.enorm_eq_ofReal (weightedPointNorm_nonneg V W k s x), ENNReal.rpow_two,
    ENNReal.ofReal_pow (weightedPointNorm_nonneg V W k s x)]

variable [CompactSpace M]

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [MeasurableSpace M] [BorelSpace M] in
/-- Finiteness is produced internally from genuine compactK and continuity. -/
theorem weightedSupNorm_ne_top (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight s ≠ ⊤ := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let a : C(W.carrier, ℝ) := ⟨weightedPointNorm V W k s, weightedPointNorm_continuous V W k s⟩
  rw [weightedSupNorm_eq_iSup_pointNorm]
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact (le_abs_self _).trans (by simpa only [a, ContinuousMap.coe_mk, Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm a x)

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [BorelSpace M] in
theorem weightedL2Norm_ne_top (μ : Measure W.carrier) [IsProbabilityMeasure μ]
    (s : HolomorphicSections (n := n) V) : weightedL2Norm V k W.erealWeight μ s ≠ ⊤ := by
  apply ne_top_of_le_ne_top (weightedSupNorm_ne_top V W k s)
  apply SGPT.Bergman.BernsteinMarkov.weightedL2Norm_le_weightedSupNorm
  simp only [SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight, EReal.coe_ne_bot,
    Set.ofPred_false, measure_empty]

#print axioms weightedPointNorm_continuous
#print axioms weightedSectionDensity_eq_pointNorm_sq
#print axioms weightedSectionDensity_half_rpow
#print axioms weightedSupNorm_eq_iSup_pointNorm
#print axioms weightedL2Norm_eq_eLpNorm
#print axioms weightedSupNorm_ne_top
#print axioms weightedL2Norm_ne_top
end SGPT.Bergman.NormAxioms

-- PORT-SOURCE bergman-norm-axioms/WeightedSectionNormAxioms.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NormAxioms
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (V : M → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (k : ℕ)

omit [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem ofReal_pointNorm_le_weightedSupNorm (s : HolomorphicSections (n := n) V) (x : W.carrier) :
    ENNReal.ofReal (weightedPointNorm V W k s x) ≤ weightedSupNorm V k W.erealWeight s := by
  rw [weightedSupNorm_eq_iSup_pointNorm]
  exact le_iSup (fun x => ENNReal.ofReal (weightedPointNorm V W k s x)) x

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedSupNorm_add_le (s t : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight (s + t) ≤
      weightedSupNorm V k W.erealWeight s + weightedSupNorm V k W.erealWeight t := by
  rw [weightedSupNorm_eq_iSup_pointNorm]
  apply iSup_le
  intro x
  calc
    _ ≤ ENNReal.ofReal (weightedPointNorm V W k s x + weightedPointNorm V W k t x) :=
      ENNReal.ofReal_le_ofReal (weightedPointNorm_add_le V W k s t x)
    _ = ENNReal.ofReal (weightedPointNorm V W k s x) + ENNReal.ofReal (weightedPointNorm V W k t x) :=
      ENNReal.ofReal_add (weightedPointNorm_nonneg V W k s x) (weightedPointNorm_nonneg V W k t x)
    _ ≤ _ := add_le_add (ofReal_pointNorm_le_weightedSupNorm V W k s x)
      (ofReal_pointNorm_le_weightedSupNorm V W k t x)

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedSupNorm_smul (c : ℂ) (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight (c • s) =
      ENNReal.ofReal ‖c‖ * weightedSupNorm V k W.erealWeight s := by
  rw [weightedSupNorm_eq_iSup_pointNorm, weightedSupNorm_eq_iSup_pointNorm, ENNReal.mul_iSup]
  apply iSup_congr
  intro x
  rw [weightedPointNorm_smul, ENNReal.ofReal_mul (norm_nonneg _)]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] in
theorem weightedSupNorm_neg (s : HolomorphicSections (n := n) V) :
    weightedSupNorm V k W.erealWeight (-s) = weightedSupNorm V k W.erealWeight s := by
  rw [weightedSupNorm_eq_iSup_pointNorm, weightedSupNorm_eq_iSup_pointNorm]
  apply iSup_congr
  intro x
  rw [weightedPointNorm_neg]

variable [MeasurableSpace M] [BorelSpace M]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] in
/-- Genuine scalar Minkowski at exponent two applied to the actual continuous
weighted fiber norms; no triangle or section-space norm is supplied. -/
theorem weightedL2Norm_add_le (μ : Measure W.carrier) (s t : HolomorphicSections (n := n) V) :
    weightedL2Norm V k W.erealWeight μ (s + t) ≤
      weightedL2Norm V k W.erealWeight μ s + weightedL2Norm V k W.erealWeight μ t := by
  rw [weightedL2Norm_eq_eLpNorm, weightedL2Norm_eq_eLpNorm, weightedL2Norm_eq_eLpNorm]
  calc
    _ ≤ eLpNorm (weightedPointNorm V W k s + weightedPointNorm V W k t) 2 μ := by
      apply eLpNorm_mono
      intro x
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (weightedPointNorm_nonneg V W k (s + t) x),
        Real.norm_of_nonneg (add_nonneg (weightedPointNorm_nonneg V W k s x)
          (weightedPointNorm_nonneg V W k t x))]
      exact weightedPointNorm_add_le V W k s t x
    _ ≤ _ := eLpNorm_add_le (weightedPointNorm_continuous V W k s).aestronglyMeasurable
      (weightedPointNorm_continuous V W k t).aestronglyMeasurable (by norm_num)

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] [BorelSpace M] in
theorem weightedL2Norm_smul (μ : Measure W.carrier) (c : ℂ) (s : HolomorphicSections (n := n) V) :
    weightedL2Norm V k W.erealWeight μ (c • s) =
      ENNReal.ofReal ‖c‖ * weightedL2Norm V k W.erealWeight μ s := by
  rw [weightedL2Norm_eq_eLpNorm, weightedL2Norm_eq_eLpNorm]
  have heq : weightedPointNorm V W k (c • s) = (‖c‖ : ℝ) • weightedPointNorm V W k s := by
    funext x
    exact weightedPointNorm_smul V W k c s x
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (norm_nonneg _)]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] [BorelSpace M] in
theorem weightedL2Norm_zero (μ : Measure W.carrier) : weightedL2Norm V (n := n) k W.erealWeight μ 0 = 0 := by
  rw [weightedL2Norm_eq_eLpNorm]
  have heq : weightedPointNorm V W k 0 = 0 := funext (weightedPointNorm_zero V W k)
  rw [heq, eLpNorm_zero]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V] [BorelSpace M] in
theorem weightedL2Norm_neg (μ : Measure W.carrier) (s : HolomorphicSections (n := n) V) :
    weightedL2Norm V k W.erealWeight μ (-s) = weightedL2Norm V k W.erealWeight μ s := by
  rw [weightedL2Norm_eq_eLpNorm, weightedL2Norm_eq_eLpNorm]
  congr 1
  funext x
  exact weightedPointNorm_neg V W k s x

variable [CompactSpace M]

/-- A genuine bundled seminorm whose values are EXACT actual original
weighted supremum values, read finitely; no global instance is altered. -/
def weightedSupSeminorm : AddGroupSeminorm (HolomorphicSections (n := n) V) where
  toFun := fun s => (weightedSupNorm V k W.erealWeight s).toReal
  map_zero' := by rw [weightedSupNorm_zero, ENNReal.toReal_zero]
  add_le' := fun s t => by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨weightedSupNorm_ne_top V W k s, weightedSupNorm_ne_top V W k t⟩)
      (weightedSupNorm_add_le V W k s t)
    rwa [ENNReal.toReal_add (weightedSupNorm_ne_top V W k s) (weightedSupNorm_ne_top V W k t)] at h
  neg' := fun s => by rw [weightedSupNorm_neg]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [MeasurableSpace M] [BorelSpace M] in
theorem weightedSupSeminorm_smul (c : ℂ) (s : HolomorphicSections (n := n) V) :
    weightedSupSeminorm V W k (c • s) = ‖c‖ * weightedSupSeminorm V W k s := by
  change (weightedSupNorm V k W.erealWeight (c • s)).toReal = _
  rw [weightedSupNorm_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  rfl

/-- Actual non-pluripolar faithfulness upgrades the actual supremum seminorm. -/
def weightedSupAddGroupNorm [ConnectedSpace M] : AddGroupNorm (HolomorphicSections (n := n) V) where
  toAddGroupSeminorm := weightedSupSeminorm V W k
  eq_zero_of_map_eq_zero' := fun s hs => by
    apply (weightedSupNorm_weightedSubset_eq_zero_iff V W k s).mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hs).resolve_right (weightedSupNorm_ne_top V W k s)

omit [MeasurableSpace M] [BorelSpace M] in
theorem weightedSupAddGroupNorm_ofReal [ConnectedSpace M] (s : HolomorphicSections (n := n) V) :
    ENNReal.ofReal (weightedSupAddGroupNorm V W k s) = weightedSupNorm V k W.erealWeight s :=
  ENNReal.ofReal_toReal (weightedSupNorm_ne_top V W k s)

omit [MeasurableSpace M] [BorelSpace M] in
theorem weightedSupAddGroupNorm_smul [ConnectedSpace M] (c : ℂ) (s : HolomorphicSections (n := n) V) :
    weightedSupAddGroupNorm V W k (c • s) = ‖c‖ * weightedSupAddGroupNorm V W k s :=
  weightedSupSeminorm_smul V W k c s

/-- The original probability measure and genuine Minkowski produce this
finite actual L2 seminorm, without a definiteness certificate or chosen basis. -/
def weightedL2Seminorm (μ : Measure W.carrier) [IsProbabilityMeasure μ] :
    AddGroupSeminorm (HolomorphicSections (n := n) V) where
  toFun := fun s => (weightedL2Norm V k W.erealWeight μ s).toReal
  map_zero' := by rw [weightedL2Norm_zero, ENNReal.toReal_zero]
  add_le' := fun s t => by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨weightedL2Norm_ne_top V W k μ s, weightedL2Norm_ne_top V W k μ t⟩)
      (weightedL2Norm_add_le V W k μ s t)
    rwa [ENNReal.toReal_add (weightedL2Norm_ne_top V W k μ s) (weightedL2Norm_ne_top V W k μ t)] at h
  neg' := fun s => by rw [weightedL2Norm_neg]

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] in
theorem weightedL2Seminorm_ofReal (μ : Measure W.carrier) [IsProbabilityMeasure μ]
    (s : HolomorphicSections (n := n) V) :
    ENNReal.ofReal (weightedL2Seminorm V W k μ s) = weightedL2Norm V k W.erealWeight μ s :=
  ENNReal.ofReal_toReal (weightedL2Norm_ne_top V W k μ s)

omit [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] in
theorem weightedL2Seminorm_smul (μ : Measure W.carrier) [IsProbabilityMeasure μ]
    (c : ℂ) (s : HolomorphicSections (n := n) V) :
    weightedL2Seminorm V W k μ (c • s) = ‖c‖ * weightedL2Seminorm V W k μ s := by
  change (weightedL2Norm V k W.erealWeight μ (c • s)).toReal = _
  rw [weightedL2Norm_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  rfl

#print axioms weightedSupNorm_add_le
#print axioms weightedSupNorm_smul
#print axioms weightedL2Norm_add_le
#print axioms weightedL2Norm_smul
#print axioms weightedSupAddGroupNorm
#print axioms weightedL2Seminorm
end SGPT.Bergman.NormAxioms

-- PORT-SOURCE bergman-norm-axioms/WholeBergmanNorms.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NormAxioms
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M]

/-- The EXACT original probability Bernstein--Markov property on the SAME
weighted subset and ALL genuine original tensor sections, uniformly in k. -/
def IsBernsteinMarkov (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (μ : Measure W.carrier) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s

variable [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [CompactSpace M] in
/-- Genuine definiteness follows from the ORIGINAL BM property and actual
non-pluripolar faithfulness, with no positive-definiteness/norm input. -/
theorem bernsteinMarkov_weightedL2Norm_eq_zero_iff (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s = 0 ↔ s = 0 := by
  constructor
  · intro hz
    obtain ⟨C, _hC, hb⟩ := hBM.2 1 (by norm_num)
    have h := hb k hk s
    rw [hz, mul_zero] at h
    exact (twistedSupNorm_weightedSubset_eq_zero_iff L T W k s).mp (le_antisymm h bot_le)
  · rintro rfl
    exact weightedL2Norm_zero (twistedPower L T k).Fiber W k μ

/-- An actual norm on the SAME full tensor H0 space. BM is the original
source assumption; no norm/basis/evaluation/definiteness certificate enters. -/
def bernsteinMarkovL2AddGroupNorm (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) :
    AddGroupNorm (twistedSections L T k) := by
  let : IsProbabilityMeasure μ := hBM.1
  refine {
    toAddGroupSeminorm := weightedL2Seminorm (twistedPower L T k).Fiber W k μ
    eq_zero_of_map_eq_zero' := fun s hs => ?_ }
  apply (bernsteinMarkov_weightedL2Norm_eq_zero_iff L T W μ hBM k hk s).mp
  exact ((ENNReal.toReal_eq_zero_iff _).mp hs).resolve_right
    (weightedL2Norm_ne_top (twistedPower L T k).Fiber W k μ s)

theorem bernsteinMarkovL2AddGroupNorm_ofReal (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (s : twistedSections L T k) :
    ENNReal.ofReal (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk s) =
      weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s := by
  let : IsProbabilityMeasure μ := hBM.1
  exact ENNReal.ofReal_toReal (weightedL2Norm_ne_top (twistedPower L T k).Fiber W k μ s)

theorem bernsteinMarkovL2AddGroupNorm_smul (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (c : ℂ) (s : twistedSections L T k) :
    bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk (c • s) =
      ‖c‖ * bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk s := by
  let : IsProbabilityMeasure μ := hBM.1
  exact weightedL2Seminorm_smul (twistedPower L T k).Fiber W k μ c s

/-- WHOLE original prop:BMNimplynorm, BOTH clauses, on the ENTIRE actual
degree-k section spaces with the SAME metric. Values are EXACT original N's.
AddGroupNorm plus complex homogeneity gives actual complex norms without
changing any global instance or introducing a different section-space alias. -/
theorem whole_BMNimplynorm (L T : HermitianHolomorphicLineBundle n M)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    (∀ k : ℕ, 0 < k → ∃ N : AddGroupNorm (twistedSections L T k),
      (∀ s : twistedSections L T k, ENNReal.ofReal (N s) =
        weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s) ∧
      ∀ c : ℂ, ∀ s : twistedSections L T k, N (c • s) = ‖c‖ * N s) ∧
    ∀ μ : Measure W.carrier, IsBernsteinMarkov L T W μ →
      ∀ k : ℕ, 0 < k → ∃ N : AddGroupNorm (twistedSections L T k),
        (∀ s : twistedSections L T k, ENNReal.ofReal (N s) =
          weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s) ∧
        ∀ c : ℂ, ∀ s : twistedSections L T k, N (c • s) = ‖c‖ * N s := by
  constructor
  · intro k _hk
    exact ⟨weightedSupAddGroupNorm (twistedPower L T k).Fiber W k,
      weightedSupAddGroupNorm_ofReal (twistedPower L T k).Fiber W k,
      weightedSupAddGroupNorm_smul (twistedPower L T k).Fiber W k⟩
  · intro μ hBM k hk
    exact ⟨bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk,
      bernsteinMarkovL2AddGroupNorm_ofReal L T W μ hBM k hk,
      bernsteinMarkovL2AddGroupNorm_smul L T W μ hBM k hk⟩

#print axioms bernsteinMarkov_weightedL2Norm_eq_zero_iff
#print axioms bernsteinMarkovL2AddGroupNorm
#print axioms bernsteinMarkovL2AddGroupNorm_ofReal
#print axioms bernsteinMarkovL2AddGroupNorm_smul
#print axioms whole_BMNimplynorm
end SGPT.Bergman.NormAxioms
