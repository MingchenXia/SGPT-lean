import SGPT.Bergman.SourceVolumeBernsteinMarkov
import SGPT.Bergman.SourceBergmanNormAxioms
import SGPT.Bergman.SourcePartialEnvelopeConcavity

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.GeneralBMTransport

open Bundle Set MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.BernsteinMarkov

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [Nonempty M]

/-- The actual original whole-space weighted subset, constructed internally. -/
def wholeWeightedSubset (v : C(M, ℝ)) : SGPT.Bergman.WeightedSubset.WeightedSubset n M where
  carrier := univ
  isClosed_carrier := isClosed_univ
  nonPluripolar_carrier := SGPT.Bergman.PartialEnvelopeConcavity.nonPluripolar_open
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M) isOpen_univ univ_nonempty
  weight := ⟨fun x => v x.val, v.continuous.comp continuous_subtype_val⟩

theorem wholeWeightedSubset_erealWeight (v : C(M, ℝ)) :
    (wholeWeightedSubset (n := n) v).erealWeight = univRealWeight v := rfl

theorem whole_weightedSupNorm (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (s : twistedSections L T k) :
    weightedSupNorm (twistedPower L T k).Fiber k
      (wholeWeightedSubset (n := n) v).erealWeight s =
    weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s := rfl

section MeasureReadback
variable {A : Type*} [MeasurableSpace A]

/-- The literal whole-subtype comap has exactly the same actual total mass. -/
theorem comap_univ_mass (μ : Measure A) :
    (μ.comap (Subtype.val : ↥(univ : Set A) → A)) univ = μ univ := by
  rw [(MeasurableEmbedding.subtype_coe MeasurableSet.univ).comap_apply]
  congr 1
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    exact ⟨⟨x, mem_univ x⟩, mem_univ _, rfl⟩

/-- Probability is transported by the actual whole-subtype comap, not normalization. -/
theorem isProbabilityMeasure_comap_univ_iff (μ : Measure A) :
    IsProbabilityMeasure (μ.comap (Subtype.val : ↥(univ : Set A) → A)) ↔
      IsProbabilityMeasure μ := by
  constructor
  · intro h
    refine ⟨?_⟩
    rw [← comap_univ_mass μ]
    exact h.measure_univ
  · intro h
    refine ⟨?_⟩
    rw [comap_univ_mass]
    exact h.measure_univ
end MeasureReadback

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
theorem whole_weightedL2Norm (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) (k : ℕ) (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k
      (wholeWeightedSubset (n := n) v).erealWeight
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M)) s =
    weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
      (μ.comap (Subtype.val : ↥(univ : Set M) → M)) s := rfl

variable [CompactSpace M]

omit [BorelSpace M] [CompactSpace M] in
/-- Exact source BM predicate transport, preserving the same constants and quantifiers. -/
theorem general_BM_iff_volume_BM (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) :
    SGPT.Bergman.NormAxioms.IsBernsteinMarkov L T (wholeWeightedSubset v)
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M)) ↔
    IsVolumeBernsteinMarkov L T v μ := by
  constructor
  · rintro ⟨hp, hb⟩
    exact ⟨(isProbabilityMeasure_comap_univ_iff μ).mp hp, hb⟩
  · rintro ⟨hp, hb⟩
    exact ⟨(isProbabilityMeasure_comap_univ_iff μ).mpr hp, hb⟩

/-- Every actual raw smooth positive volume has the all-degree comparison on
the SAME general weighted subset and unscaled measure; no probability input. -/
theorem smoothPositiveVolume_general_comparison (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M)
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k (wholeWeightedSubset (n := n) v).erealWeight s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k (wholeWeightedSubset (n := n) v).erealWeight
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M)) s := by
  exact smoothPositiveVolume_bernsteinMarkov L T v μ hμ hε

/-- The original probability convention is explicit: for a raw smooth volume,
general BM membership is equivalent to probability, without rescaling μ. -/
theorem smoothPositiveVolume_general_BM_iff_probability (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M)
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ) :
    SGPT.Bergman.NormAxioms.IsBernsteinMarkov L T (wholeWeightedSubset v)
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M)) ↔
    IsProbabilityMeasure μ := by
  constructor
  · intro h
    exact (isProbabilityMeasure_comap_univ_iff μ).mp h.1
  · intro hp
    refine ⟨(isProbabilityMeasure_comap_univ_iff μ).mpr hp, fun ε hε => ?_⟩
    obtain ⟨C, hC, hb⟩ := smoothPositiveVolume_general_comparison L T v μ hμ hε
    exact ⟨C, hC, fun k _ s => hb k s⟩

/-- Natural actual smooth positivity and source probability produce the GENERAL BM property. -/
theorem smoothPositiveProbabilityVolume_general_BM (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ) :
    SGPT.Bergman.NormAxioms.IsBernsteinMarkov L T (wholeWeightedSubset v)
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M)) :=
  (smoothPositiveVolume_general_BM_iff_probability L T v μ hμ).mpr inferInstance

variable [ConnectedSpace M]

/-- An actual SAME full-H0 complex norm produced from the geometric volume,
not supplied as a norm or positive-definiteness certificate. -/
def smoothPositiveProbabilityVolume_L2Norm (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ)
    (k : ℕ) (hk : 0 < k) : AddGroupNorm (twistedSections L T k) :=
  SGPT.Bergman.NormAxioms.bernsteinMarkovL2AddGroupNorm L T (wholeWeightedSubset v)
    (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M))
    (smoothPositiveProbabilityVolume_general_BM L T v μ hμ) k hk

theorem smoothPositiveProbabilityVolume_L2Norm_ofReal (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ)
    (k : ℕ) (hk : 0 < k) (s : twistedSections L T k) :
    ENNReal.ofReal (smoothPositiveProbabilityVolume_L2Norm L T v μ hμ k hk s) =
      weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
        (μ.comap (Subtype.val : ↥(univ : Set M) → M)) s := by
  exact SGPT.Bergman.NormAxioms.bernsteinMarkovL2AddGroupNorm_ofReal L T
    (wholeWeightedSubset v) (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M))
    (smoothPositiveProbabilityVolume_general_BM L T v μ hμ) k hk s

theorem smoothPositiveProbabilityVolume_L2Norm_smul (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ)
    (k : ℕ) (hk : 0 < k) (c : ℂ) (s : twistedSections L T k) :
    smoothPositiveProbabilityVolume_L2Norm L T v μ hμ k hk (c • s) =
      ‖c‖ * smoothPositiveProbabilityVolume_L2Norm L T v μ hμ k hk s := by
  exact SGPT.Bergman.NormAxioms.bernsteinMarkovL2AddGroupNorm_smul L T
    (wholeWeightedSubset v) (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → M))
    (smoothPositiveProbabilityVolume_general_BM L T v μ hμ) k hk c s

#print axioms wholeWeightedSubset
#print axioms wholeWeightedSubset_erealWeight
#print axioms whole_weightedSupNorm
#print axioms comap_univ_mass
#print axioms isProbabilityMeasure_comap_univ_iff
#print axioms whole_weightedL2Norm
#print axioms general_BM_iff_volume_BM
#print axioms smoothPositiveVolume_general_comparison
#print axioms smoothPositiveVolume_general_BM_iff_probability
#print axioms smoothPositiveProbabilityVolume_general_BM
#print axioms smoothPositiveProbabilityVolume_L2Norm
#print axioms smoothPositiveProbabilityVolume_L2Norm_ofReal
#print axioms smoothPositiveProbabilityVolume_L2Norm_smul
end SGPT.Bergman.GeneralBMTransport
