import SGPT.Bergman.SourceActualDonaldsonNorms

/-!
# FiniteBMLComparison

The finite-degree estimate behind source `lma:BML`: `|L_k(N^k_{v,K}) - L_k(N^k_{v,μ})| ≤ 2 n!/k^{n+1} · h⁰ · (log C_ε + εk)`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.QuantizationFrontier
open Bundle Set MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ)

/-- ORIGINAL probability and real v imply the true restricted source norm order; no comparison input. -/
theorem sourceL2ComplexNorm_le_sup (k : ℕ) (hk : 0 < k) (φ : X → EReal)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    (sourceL2ComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s ≤
      (sourceSupComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s := by
  let : IsProbabilityMeasure μ := hBM.1
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
  rw [sourceL2ComplexNorm_ofReal, sourceSupComplexNorm_ofReal]
  exact SGPT.Bergman.BernsteinMarkov.weightedL2Norm_le_weightedSupNorm
    (twistedPower L T k).Fiber k W.erealWeight μ
    (by simp [SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight]) _

/-- The ORIGINAL BM constants selected before all degrees/sections give the true real norm comparison. -/
theorem sourceSupComplexNorm_le_of_BM_bound {C ε : ℝ} (hC : 0 < C)
    (hb : ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s)
    (k : ℕ) (hk : 0 < k) (φ : X → EReal) (s : SourceHilbertSections L T W μ hBM k hk φ) :
    (sourceSupComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s ≤
      (C * Real.exp (ε * k)) * (sourceL2ComplexNorm L T W μ hBM k hk φ).toAddGroupNorm s := by
  have ha : 0 ≤ C * Real.exp (ε * k) := (mul_pos hC (Real.exp_pos _)).le
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ha (apply_nonneg _ _))).mp
  rw [ENNReal.ofReal_mul ha, sourceSupComplexNorm_ofReal, sourceL2ComplexNorm_ofReal]
  exact hb k hk _

local instance sourceVolumeMeasurable (k : ℕ) (hk : 0 < k) (φ : X → EReal) :
    MeasurableSpace (SourceHilbertSections L T W μ hBM k hk φ) := borel _
local instance sourceVolumeBorel (k : ℕ) (hk : 0 < k) (φ : X → EReal) :
    BorelSpace (SourceHilbertSections L T W μ hBM k hk φ) := ⟨rfl⟩

/-- The exact finite-degree ORIGINAL BML estimate on ALL literal original sections and arbitrary genuine
Haar normalization. No O(k^n), trace asymptotic or desired limiting measure is an input or conclusion. -/
theorem exists_finite_source_BML_bound (φ : X → EReal) (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (hμ0 : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (hk : 0 < k),
      ∀ vol : Measure (SourceHilbertSections L T W μ hBM k hk φ), vol.IsAddHaarMeasure →
      |sourceDonaldsonFunctional vol n k
          (sourceSupComplexNorm L T W μ hBM k hk φ)
          (sourceZeroReferenceComplexNorm L T W μ hBM k hk φ μ0 hμ0) -
        sourceDonaldsonFunctional vol n k
          (sourceL2ComplexNorm L T W μ hBM k hk φ)
          (sourceZeroReferenceComplexNorm L T W μ hBM k hk φ μ0 hμ0)| ≤
        (2 * (n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
          (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ) *
            (Real.log C + ε * k) := by
  obtain ⟨C0, hC0, hb⟩ := hBM.2 ε hε
  let C := max C0 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hbound : ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s := by
    intro k hk s
    exact (hb k hk s).trans (by gcongr; exact le_max_left _ _)

  refine ⟨C, hC, fun k hk vol hvol => ?_⟩
  let := hvol
  have ha : 1 ≤ C * Real.exp (ε * k) :=
    one_le_mul_of_one_le_of_one_le hC ((Real.one_le_exp_iff).mpr (mul_nonneg hε.le (Nat.cast_nonneg _)))
  have h := sourceDonaldsonFunctional_abs_difference_le vol n k
    (sourceL2ComplexNorm L T W μ hBM k hk φ)
    (sourceSupComplexNorm L T W μ hBM k hk φ)
    (sourceZeroReferenceComplexNorm L T W μ hBM k hk φ μ0 hμ0) ha
    (sourceL2ComplexNorm_le_sup L T W μ hBM k hk φ)
    (sourceSupComplexNorm_le_of_BM_bound L T W μ hBM hCp hbound k hk φ)
  have hd := (literalSourceHilbertEquiv L T W μ hBM k hk φ).finrank_eq
  rw [← hd, Real.log_mul hCp.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  convert h using 1; unfold sourceDonaldsonNormalization; push_cast; ring

end SGPT.Bergman.QuantizationFrontier
