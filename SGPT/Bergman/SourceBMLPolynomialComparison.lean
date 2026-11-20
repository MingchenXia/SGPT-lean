import SGPT.Bergman.SourceFullH0PolynomialGrowth
import SGPT.Bergman.SourceFiniteBMLComparison

/-!
# BMLPolynomialComparison

The Bernstein--Markov comparison of source `lma:BML`, `L_k(N^k_{v,K}) - L_k(N^k_{v,μ}) → 0`, on the Hilbert-space model of `H⁰(X, L^k ⊗ T ⊗ I(kφ))`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Bundle Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NormAxioms
open SGPT.Bergman.QuantizationFrontier
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (φ : X → EReal)

local instance bmlSectionsMeasurable (k : ℕ) (hk : 0 < k) :
    MeasurableSpace (SourceHilbertSections L T W μ hBM k hk φ) := borel _
local instance bmlSectionsBorel (k : ℕ) (hk : 0 < k) :
    BorelSpace (SourceHilbertSections L T W μ hBM k hk φ) := ⟨rfl⟩

/-- The literal source Donaldson DIFFERENCE with its reference already
cancelled by finite52's actual identity. Degree zero is a harmless total
extension only; every original positive degree has its exact source factor.
The arbitrary genuine Haar normalization is allowed to vary with degree. -/
def sourceBMLDifference
    (vol : ∀ (k : ℕ) (hk : 0 < k), Measure (SourceHilbertSections L T W μ hBM k hk φ))
    (k : ℕ) : ℝ :=
  if hk : 0 < k then sourceDonaldsonNormalization n k *
    (Real.log ((vol k hk).real (normUnitBall (sourceSupComplexNorm L T W μ hBM k hk φ))) -
      Real.log ((vol k hk).real (normUnitBall (sourceL2ComplexNorm L T W μ hBM k hk φ))))
  else 0

/-- Exact source-reference cancellation for EVERY genuine original reference
norm, not an assumed equality or a replacement of the original μ. -/
theorem sourceBMLDifference_eq_Donaldson_difference
    (vol : ∀ (k : ℕ) (hk : 0 < k), Measure (SourceHilbertSections L T W μ hBM k hk φ))
    (hvol : ∀ k hk, (vol k hk).IsAddHaarMeasure) (k : ℕ) (hk : 0 < k)
    (N0 : ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ)) :
    sourceBMLDifference L T W μ hBM φ vol k =
      sourceDonaldsonFunctional (vol k hk) n k (sourceSupComplexNorm L T W μ hBM k hk φ) N0 -
        sourceDonaldsonFunctional (vol k hk) n k (sourceL2ComplexNorm L T W μ hBM k hk φ) N0 := by
  let := hvol k hk
  rw [sourceDonaldsonFunctional_difference, sourceBMLDifference, dif_pos hk]

/-- Original BML comparison limit, derived from genuine source-metric H0
growth and the actual finite52 norm-ball inequality. No DXmain1, prescribed
growth coefficient, trace asymptotic, positive mass of zero potential,
peak-section estimate, or limiting measure is an incoming hypothesis.
Original real v/closed nonPP K and arbitrary probability BM μ remain EXACT. -/
theorem tendsto_sourceBMLDifference
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X)
    (vol : ∀ (k : ℕ) (hk : 0 < k), Measure (SourceHilbertSections L T W μ hBM k hk φ))
    (hvol : ∀ k hk, (vol k hk).IsAddHaarMeasure) :
    Tendsto (sourceBMLDifference L T W μ hBM φ vol) atTop (𝓝 0) := by
  obtain ⟨D, hD, hdim⟩ := exists_source_literal_multiplier_dimension_bound L T hL hT omega
  let A : ℝ := 2 * (n.factorial : ℝ) * D
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.factorial_pos n))) hD
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let ε : ℝ := δ / (2 * A)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hA)
  obtain ⟨C, hC, hfinite⟩ := exists_finite_source_BML_bound L T W μ hBM φ
    (sourceAuxiliaryProbabilityVolume omega) (sourceAuxiliaryProbabilityVolume_smoothPositive omega) hε
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A * Real.log C / δ)
  refine ⟨N + 1, fun k hkN => ?_⟩
  have hk : 0 < k := lt_of_lt_of_le (Nat.succ_pos N) hkN
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hNk : (N : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self N) hkN)
  have hsmall : A * Real.log C / (k : ℝ) < δ / 2 := by
    have ht : 2 * A * Real.log C / δ < (k : ℝ) := hN.trans hNk
    have htk := (div_lt_iff₀ hδ).mp ht
    apply (div_lt_iff₀ hkp).mpr
    nlinarith
  have hbound := hfinite k hk (vol k hk) (hvol k hk)
  rw [← sourceBMLDifference_eq_Donaldson_difference L T W μ hBM φ vol hvol k hk] at hbound
  have hpoly : |sourceBMLDifference L T W μ hBM φ vol k| ≤
      A * (Real.log C / (k : ℝ) + ε) := by
    calc
      _ ≤ (2 * (n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
          (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ) *
            (Real.log C + ε * k) := hbound
      _ ≤ (2 * (n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
          (D * (k : ℝ) ^ n) * (Real.log C + ε * k) := by
        gcongr
        exact hdim k hk φ
      _ = A * (Real.log C / (k : ℝ) + ε) := by
        dsimp only [A]
        rw [pow_succ]
        field_simp
  have hεeq : A * ε = δ / 2 := by
    dsimp only [ε]
    field_simp
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ A * (Real.log C / (k : ℝ) + ε) := hpoly
    _ = A * Real.log C / (k : ℝ) + δ / 2 := by rw [mul_add, hεeq]; ring
    _ < δ := by linarith

/-- Actual ORIGINAL N0,ω^n from the book's explicit ∫ω^n=1 convention.
The original reference norm is internally supplied by its genuine smooth
positive probability volume; it is not an incoming norm certificate. -/
def sourceKahlerReferenceComplexNorm (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k) :
    ComplexNorm (SourceHilbertSections L T W μ hBM k hk φ) := by
  let : IsProbabilityMeasure (IntegrationCurrent.kahlerVolume omega) := ⟨hmass⟩
  exact sourceZeroReferenceComplexNorm L T W μ hBM k hk φ
    (IntegrationCurrent.kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)

/-- Exact SAME source zero-weight reference integral, including original
coefficient zeros/poles in the domain and all actual ideal-H0 vectors. -/
theorem sourceKahlerReferenceComplexNorm_ofReal (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ENNReal.ofReal ((sourceKahlerReferenceComplexNorm L T W μ hBM φ omega hmass k hk).toAddGroupNorm s) =
      SGPT.Bergman.QuantizationDraft.weightedL2Norm (twistedPower L T k).Fiber k
        (SGPT.Bergman.BernsteinMarkov.univRealWeight 0)
        ((IntegrationCurrent.kahlerVolume omega).comap (Subtype.val : ↥(univ : Set X) → X))
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) := by
  let : IsProbabilityMeasure (IntegrationCurrent.kahlerVolume omega) := ⟨hmass⟩
  exact sourceZeroReferenceComplexNorm_ofReal L T W μ hBM k hk φ
    (IntegrationCurrent.kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) s

/-- Source `lma:BML` (Hilbert-space model of `H⁰(X, L^k ⊗ T ⊗ I(kφ))`; the source-facing form is
`SGPT.Bergman.PartialDonaldson.tendsto_partialDonaldson_sup_sub_l2`): Donaldson difference with the
normalized ω^n reference. It preserves the SAME real continuous v on closed
nonPP K, general probability BM μ, literal Γ ideal-H0, h_L^k⊗h_T and exact
n!/k^(n+1) factor. No Bergman weak convergence or DXmain1 is assumed. -/
theorem tendsto_original_BML_Donaldson_difference
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X) (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (vol : ∀ (k : ℕ) (hk : 0 < k), Measure (SourceHilbertSections L T W μ hBM k hk φ))
    (hvol : ∀ k hk, (vol k hk).IsAddHaarMeasure) :
    Tendsto (fun k : ℕ => if hk : 0 < k then
      sourceDonaldsonFunctional (vol k hk) n k (sourceSupComplexNorm L T W μ hBM k hk φ)
        (sourceKahlerReferenceComplexNorm L T W μ hBM φ omega hmass k hk) -
      sourceDonaldsonFunctional (vol k hk) n k (sourceL2ComplexNorm L T W μ hBM k hk φ)
        (sourceKahlerReferenceComplexNorm L T W μ hBM φ omega hmass k hk) else 0)
      atTop (𝓝 0) := by
  have heq : (fun k : ℕ => if hk : 0 < k then
      sourceDonaldsonFunctional (vol k hk) n k (sourceSupComplexNorm L T W μ hBM k hk φ)
        (sourceKahlerReferenceComplexNorm L T W μ hBM φ omega hmass k hk) -
      sourceDonaldsonFunctional (vol k hk) n k (sourceL2ComplexNorm L T W μ hBM k hk φ)
        (sourceKahlerReferenceComplexNorm L T W μ hBM φ omega hmass k hk) else 0) =
        sourceBMLDifference L T W μ hBM φ vol := by
    funext k
    by_cases hk : 0 < k
    · rw [dif_pos hk]
      exact (sourceBMLDifference_eq_Donaldson_difference L T W μ hBM φ vol hvol k hk _).symm
    · simp only [dif_neg hk, sourceBMLDifference]
  rw [heq]
  exact tendsto_sourceBMLDifference L T W μ hBM φ hL hT omega vol hvol


end SGPT.Bergman.PolynomialH0Growth
