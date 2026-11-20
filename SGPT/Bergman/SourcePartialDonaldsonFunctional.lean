import SGPT.Bergman.SourceBMLPolynomialComparison

/-!
# The partial Donaldson functional and the Bernstein--Markov comparison

Source: `author/chapter_Bergman.tex`, `def:Bergman:L942` and `lma:BML`.

Throughout, `X` is a connected compact complex manifold carrying a Kähler background `ω` with
`∫_X ωⁿ = 1`, `(L,h)` and `(T,h_T)` are Hermitian holomorphic line bundles, and
`H⁰(X, L^k ⊗ T ⊗ I(kφ))` is the space of holomorphic sections of `L^k ⊗ T` whose local
coefficient lies in the multiplier ideal `I(kφ)` at every point
(`fullHolomorphicIdealSections` of `sourceDegreeMultiplierIdeal k φ`; it is identified with the
global sections of the sheaf tensor product `O(L^k ⊗ T) ⊗ I(kφ)` by
`literalTwistedMultiplierSectionEquiv`).

* `partialDonaldsonFunctional` is the book's partial Donaldson functional
  `L_{k,φ}(H) = n!/k^{n+1} · log (vol{H ≤ 1} / vol{N^k_{0,ωⁿ} ≤ 1})` on the space of complex
  norms `H` of `H⁰(X, L^k ⊗ T ⊗ I(kφ))`, computed with an (arbitrary) additive Haar measure;
  `partialDonaldsonFunctional_eq_haar` proves that every Haar measure gives the same value
  ("the normalization does not matter").
* `tendsto_partialDonaldson_sup_sub_l2` is `lma:BML`: for a Bernstein--Markov measure `μ` of a
  weighted subset `(K,v)`, `L_{k,φ}(N^k_{v,K}) - L_{k,φ}(N^k_{v,μ}) → 0`. Its proof uses the
  polynomial bound `dim H⁰(X, L^k ⊗ T ⊗ I(kφ)) ≤ C kⁿ`, proved from the smoothness of the
  Hermitian metrics (`exists_source_literal_multiplier_dimension_bound`), in place of the
  book's appeal to `thm:DXmain1`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.PartialDonaldson

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationFrontier SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L T : HermitianHolomorphicLineBundle n X)

/-- `H⁰(X, L^k ⊗ T ⊗ I(kφ))`: the holomorphic sections of `L^k ⊗ T` whose coefficient lies in
the multiplier ideal `I(kφ)` at every point. -/
abbrev idealSections (k : ℕ) (φ : X → EReal) : Submodule ℂ (twistedSections L T k) :=
  fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)

/-- `H⁰(X, L^k ⊗ T ⊗ I(kφ))` has the same dimension as the global sections of the sheaf
tensor product `O(L^k ⊗ T) ⊗ I(kφ)`. -/
theorem finrank_idealSections (k : ℕ) (φ : X → EReal) :
    Module.finrank ℂ (idealSections L T k φ) =
      Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) :=
  (literalTwistedMultiplierSectionEquiv L T k φ).finrank_eq.symm

variable {L T}

/-- Restriction of a complex norm on `H⁰(X, L^k ⊗ T)` to `H⁰(X, L^k ⊗ T ⊗ I(kφ))`. -/
def restrictNorm {k : ℕ} (φ : X → EReal) (Q : AddGroupNorm (twistedSections L T k))
    (hQ : ∀ (c : ℂ) (s : twistedSections L T k), Q (c • s) = ‖c‖ * Q s) :
    ComplexNorm (idealSections L T k φ) where
  toAddGroupNorm :=
    { toAddGroupSeminorm :=
        Q.toAddGroupSeminorm.comp (idealSections L T k φ).subtype.toAddMonoidHom
      eq_zero_of_map_eq_zero' := fun s hs => Subtype.ext (Q.eq_zero_of_map_eq_zero' s.val hs) }
  norm_smul c s := hQ c s.val

theorem restrictNorm_apply {k : ℕ} (φ : X → EReal) (Q : AddGroupNorm (twistedSections L T k))
    (hQ : ∀ (c : ℂ) (s : twistedSections L T k), Q (c • s) = ‖c‖ * Q s)
    (s : idealSections L T k φ) : (restrictNorm φ Q hQ).toAddGroupNorm s = Q s.val := rfl

variable (L T) [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

instance idealSections_finiteDimensional (k : ℕ) (φ : X → EReal) :
    FiniteDimensional ℂ (idealSections L T k φ) :=
  fullTwistedMultiplierSections_finiteDimensional L T k φ

/-- The Borel structure of the (unique) vector-space topology of `H⁰(X, L^k ⊗ T ⊗ I(kφ))`. -/
instance idealSections_measurableSpace (k : ℕ) (φ : X → EReal) :
    MeasurableSpace (idealSections L T k φ) := borel _

instance idealSections_borelSpace (k : ℕ) (φ : X → EReal) :
    BorelSpace (idealSections L T k φ) := ⟨rfl⟩

/-- `N^k_{v,K}` (`def:Bergman:L706`) restricted to `H⁰(X, L^k ⊗ T ⊗ I(kφ))`; it is a norm by
`prop:BMNimplynorm`. -/
def supNorm (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ) (φ : X → EReal) :
    ComplexNorm (idealSections L T k φ) :=
  restrictNorm φ (weightedSupAddGroupNorm (twistedPower L T k).Fiber W k)
    (weightedSupAddGroupNorm_smul (twistedPower L T k).Fiber W k)

/-- `N^k_{v,μ}` (`def:Bergman:L706`) restricted to `H⁰(X, L^k ⊗ T ⊗ I(kφ))`, for a
Bernstein--Markov measure `μ`; it is a norm by `prop:BMNimplynorm`. -/
def l2Norm (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal) :
    ComplexNorm (idealSections L T k φ) :=
  restrictNorm φ (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk)
    (bernsteinMarkovL2AddGroupNorm_smul L T W μ hBM k hk)

/-- The reference norm `N^k_{0,ωⁿ}`: the `L²` norm on `K = X` with weight `0` and the
probability measure `ωⁿ`. -/
def referenceNorm (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) : ComplexNorm (idealSections L T k φ) := by
  let : IsProbabilityMeasure (IntegrationCurrent.kahlerVolume omega) := ⟨hmass⟩
  exact restrictNorm φ
    (SGPT.Bergman.GeneralBMTransport.smoothPositiveProbabilityVolume_L2Norm L T 0
      (IntegrationCurrent.kahlerVolume omega)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) k hk)
    (SGPT.Bergman.GeneralBMTransport.smoothPositiveProbabilityVolume_L2Norm_smul L T 0
      (IntegrationCurrent.kahlerVolume omega)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) k hk)

omit [MeasurableSpace X] [BorelSpace X] in
theorem supNorm_ofReal (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (φ : X → EReal) (s : idealSections L T k φ) :
    ENNReal.ofReal ((supNorm L T W k φ).toAddGroupNorm s) =
      weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s.val :=
  weightedSupAddGroupNorm_ofReal (twistedPower L T k).Fiber W k s.val

theorem l2Norm_ofReal (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (μ : Measure W.carrier) (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) (s : idealSections L T k φ) :
    ENNReal.ofReal ((l2Norm L T W μ hBM k hk φ).toAddGroupNorm s) =
      weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ s.val :=
  bernsteinMarkovL2AddGroupNorm_ofReal L T W μ hBM k hk s.val

theorem referenceNorm_ofReal (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) (s : idealSections L T k φ) :
    ENNReal.ofReal ((referenceNorm L T omega hmass k hk φ).toAddGroupNorm s) =
      weightedL2Norm (twistedPower L T k).Fiber k (SGPT.Bergman.BernsteinMarkov.univRealWeight 0)
        ((IntegrationCurrent.kahlerVolume omega).comap (Subtype.val : ↥(univ : Set X) → X))
        s.val := by
  let : IsProbabilityMeasure (IntegrationCurrent.kahlerVolume omega) := ⟨hmass⟩
  exact SGPT.Bergman.GeneralBMTransport.smoothPositiveProbabilityVolume_L2Norm_ofReal L T 0
    (IntegrationCurrent.kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) k hk s.val

/-- Source `def:Bergman:L942`: the partial Donaldson functional
`L_{k,φ}(H) = n!/k^{n+1} · log (vol{H ≤ 1} / vol{N^k_{0,ωⁿ} ≤ 1})` on complex norms `H` of
`H⁰(X, L^k ⊗ T ⊗ I(kφ))`, `k ≥ 1`, where `vol` is a Haar (Lebesgue) measure; the choice of
Haar measure is irrelevant by `partialDonaldsonFunctional_eq_haar`. -/
def partialDonaldsonFunctional (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) (H : ComplexNorm (idealSections L T k φ)) : ℝ :=
  sourceDonaldsonFunctional (Measure.addHaar : Measure (idealSections L T k φ)) n k H
    (referenceNorm L T omega hmass k hk φ)

/-- The partial Donaldson functional does not depend on the normalization of the Lebesgue
measure: any Haar measure `vol` gives the same value. -/
theorem partialDonaldsonFunctional_eq_haar (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) (H : ComplexNorm (idealSections L T k φ))
    (vol : Measure (idealSections L T k φ)) [vol.IsAddHaarMeasure] :
    partialDonaldsonFunctional L T omega hmass k hk φ H =
      ((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (vol.real (normUnitBall H) /
          vol.real (normUnitBall (referenceNorm L T omega hmass k hk φ))) := by
  rw [partialDonaldsonFunctional,
    ← sourceDonaldsonFunctional_haarIndependent Measure.addHaar vol]
  rfl

/-- `N^k_{v,μ} ≤ N^k_{v,K}` on `H⁰(X, L^k ⊗ T ⊗ I(kφ))` (equation `eq:Nkinfcomp`). -/
theorem l2Norm_le_supNorm (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (μ : Measure W.carrier) (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k)
    (φ : X → EReal) (s : idealSections L T k φ) :
    (l2Norm L T W μ hBM k hk φ).toAddGroupNorm s ≤ (supNorm L T W k φ).toAddGroupNorm s := by
  let : IsProbabilityMeasure μ := hBM.1
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
  rw [l2Norm_ofReal, supNorm_ofReal]
  exact SGPT.Bergman.BernsteinMarkov.weightedL2Norm_le_weightedSupNorm
    (twistedPower L T k).Fiber k W.erealWeight μ
    (by simp [SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight]) _

/-- Source `lma:BML`: for a Bernstein--Markov measure `μ ∈ BM(K,v)`,
`L_{k,φ}(N^k_{v,K}) - L_{k,φ}(N^k_{v,μ}) → 0` as `k → ∞` (the value at `k = 0`, where the
functional is not defined, is set to `0`). The metrics `h`, `h_T` are smooth, as in the book. -/
theorem tendsto_partialDonaldson_sup_sub_l2
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X) (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (φ : X → EReal) :
    Tendsto (fun k : ℕ => if hk : 0 < k then
        partialDonaldsonFunctional L T omega hmass k hk φ (supNorm L T W k φ) -
          partialDonaldsonFunctional L T omega hmass k hk φ (l2Norm L T W μ hBM k hk φ)
        else 0) atTop (𝓝 0) := by
  obtain ⟨D, hD, hdim⟩ := exists_source_literal_multiplier_dimension_bound L T hL hT omega
  let A : ℝ := 2 * (n.factorial : ℝ) * D
  have hA : 0 < A := mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.factorial_pos n))) hD
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let ε : ℝ := δ / (2 * A)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hA)
  obtain ⟨C0, _hC0, hb⟩ := hBM.2 ε hε
  let C := max C0 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
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
  rw [dif_pos hk, Real.dist_eq, sub_zero]
  -- the Bernstein--Markov comparison of the two norms, with constant `C e^{εk}`
  have ha0 : 0 ≤ C * Real.exp (ε * k) := (mul_pos hCp (Real.exp_pos _)).le
  have ha : 1 ≤ C * Real.exp (ε * k) :=
    one_le_mul_of_one_le_of_one_le hC
      ((Real.one_le_exp_iff).mpr (mul_nonneg hε.le (Nat.cast_nonneg _)))
  have hMN : ∀ s : idealSections L T k φ, (supNorm L T W k φ).toAddGroupNorm s ≤
      (C * Real.exp (ε * k)) * (l2Norm L T W μ hBM k hk φ).toAddGroupNorm s := by
    intro s
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ha0 (apply_nonneg _ _))).mp
    rw [ENNReal.ofReal_mul ha0, supNorm_ofReal, l2Norm_ofReal]
    exact (hb k hk s.val).trans (by gcongr; exact le_max_left _ _)
  have h := sourceDonaldsonFunctional_abs_difference_le
    (Measure.addHaar : Measure (idealSections L T k φ)) n k
    (l2Norm L T W μ hBM k hk φ) (supNorm L T W k φ) (referenceNorm L T omega hmass k hk φ) ha
    (l2Norm_le_supNorm L T W μ hBM k hk φ) hMN
  rw [Real.log_mul hCp.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have hd : (Module.finrank ℂ (idealSections L T k φ) : ℝ) ≤ D * (k : ℝ) ^ n := by
    rw [finrank_idealSections]
    exact hdim k hk φ
  have hεeq : A * ε = δ / 2 := by
    dsimp only [ε]
    field_simp
  calc |partialDonaldsonFunctional L T omega hmass k hk φ (supNorm L T W k φ) -
        partialDonaldsonFunctional L T omega hmass k hk φ (l2Norm L T W μ hBM k hk φ)|
      ≤ sourceDonaldsonNormalization n k *
          ((2 * Module.finrank ℂ (idealSections L T k φ) : ℕ) : ℝ) *
            (Real.log C + ε * k) := h
    _ ≤ sourceDonaldsonNormalization n k * (2 * (D * (k : ℝ) ^ n)) *
          (Real.log C + ε * k) := by
        have hc := sourceDonaldsonNormalization_nonneg n k
        have hl : 0 ≤ Real.log C + ε * k := by positivity
        push_cast
        gcongr
    _ = A * (Real.log C / (k : ℝ) + ε) := by
        dsimp only [A, sourceDonaldsonNormalization]
        rw [pow_succ]
        field_simp
    _ = A * Real.log C / (k : ℝ) + δ / 2 := by rw [mul_add, hεeq]; ring
    _ < δ := by linarith

end SGPT.Bergman.PartialDonaldson
