import SGPT.Okounkov.EffectiveDivisorResidual
import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder

set_option autoImplicit false
noncomputable section

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
open IdealWeightPowers DivisorExponent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The produced integer power of a genuine unit divisor metric has exactly
that original squared-logarithmic generic coefficient, including zero. -/
theorem sourceGeneric_unit_divisor_metric_nsmul_eq
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (L : EffectiveDivisor (m + 1) M) (hLI : L.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hmetric : DivisorMetric.IsDivisorMetric L E)
    (a : ℕ) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun x => a • E.weight x) = (a : ℝ≥0∞) := by
  by_cases ha : a = 0
  · subst a
    simpa only [zero_nsmul, Nat.cast_zero] using sourceGeneric_subtype_zero hW.2.1.nonempty
  have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hscale := flagGenericLelong_smul_eq (n := m + 1)
    (fun _ : Fin (m + 1 + 1) => W) E.weight 0 haR
  have hfun : (fun x => a • E.weight x) =
      (fun x => ((a : ℝ) : EReal) * E.weight x) := by
    funext x
    rw [EReal.nsmul_eq_mul, EReal.coe_coe_eq_natCast]
  rw [hfun]
  change sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
    (fun x => ((a : ℝ) : EReal) * E.weight x) = _
  simpa only [flagGenericLelong, sourceGeneric_divisor_metric_eq_one hW L hLI E hmetric,
    mul_one, ENNReal.ofReal_natCast] using hscale

/-- The actual ideal factorization manufactures genuine theta-PSH
membership and original multiplier equivalence of the literal sum weight.
This is the same producer reused by the integer reader and trace handoff. -/
theorem iEquivalent_effectiveDivisorMetric_factorized_weights [CompactSpace M]
    (D L R : EffectiveDivisor (m + 1) M) (a : ℕ)
    (hDR : D.ideal = (idealPow L.ideal a).mul R.ideal)
    (ED EL ER : MeteredEffectiveQDivisor (m + 1) M)
    (hED : DivisorMetric.IsDivisorMetric D ED)
    (hEL : DivisorMetric.IsDivisorMetric L EL)
    (hER : DivisorMetric.IsDivisorMetric R ER) :
    ∃ _hF : IsThetaPshPotential (((a : ℝ) • EL.curvature) + ER.curvature).val
        (fun x => a • EL.weight x + ER.weight x),
      IEquivalentOnManifold (n := m + 1) ED.weight
        (fun x => a • EL.weight x + ER.weight x) := by
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have hv := isThetaPshPotential_effectiveDivisorMetric L EL hEL
  have hw := isThetaPshPotential_effectiveDivisorMetric R ER hER
  have hfun : (fun x => a • EL.weight x) =
      (fun x => ((a : ℝ) : EReal) * EL.weight x) := by
    funext x
    rw [EReal.nsmul_eq_mul, EReal.coe_coe_eq_natCast]
  obtain ⟨hav, _⟩ := exists_thetaPotentialCurrent_nonneg_smul hv (Nat.cast_nonneg a)
  have hav' : IsThetaPshPotential ((a : ℝ) • EL.curvature).val
      (fun x => a • EL.weight x) := by rwa [← hfun] at hav
  obtain ⟨hF, _⟩ := exists_thetaPotentialCurrent_add hav' hw
  have htypeF := hasAnalyticSingularitiesOfType_mul
    (hasAnalyticSingularitiesOfType_pow
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEL) a)
    (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hER)
  rw [← hDR] at htypeF
  obtain ⟨⟨C, hC⟩, ⟨B, hB⟩⟩ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hED) htypeF
  have hI : IEquivalentOnManifold (n := m + 1) ED.weight
      (fun x => a • EL.weight x + ER.weight x) :=
    ⟨iOrderOnManifold_of_le_add hF.1.quasiPlurisubharmonic
        (fun x => hC x (mem_univ x)),
      iOrderOnManifold_of_le_add hu.1.quasiPlurisubharmonic
        (fun x => hB x (mem_univ x))⟩
  exact ⟨hF, hI⟩

/-- Actual Cartier factorization and actual residual noncontainment identify
the original metric's generic coefficient with the produced integer order.
No reader, singularity comparison or ideal-equivalence certificate is supplied. -/
theorem sourceGeneric_effectiveDivisorMetric_eq_integer_order [CompactSpace M]
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D L R : EffectiveDivisor (m + 1) M)
    (hLI : L.ideal = vanishingIdeal (n := m + 1) W) (a : ℕ)
    (hDR : D.ideal = (idealPow L.ideal a).mul R.ideal) (hnot : ¬ W ⊆ R.support)
    (ED EL ER : MeteredEffectiveQDivisor (m + 1) M)
    (hED : DivisorMetric.IsDivisorMetric D ED)
    (hEL : DivisorMetric.IsDivisorMetric L EL)
    (hER : DivisorMetric.IsDivisorMetric R ER) (hERsup : ER.support = R.support) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) ED.weight =
      (a : ℝ≥0∞) := by
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have hv := isThetaPshPotential_effectiveDivisorMetric L EL hEL
  have hw := isThetaPshPotential_effectiveDivisorMetric R ER hER
  have hfun : (fun x => a • EL.weight x) =
      (fun x => ((a : ℝ) : EReal) * EL.weight x) := by
    funext x
    rw [EReal.nsmul_eq_mul, EReal.coe_coe_eq_natCast]
  obtain ⟨hav, _⟩ := exists_thetaPotentialCurrent_nonneg_smul hv (Nat.cast_nonneg a)
  have hav' : IsThetaPshPotential ((a : ℝ) • EL.curvature).val
      (fun x => a • EL.weight x) := by rwa [← hfun] at hav
  obtain ⟨hF, hI⟩ := iEquivalent_effectiveDivisorMetric_factorized_weights
    D L R a hDR ED EL ER hED hEL hER
  rw [sourceGeneric_subtype_eq_of_iEquivalent hW
    ⟨hu.1.quasiPlurisubharmonic, hu.2⟩ ⟨hF.1.quasiPlurisubharmonic, hF.2⟩ hI,
    sourceGeneric_subtype_add_eq hW
      ⟨hav'.1.quasiPlurisubharmonic, hav'.2⟩ ⟨hw.1.quasiPlurisubharmonic, hw.2⟩,
    sourceGeneric_unit_divisor_metric_nsmul_eq hW L hLI EL hEL a,
    sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains R ER hERsup hnot,
    add_zero]

/-- The original effective divisor and smooth component manufacture every
factorization/metric datum and the exact integer-current-reader identification. -/
theorem exists_effectiveDivisor_integer_reader [CompactSpace M]
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) :
    ∃ (a : ℕ) (R : EffectiveDivisor (m + 1) M)
      (ED : MeteredEffectiveQDivisor (m + 1) M),
      (∀ x ∈ W, ∀ r : ℕ, IsDivNear (m + 1) D.ideal W r x ↔ r ≤ a) ∧
      D.ideal = (idealPow (vanishingIdeal (n := m + 1) W) a).mul R.ideal ∧
      ¬ W ⊆ R.support ∧ ED.support = D.support ∧
      DivisorMetric.IsDivisorMetric D ED ∧
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) ED.weight =
        (a : ℝ≥0∞) := by
  obtain ⟨a, R, ha, hDR, hnot⟩ := exists_effectiveDivisor_residual_smooth_component hW D
  obtain ⟨L, hLI, EL, _hELsup, hEL, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms hW
  obtain ⟨ED, hEDsup, hED⟩ := DivisorMetric.exists_divisorMetric D
  obtain ⟨ER, hERsup, hER⟩ := DivisorMetric.exists_divisorMetric R
  refine ⟨a, R, ED, ha, hDR, hnot, hEDsup, hED, ?_⟩
  exact sourceGeneric_effectiveDivisorMetric_eq_integer_order hW D L R hLI a
    (by rwa [hLI]) hnot ED EL ER hED hEL hER hERsup

end SGPT.Okounkov
