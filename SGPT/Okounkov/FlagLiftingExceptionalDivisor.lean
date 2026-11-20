import SGPT.Okounkov.FlagLiftingStrictTransform
import SGPT.Okounkov.EffectiveDivisorCoefficient
import SGPT.Okounkov.EffectiveDivisorRestriction
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform

set_option autoImplicit false

noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy SourceTraceRepresentativeDefinition
open SourceGenericSubmanifoldMinimum DivisorExponent IdealWeightPowers

/-- The genuine thin-set presentation manufactures the geometric hypothesis
required by the existing ideal total-transform construction. -/
theorem IsFlagLifting.interior_exceptional_eq_empty {n : ℕ}
    {F W : OriginalFlagGeometry.{u} n} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) : interior (exceptionalLocus n π) = ∅ := by
  obtain ⟨A, _hAc, _hAa, hAi, _hinj, hnon⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ.1
  have hsub : exceptionalLocus n π ⊆ A := by
    intro y hy
    by_contra hyA
    exact hnon y hyA hy
  exact subset_empty_iff.mp ((interior_mono hsub).trans hAi.subset)

/-- Every actual total-transform metric has the original source coefficient
one, produced from the reduced unit divisor and genuine pullback covariance. -/
theorem IsFlagLifting.total_divisor_source_reader_eq_one {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))))
    (EA : MeteredEffectiveQDivisor (m + 1) W.carrier)
    (hEA : DivisorMetric.IsDivisorMetric
      (GermIdealTotalTransform.EffectiveDivisor.totalTransform
        hπ.1.1 hπ.interior_exceptional_eq_empty D) EA) :
    sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) EA.weight = 1 := by
  obtain ⟨EY, _hEYsup, hEY⟩ := DivisorMetric.exists_divisorMetric D
  have huY := isThetaPshPotential_effectiveDivisorMetric D EY hEY
  have huA := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ.1 EY.curvature huY
  have htypeY := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hπ.1.1
    (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEY)
  have htypeA := DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEA
  have huEA := isThetaPshPotential_effectiveDivisorMetric _ EA hEA
  obtain ⟨⟨C, hC⟩, ⟨B, hB⟩⟩ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type htypeA htypeY
  have hI : IEquivalentOnManifold (n := m + 1) EA.weight (EY.weight ∘ π) :=
    ⟨iOrderOnManifold_of_le_add huA.1.quasiPlurisubharmonic
        (fun x => hC x (mem_univ x)),
      iOrderOnManifold_of_le_add huEA.1.quasiPlurisubharmonic
        (fun x => hB x (mem_univ x))⟩
  rw [sourceGeneric_subtype_eq_of_iEquivalent W.firstDivisor
      ⟨huEA.1.quasiPlurisubharmonic, huEA.2⟩
      ⟨huA.1.quasiPlurisubharmonic, huA.2⟩ hI]
  change sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (EY.weight ∘ π) = 1
  rw [hπ.sourceGeneric_first_comp_eq ⟨huY.1.quasiPlurisubharmonic, huY.2⟩]
  exact sourceGeneric_divisor_metric_eq_one F.firstDivisor D hDI EY hEY

/-- Actual maximal Cartier order equals one. The effective residual's literal
restriction and its independent integer tail vector are constructed internally. -/
theorem IsFlagLifting.exists_effective_exceptional_divisor {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))) :
    ∃ (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ),
      OriginalCartierFlagStep W
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
      OriginalCartierFlagValuation m W.tail Dtail ν := by
  let DA := GermIdealTotalTransform.EffectiveDivisor.totalTransform
    hπ.1.1 hπ.interior_exceptional_eq_empty D
  obtain ⟨a, R, EA, ha, hDR, hnot, _hEAsup, hEA, hreader⟩ :=
    exists_effectiveDivisor_integer_reader W.firstDivisor DA
  have hone : (a : ℝ≥0∞) = 1 :=
    hreader.symm.trans (hπ.total_divisor_source_reader_eq_one D hDI EA hEA)
  have haone : a = 1 := by exact_mod_cast hone
  subst a
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  let : IsComplexManifold m (W.flag (1 : Fin (m + 2))) := W.tail.complex
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (Subtype.val : W.tail.carrier → W.carrier) :=
    SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) W.firstDivisor.2.2
  have hIR : RestrictedIdealQuotient.IsInvertibleAlong (m + 1)
      (W.flag (1 : Fin (m + 2))) R.ideal :=
    SubmanifoldDivisorRestriction.isInvertibleAlong_of_isClosedConnectedSubmanifold
      W.firstDivisor R.isInvertible hnot
  let Dtail : EffectiveDivisor m W.tail.carrier :=
    SubmanifoldIdealRestriction.restrictDivisor hval hIR
  obtain ⟨ν, hν⟩ := exists_originalCartierFlagValuation m W.tail Dtail
  exact ⟨Dtail, ν, ⟨R, ha, hDR, hnot, rfl⟩, hν⟩

end SGPT.Okounkov
