import SGPT.Okounkov.EffectiveDivisorResidualClass
import SGPT.Okounkov.EffectiveDivisorRestriction
import SGPT.Okounkov.PotentialFlagValuationIndependence
import SGPT.Foundations.Analysis.Pending.AnalyticTraceOrdinaryAgreement
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open IdealWeightPowers

/-- Literal pullback of the actual residual ideal gives the multiplier
class of its genuine restricted Cartier metric; no restriction certificate. -/
theorem iEquivalent_divisorMetric_pullback_restrictedDivisorMetric
    {n k : ℕ} {M V : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [CompactSpace V]
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (R : EffectiveDivisor n M) (RT : EffectiveDivisor k V)
    (hRI : RT.ideal = GermIdeal.pullback (m := k) ι R.ideal)
    (ER : MeteredEffectiveQDivisor n M) (ET : MeteredEffectiveQDivisor k V)
    (hER : DivisorMetric.IsDivisorMetric R ER)
    (hET : DivisorMetric.IsDivisorMetric RT ET) :
    IEquivalentOnManifold (n := k) (fun y => ER.weight (ι y)) ET.weight := by
  have htype := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hι
    (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hER)
  have htypeT := DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hET
  rw [hRI] at htypeT
  obtain ⟨⟨C, hC⟩, ⟨B, hB⟩⟩ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type htype htypeT
  have hR := isThetaPshPotential_effectiveDivisorMetric R ER hER
  have hT := isThetaPshPotential_effectiveDivisorMetric RT ET hET
  have hpull := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hι
    hR.1.quasiPlurisubharmonic
  exact ⟨iOrderOnManifold_of_le_add hT.1.quasiPlurisubharmonic
      (fun y => hC y (mem_univ y)),
    iOrderOnManifold_of_le_add hpull (fun y => hB y (mem_univ y))⟩

/-- Every original unit-metric/source-trace choice agrees with the actual
Cartier residual restriction in multiplier class on the genuine tail. -/
theorem originalFlagStep_effectiveDivisorMetric_target_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier)
    (ED : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hED : DivisorMetric.IsDivisorMetric D ED)
    {a : ℕ} {Dtail : EffectiveDivisor m F.tail.carrier}
    (hC : OriginalCartierFlagStep F D a Dtail)
    {τ : F.tail.carrier → EReal} (hstep : OriginalFlagStep F ED.weight τ)
    (ET : MeteredEffectiveQDivisor m F.tail.carrier)
    (hET : DivisorMetric.IsDivisorMetric Dtail ET) :
    IEquivalentOnManifold (n := m) τ ET.weight := by
  obtain ⟨R, _ha, hDR, hnot, hDtail⟩ := hC
  obtain ⟨_θ, _hθ, L, hLI, EL, hELsup, hEL, htrace⟩ := hstep
  obtain ⟨ER, hERsup, hER⟩ := DivisorMetric.exists_divisorMetric R
  have hfactor : D.ideal = (idealPow L.ideal a).mul R.ideal := by
    simpa only [hLI] using hDR
  have hIambient := iEquivalent_effectiveDivisorMetric_residual_weight
    F.firstDivisor D L R hLI a hfactor hnot ED EL ER hED hEL hELsup hER hERsup
  have hr := isThetaPshPotential_effectiveDivisorMetric R ER hER
  have hzero := sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains
    R ER hERsup hnot
  obtain ⟨τR, htraceR⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      F.omega F.firstDivisor hr hzero
  let W := F.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  let : CompactSpace W := F.tail.compact
  let : ConnectedSpace W := F.tail.connected
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τ at htrace
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι ER.weight τR at htraceR
  have hItarget := iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives
    (Nat.succ_ne_zero m) F.tail.omega F.tail.omega hι htrace htraceR hIambient
  have hntrace := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp htraceR
  have hanalytic :=
    (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hER).hasManifoldAnalyticSingularityType
  have hordinary :=
    AnalyticTraceOrdinaryAgreement.sourcePEquivalent_ordinaryRestriction_of_analytic_isTraceRepresentativeAlong
      F.tail.omega hι hntrace hanalytic
  have hIordinary := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hordinary
  have hImetric := iEquivalent_divisorMetric_pullback_restrictedDivisorMetric
    hι R Dtail hDtail ER ET hER hET
  exact hItarget.trans (hIordinary.trans hImetric)

end SGPT.Okounkov
