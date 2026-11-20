import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum

set_option autoImplicit false
noncomputable section

/-! Whole original comparison/envelope characterizations: the actual global P
relation, source all-chart multiplier domains, and literal normalized suprema.
Positive mass is required only in the original positive-reference statements. -/

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section GlobalComparison
variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}

/-- Whole original `lma:Plor1`, with both original positive masses and big class. -/
theorem sourcePEnvelope_max (omega : KahlerBackground n M)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (_hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ) :
    sourceSingularityEnvelope θ (fun x => max (φ x) (ψ x)) =
      sourceSingularityEnvelope θ
        (fun x => max (sourceSingularityEnvelope θ φ x) (sourceSingularityEnvelope θ ψ x)) := by
  let w : M → EReal := fun x => max (φ x) (ψ x)
  let G : M → EReal := fun x =>
    max (sourceSingularityEnvelope θ φ x) (sourceSingularityEnvelope θ ψ x)
  have hw : (ofFixedModel n M).IsThetaPSH θ w := sourceThetaMaximum_genuine hφ hψ
  have hwpos : 0 < sourcePotentialNonPluripolarMeasure θ w hw univ :=
    hφpos.trans_le (sourcePotentialNonPluripolarMass_mono omega hφ hw
      (MoreSingularOn.of_le fun x _ => le_max_left _ _))
  have hφP : MoreSingularOn φ (sourceSingularityEnvelope θ φ) univ := by
    rw [sourceSingularityEnvelope_eq_native]
    exact moreSingularOn_singularityEnvelope ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
  have hψP : MoreSingularOn ψ (sourceSingularityEnvelope θ ψ) univ := by
    rw [sourceSingularityEnvelope_eq_native]
    exact moreSingularOn_singularityEnvelope ((isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ)
  obtain ⟨a, ha⟩ := hφP
  obtain ⟨b, hb⟩ := hψP
  have hwG : SGPT.PSH.SingularityLE w G := by
    refine ⟨max a b, fun x hx => max_le ?_ ?_⟩
    · exact (ha x hx).trans (add_le_add (le_max_left _ _)
        (EReal.coe_le_coe_iff.mpr (le_max_left a b)))
    · exact (hb x hx).trans (add_le_add (le_max_right _ _)
        (EReal.coe_le_coe_iff.mpr (le_max_right a b)))
  have hφw : SGPT.PSH.SingularityLE φ w :=
    MoreSingularOn.of_le fun x _ => le_max_left _ _
  have hψw : SGPT.PSH.SingularityLE ψ w :=
    MoreSingularOn.of_le fun x _ => le_max_right _ _
  have hGF : G ≤ sourceSingularityEnvelope θ w := fun x =>
    max_le (sourceOrdinaryEnvelope_mono hφw x) (sourceOrdinaryEnvelope_mono hψw x)
  change sourceSingularityEnvelope θ w = sourceSingularityEnvelope θ G
  refine le_antisymm (sourceOrdinaryEnvelope_mono hwG) ?_
  exact (sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ => hGF x)).trans_eq
    (sourceOrdinaryEnvelope_idempotent_of_positive_mass omega hw hwpos)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem native_of_sourceQPSH {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨η, hη⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential η u).mp hη).quasiPshPotential

/-- Whole P clause of original `lma:reform_preceqP` on the genuine QPSH domain. -/
theorem sourcePOrder_iff_sourcePEquivalent_max (omega : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ) :
    GlobalPComparison.sourcePOrder (n := n) φ ψ ↔
      GlobalPComparison.sourcePEquivalent (n := n) (fun x => max (φ x) (ψ x)) ψ :=
  GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    omega (native_of_sourceQPSH hφ) (native_of_sourceQPSH hψ)

/-- Whole I clause of original `lma:reform_preceqP`, retaining every source domain. -/
theorem sourceIOrder_iff_sourceIEquivalent_max (omega : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ) :
    sourceIOrder (ofFixedModel n M) φ ψ ↔
      sourceIEquivalent (ofFixedModel n M) (fun x => max (φ x) (ψ x)) ψ := by
  have hmax := hφ.max_compactKahler omega hψ
  exact (sourceIOrder_iff_native hφ hψ).trans
    ((GlobalQuasiPshMaximumOrders.iOrderOnManifold_iff_iEquivalent_max_globalQuasiPsh
      omega (native_of_sourceQPSH hφ) (native_of_sourceQPSH hψ)).trans
      (sourceIEquivalent_iff_native hmax hψ).symm)

omit [BorelSpace M] in
/-- Whole original `cor:PimpliesI` from the actual existential global P witness. -/
theorem sourceIOrder_of_sourcePOrder
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ)
    (hP : GlobalPComparison.sourcePOrder (n := n) φ ψ) :
    sourceIOrder (ofFixedModel n M) φ ψ :=
  (sourceIOrder_iff_native hφ hψ).mpr
    (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder hP)

/-- The entire displayed ordinary-to-P-to-I comparison chain after `cor:PimpliesI`. -/
theorem sourceComparison_chain (omega : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ)
    (hmore : SGPT.PSH.SingularityLE φ ψ) :
    GlobalPComparison.sourcePOrder (n := n) φ ψ ∧ sourceIOrder (ofFixedModel n M) φ ψ := by
  have hP := GlobalPComparison.sourcePOrder_of_moreSingular omega
    (native_of_sourceQPSH hφ) (native_of_sourceQPSH hψ) hmore
  exact ⟨hP, sourceIOrder_of_sourcePOrder hφ hψ hP⟩

/-- First whole equality of original `cor:Pvarphidef3`, as an ordinary function supremum. -/
theorem sourcePEnvelope_eq_sSup_sourcePEquivalent (omega : KahlerBackground n M)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    sourceSingularityEnvelope θ φ = sSup
      {ψ : M → EReal | (ofFixedModel n M).IsThetaPSH θ ψ ∧ ψ ≤ 0 ∧
        GlobalPComparison.sourcePEquivalent (n := n) ψ φ} := by
  rw [sourceSingularityEnvelope_eq_native]
  simpa only [isThetaPSH_iff_nativeThetaPotential] using
    (PositiveGlobalPEnvelopeSuprema.singularityEnvelope_eq_sSup_sourcePEquivalent
      omega (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ) hφpos)

/-- Second whole equality of original `cor:Pvarphidef3`; candidate mass may vanish. -/
theorem sourcePEnvelope_eq_sSup_sourcePOrder (omega : KahlerBackground n M)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    sourceSingularityEnvelope θ φ = sSup
      {ψ : M → EReal | (ofFixedModel n M).IsThetaPSH θ ψ ∧ ψ ≤ 0 ∧
        GlobalPComparison.sourcePOrder (n := n) ψ φ} := by
  rw [sourceSingularityEnvelope_eq_native]
  simpa only [isThetaPSH_iff_nativeThetaPotential] using
    (PositiveGlobalPEnvelopeSuprema.singularityEnvelope_eq_sSup_sourcePOrder
      omega (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ) hφpos)

end GlobalComparison

section IdealEnvelope
variable [CompactSpace M] [Nonempty M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}

private theorem sourceIEnvelope_le_of_sourceIOrder
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hI : sourceIOrder (ofFixedModel n M) φ ψ) :
    sourceIEnvelope θ φ ≤ sourceIEnvelope θ ψ := by
  rw [sourceIEnvelope_eq_native θ φ hφ, sourceIEnvelope_eq_native θ ψ hψ]
  exact ActualIEnvelopeOrderInfimum.iSingularityEnvelope_le_of_iOrderOnManifold
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ)
    ((sourceIOrder_iff_native ⟨θ, hφ⟩ ⟨θ, hψ⟩).mp hI)

/-- Whole original `cor:Ienvelopedef2`, with an ordinary supremum of ALL source candidates. -/
theorem sourceIEnvelope_eq_sSup_sourceIOrder
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEnvelope θ φ = sSup
      {ψ : M → EReal | (ofFixedModel n M).IsThetaPSH θ ψ ∧ ψ ≤ 0 ∧
        sourceIOrder (ofFixedModel n M) ψ φ} := by
  have hB := isThetaPSH_sourceIEnvelope hφ
  have hφB := sourceIEquivalent_iEnvelope hφ
  refine le_antisymm (le_sSup ⟨hB, sourceIEnvelope_le_zero θ φ, hφB.2⟩) (sSup_le ?_)
  rintro ψ ⟨hψ, hψ0, hψφ⟩
  exact (le_sourceIEnvelope hψ hψ0 (sourceIEquivalent_refl ⟨θ, hψ⟩)).trans
    (sourceIEnvelope_le_of_sourceIOrder hψ hφ hψφ)

/-- Both directions of original `prop:Icomparandenvelope` on the same genuine domain. -/
theorem sourceIOrder_iff_sourceIEnvelope_le
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ) :
    sourceIOrder (ofFixedModel n M) φ ψ ↔ sourceIEnvelope θ φ ≤ sourceIEnvelope θ ψ := by
  constructor
  · intro hI
    rw [sourceIEnvelope_eq_sSup_sourceIOrder hφ, sourceIEnvelope_eq_sSup_sourceIOrder hψ]
    apply sSup_le_sSup
    rintro η ⟨hη, hη0, hηφ⟩
    exact ⟨hη, hη0, sourceIOrder_trans hηφ hI⟩
  · intro hle
    have hA := isThetaPSH_sourceIEnvelope hφ
    have hB := isThetaPSH_sourceIEnvelope hψ
    have hAB : sourceIOrder (ofFixedModel n M) (sourceIEnvelope θ φ) (sourceIEnvelope θ ψ) :=
      (sourceIOrder_iff_native ⟨θ, hA⟩ ⟨θ, hB⟩).mpr
        (iOrderOnManifold_of_le
          ((isThetaPSH_iff_nativeThetaPotential θ _).mp hB).1.quasiPlurisubharmonic hle)
    exact sourceIOrder_trans (sourceIEquivalent_iEnvelope hφ).1
      (sourceIOrder_trans hAB (sourceIEquivalent_iEnvelope hψ).2)

end IdealEnvelope
end SGPT.PSH.VariableComplexAtlas
