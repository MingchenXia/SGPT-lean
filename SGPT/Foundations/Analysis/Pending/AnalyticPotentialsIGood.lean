import SGPT.Foundations.Analysis.Pending.AnalyticReferenceIdealGlobalPOrder
import SGPT.Foundations.Analysis.Pending.IGoodBasic

set_option autoImplicit false

/-! # Genuine analytic potentials internally produce actual I-goodness -/

open Set

namespace SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses FirstPass.POrder
  FirstPass.QuasiEquisingularApproximation DiagonalMass
  SingularGlobalPOrder AnalyticReferenceIdealGlobalPOrder

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The analytic-reference ideal bridge internally equates the actual
P- and I-envelopes in any natural positive-mass original background. -/
theorem iGoodWith_of_analytic_type_of_positive_mass
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M} {Φ : M → EReal}
    (hΦ : IsThetaPshPotential θ.val Φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) Φ)
    (hpos : HasPositivePotentialMass θ Φ hΦ) : IGoodWith θ Φ hΦ := by
  let Ψ : M → EReal := iSingularityEnvelope θ.val Φ
  have hΨ : IsThetaPshPotential θ.val Ψ :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hΦ.1.hasSmoothLocalPotentials Φ hΦ
  have hI : IEquivalentOnManifold (n := n) Φ Ψ :=
    iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hΦ.1.hasSmoothLocalPotentials Φ hΦ
  obtain ⟨D, hD⟩ := hΦ.exists_normalized_sub_const
  have hle : (fun x => Φ x - (D : EReal)) ≤ Ψ :=
    le_iSingularityEnvelope hD.1 hD.2 (iEquivalentOnManifold_sub_const Φ D)
  have hmore : MoreSingularOn Φ Ψ univ :=
    (sameSingularityTypeOn_add_const Φ univ (-D)).2.trans
      (MoreSingularOn.of_le fun x _ => by
        simpa only [sub_eq_add_neg, EReal.coe_neg] using hle x)
  have hΨpos : HasPositivePotentialMass θ Ψ hΨ :=
    hpos.trans_le (diagonalPotentialMass_mono_of_kahler
      omega hΦ hΨ hmore)
  have hforward : SourcePOrder (n := n) Φ Ψ :=
    sourcePOrder_of_moreSingularOn omega θ θ hΦ hΨ hmore
  have hreverse : SourcePOrder (n := n) Ψ Φ :=
    sourcePOrder_of_iOrderOnManifold_of_analytic_reference omega
      hΨ.quasiPshPotential hΦ.quasiPshPotential hA hI.2
  have hPeq : singularityEnvelope θ.val Φ = singularityEnvelope θ.val Ψ :=
    pEquivalentWith_iff_envelope_eq.mp
      ((sourcePEquivalent_iff_pEquivalentWith omega θ hΦ hΨ hpos hΨpos).mp
        ⟨hforward, hreverse⟩)
  refine ⟨hpos, hPeq.trans ?_⟩
  exact singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hΦ.1.hasSmoothLocalPotentials Φ hΦ

/-- The actual positive Kähler background is produced from the natural
genuine global quasi-PSH input; no I-goodness or mass witness is supplied. -/
theorem iGood_of_globalQuasiPsh_of_analytic_type
    (omega : KahlerBackground n M) {Φ : M → EReal}
    (hΦ : IsGlobalQuasiPshPotential (n := n) Φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) Φ) : IGood (n := n) Φ := by
  obtain ⟨C, _, hΦC, _, hpos, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega hΦ hΦ
  exact (iGoodWith_of_analytic_type_of_positive_mass omega hΦC hA hpos).iGood

end

end SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood
