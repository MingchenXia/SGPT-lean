import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.IGoodMassReduction
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! # I-goodness descends through actual semipositive background enlargement -/

namespace SGPT.Foundations.Analysis.Pending.IGoodBackgroundDescent

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope FirstPass.POrder
  SingularGlobalPOrder SingularGlobalPEnvelopeBridge DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A genuine semipositive background enlargement cannot turn an original
positive-mass non-I-good potential into an I-good one. -/
theorem iGoodWith_of_semipositive_background_enlargement
    (omega : KahlerBackground n M) {θ σ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hσu : IsThetaPshPotential σ.val u)
    (hsemi : (σ - θ).val.IsSemipositive)
    (hpos : HasPositivePotentialMass θ u hu)
    (hgood : IGoodWith σ u hσu) : IGoodWith θ u hu := by
  let v : M → EReal := iSingularityEnvelope θ.val u
  let w : M → EReal := iSingularityEnvelope σ.val u
  have hv : IsThetaPshPotential θ.val v :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hw : IsThetaPshPotential σ.val w :=
    iSingularityEnvelope_isThetaPshPotential σ.val σ.property.1 σ.property.2
      hσu.1.hasSmoothLocalPotentials u hσu
  have hvσ : IsThetaPshPotential σ.val v := by
    have hform : θ + (σ - θ) = σ := by abel
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  have hIE : IEquivalentOnManifold (n := n) u v :=
    iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hvw : v ≤ w :=
    le_iSingularityEnvelope hvσ (iSingularityEnvelope_le_zero θ.val u) hIE.symm
  have huv : MoreSingularOn u v Set.univ := moreSingularOn_iSingularityEnvelope hu
  have horderuv : SourcePOrder (n := n) u v :=
    sourcePOrder_of_moreSingularOn omega θ θ hu hv huv
  have hordervw : SourcePOrder (n := n) v w :=
    sourcePOrder_of_moreSingularOn omega θ σ hv hw
      (MoreSingularOn.of_le fun x _ => hvw x)
  have horderwu : SourcePOrder (n := n) w u := by
    have hP := (sourcePEquivalent_singularityEnvelope omega σ hσu).2
    change SourcePOrder (n := n) (iSingularityEnvelope σ.val u) u
    rw [← hgood.envelope_eq]
    exact hP
  have hEq : SourcePEquivalent (n := n) v u :=
    ⟨hordervw.trans omega horderwu, horderuv⟩
  have hvpos : HasPositivePotentialMass θ v hv :=
    hpos.trans_le (diagonalPotentialMass_mono_of_kahler omega hu hv huv)
  have hvgood : IGoodWith θ v hv := by
    refine ⟨hvpos, ?_⟩
    exact (singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu).trans
      (iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2
        hu.1.hasSmoothLocalPotentials u hu).symm
  exact IGoodGlobalPStability.iGoodWith_of_sourcePEquivalent omega hv hu hvgood hEq

end

end SGPT.Foundations.Analysis.Pending.IGoodBackgroundDescent
