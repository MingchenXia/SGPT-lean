import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum

set_option autoImplicit false

/-! # Actual positive-reference envelopes as ordinary global-P suprema -/

open Set

namespace SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularGlobalPOrder SingularGlobalPMaximum SingularGlobalPEnvelopeBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A true global source comparison to a positive reference internally
produces the positive maximum needed for a normalized envelope bound.
The candidate's original mass is allowed to vanish. -/
theorem le_singularityEnvelope_of_sourcePOrder_of_nonpositive
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ ψ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφpos : HasPositivePotentialMass θ φ hφ)
    (hψ : IsThetaPshPotential θ.val ψ) (hψ0 : ψ ≤ 0)
    (hψφ : SourcePOrder (n := n) ψ φ) : ψ ≤ singularityEnvelope θ.val φ := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hφ.1.hasSmoothLocalPotentials φ hφ
  have hPpos : HasPositivePotentialMass θ (singularityEnvelope θ.val φ) hP := by
    change 0 < diagonalPotentialMass θ (singularityEnvelope θ.val φ) hP
    rw [singularityEnvelopeMassPreserving omega θ φ hφ hP]
    exact hφpos
  have hφP := sourcePEquivalent_singularityEnvelope omega θ hφ
  have hφPfixed := (sourcePEquivalent_iff_pEquivalentWith omega θ
    hφ hP hφpos hPpos).mp hφP
  have hψP := hψφ.trans omega hφP.1
  have hwP := (sourcePOrder_iff_sourcePEquivalent_max omega hψ hP).mp hψP
  have hw := IsThetaPshPotential.max hψ hP
  have hwpos : HasPositivePotentialMass θ
      (fun x => max (ψ x) (singularityEnvelope θ.val φ x)) hw :=
    hPpos.trans_le (diagonalPotentialMass_mono_of_kahler omega hP hw
      (MoreSingularOn.of_le fun x _ => le_max_right _ _))
  have hwPfixed := (sourcePEquivalent_iff_pEquivalentWith omega θ
    hw hP hwpos hPpos).mp hwP
  have hw0 : (fun x => max (ψ x) (singularityEnvelope θ.val φ x)) ≤ 0 :=
    fun x => max_le (hψ0 x) (singularityEnvelope_le_zero θ.val φ x)
  exact (show ψ ≤ (fun x => max (ψ x) (singularityEnvelope θ.val φ x))
    from fun x => le_max_left _ _).trans
    ((self_le_singularityEnvelope hw hw0).trans (hwPfixed.1.trans hφPfixed.2))

/-- The actual positive-reference envelope is itself a normalized
candidate in its global source P-class and bounds all such candidates.
This is an ordinary function supremum, without new regularization. -/
theorem singularityEnvelope_eq_sSup_sourcePEquivalent
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφpos : HasPositivePotentialMass θ φ hφ) :
    singularityEnvelope θ.val φ = sSup
      {ψ : M → EReal | IsThetaPshPotential θ.val ψ ∧ ψ ≤ 0 ∧
        SourcePEquivalent (n := n) ψ φ} := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hφ.1.hasSmoothLocalPotentials φ hφ
  have hφP := sourcePEquivalent_singularityEnvelope omega θ hφ
  refine le_antisymm (le_sSup ⟨hP, singularityEnvelope_le_zero θ.val φ,
    hφP.2, hφP.1⟩) (sSup_le ?_)
  rintro ψ ⟨hψ, hψ0, hψφ⟩
  exact le_singularityEnvelope_of_sourcePOrder_of_nonpositive
    omega θ hφ hφpos hψ hψ0 hψφ.1

/-- The actual envelope also bounds every normalized source-P-more-singular
candidate, including those of zero original mass. -/
theorem singularityEnvelope_eq_sSup_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφpos : HasPositivePotentialMass θ φ hφ) :
    singularityEnvelope θ.val φ = sSup
      {ψ : M → EReal | IsThetaPshPotential θ.val ψ ∧ ψ ≤ 0 ∧
        SourcePOrder (n := n) ψ φ} := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hφ.1.hasSmoothLocalPotentials φ hφ
  have hφP := sourcePEquivalent_singularityEnvelope omega θ hφ
  refine le_antisymm (le_sSup ⟨hP, singularityEnvelope_le_zero θ.val φ,
    hφP.2⟩) (sSup_le ?_)
  rintro ψ ⟨hψ, hψ0, hψφ⟩
  exact le_singularityEnvelope_of_sourcePOrder_of_nonpositive
    omega θ hφ hφpos hψ hψ0 hψφ

end

end SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema
