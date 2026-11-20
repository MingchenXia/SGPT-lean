import SGPT.Okounkov.SourceValuativeSetClosure
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceValuativeClosure
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending DiagonalMass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody SGPT.Okounkov.Valuative

/-- The SAME original current comparison set only depends on its actual
I-class; all actual real valuation vectors remain unchanged. -/
theorem valuationsBelow_eq_of_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) {u v : F.carrier → EReal}
    (hI : IEquivalentOnManifold (n := m + 1) u v) :
    valuationsBelow F θ u = valuationsBelow F θ v := by
  ext x
  constructor
  · rintro ⟨ψ, hψ, hψu, hx⟩
    exact ⟨ψ, hψ, hψu.trans hI.1, hx⟩
  · rintro ⟨ψ, hψ, hψv, hx⟩
    exact ⟨ψ, hψ, hψv.trans hI.2, hx⟩

/-- Actual original body readback, independently of any positive original
NPP mass. The big-class premise is exactly the standing source domain. -/
theorem generalPartialBody_eq_of_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    (hI : IEquivalentOnManifold (n := m + 1) u v) :
    generalPartialBody F θ u = generalPartialBody F θ v :=
  ((generalPartialBody_subset_of_iOrder hu hv hI.1 hbig).1).antisymm
    (generalPartialBody_subset_of_iOrder hv hu hI.2 hbig).1

/-- POSITIVE ORIGINAL I-volume internally yields a genuine positive-NPP-
mass I-equivalent reader. Original NPP mass may be ZERO and is not assumed. -/
theorem exists_positive_mass_iEquivalent_reader {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hpos : letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      letI : Nonempty F.carrier := PartialBody.nonempty_carrier F
      0 < iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ) :
    ∃ ψ : F.carrier → EReal, ∃ hψ : IsThetaPshPotential θ.val ψ,
      IEquivalentOnManifold (n := m + 1) φ ψ ∧
      (letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      HasPositivePotentialMass θ ψ hψ) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  let ψ := iSingularityEnvelope θ.val φ
  have hψ : IsThetaPshPotential θ.val ψ :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ
  refine ⟨ψ, hψ, iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ, ?_⟩
  exact hpos

end SGPT.Okounkov.SourceValuativeClosure
