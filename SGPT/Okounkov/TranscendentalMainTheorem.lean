import SGPT.Okounkov.TranscendentalWNConvFL4
import SGPT.Okounkov.TranscendentalL2Corollaries
import SGPT.Okounkov.PartialBodyVolume

/-!
# `thm:Okounkovtranmain` (corrected statement)

`TranscendentalMain.okounkovTranMain`: for every flag geometry `(X, Y•)` of a compact Kähler
manifold, the transcendental Okounkov body `Δ_{Y•}(α)` of a big class is well defined (independent
of the representative) and a convex body, and items 1–4 of `thm:Okounkovtranmain` hold, with item 5
for Kähler classes (the printed item 5 for all big classes is false, ERRATA E12).

Proof: `okounkovTranMain_of_FL4` (assembly of all packages; the volume identity via the induction
over dimension and WN21 Theorem C along the deformation to the normal cone).

Consequences discharging item 1 in earlier conditional results: the volume identity for every
dimension (`TranscendentalPartial.volumeIdentityAll`), the volume of partial Okounkov bodies of
Kähler currents with analytic singularities (`lma:Okounkovanalycomp`), of Kähler currents
(`prop:Okounkov:L1551`) and of general currents (`thm:pobmain` (1)).
-/

universe u

namespace SGPT.Okounkov

namespace TranscendentalWN

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- WN21 §§6–7: the key convergence (hard inequality), unconditional. -/
theorem keyConvergence : KeyConvergenceStatement F :=
  keyConvergence_of_measureControl_of_fibreLimit F (measureControl F) (fibreLimit_of_FL4 F)

/-- **WN21 Theorem C** (DRWNXZ Theorem 2.10): the integrated identity and the continuity of the
restricted volume, unconditional. -/
theorem wnStatement : WNStatement F :=
  wnStatement_of_keyConvergence F (keyConvergence F) (exceptionalRestrictedVolume_formula F)

/-- **WN21 Theorem C** (`tok:ext-wn21`): `d/dt vol(ξ − t{Y₁})|_{t=0} = −n vol_{X|Y₁}(ξ)`,
unconditional. -/
theorem wnDerivative : WNDerivativeStatement F :=
  wnDerivative_of_keyConvergence F (keyConvergence F) (exceptionalRestrictedVolume_formula F)

end TranscendentalWN

namespace TranscendentalMain

/-- **`thm:Okounkovtranmain`** (corrected: item 5 for Kähler classes, ERRATA E12). -/
theorem okounkovTranMain :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), OkounkovTranMainStatement F :=
  okounkovTranMain_of_FL4

end TranscendentalMain

namespace TranscendentalPartial

/-- Property `A_n` for every `n`: the volume identity `vol Δ_{Y•}(α) = vol α / n!`. -/
theorem volumeIdentityAll (m : ℕ) : VolumeIdentityAllStatement.{u} m :=
  fun F => (TranscendentalMain.okounkovTranMain m F).2.2.1

end TranscendentalPartial

section Corollaries

open Set Filter MeasureTheory
open scoped ENNReal Topology Matrix Pointwise Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen SGPT.Okounkov.TranscendentalPartial

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `lma:Okounkovanalycomp`, volume formula: `vol Δ(T) = (1/n!) ∫⟨Tⁿ⟩` for a Kähler current with
analytic singularities of a global type, unconditional. -/
theorem TranscendentalL2.volume_analyticPartialBody_uncond
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ ψ) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    volume (analyticPartialBody F θ ψ) = diagonalPotentialMass θ ψ hψ.1 / ((m + 1)! : ℝ≥0∞) :=
  TranscendentalL2.volume_analyticPartialBody (volumeIdentityAll m) hψ hK

/-- `prop:Okounkov:L1551`: `vol Δ(T) = vol(T)/n!` for a Kähler current `T`, unconditional. -/
theorem PartialBody.volume_kahlerPartialBody_uncond
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {w : F.carrier → EReal}
    (hw : IsKahlerCurrentPotential θ w) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    haveI : Nonempty F.carrier := PartialBody.nonempty_carrier F
    volume (PartialBody.kahlerPartialBody F θ w) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) w
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hw) /
          ((m + 1).factorial : ℝ≥0∞) :=
  PartialBody.volume_kahlerPartialBody (volumeIdentityAll m) hw

/-- `thm:pobmain` (1): `vol Δ(T) = vol(T)/n!` for every `T ∈ 𝒵₊(X, α)`, unconditional. -/
theorem PartialBody.volume_generalPartialBody_uncond
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {w : F.carrier → EReal}
    (hw : IsThetaPshPotential θ.val w) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    haveI : Nonempty F.carrier := PartialBody.nonempty_carrier F
    volume (PartialBody.generalPartialBody F θ w) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) w hw /
        ((m + 1).factorial : ℝ≥0∞) :=
  PartialBody.volume_generalPartialBody (volumeIdentityAll m) hw

end Corollaries

end SGPT.Okounkov
