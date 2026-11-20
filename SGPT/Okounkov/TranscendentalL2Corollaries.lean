import SGPT.Okounkov.TranscendentalL2Assembly
import SGPT.Okounkov.TranscendentalL2Bridge
import SGPT.Okounkov.TranscendentalPartialBook

/-!
# Unconditional corollaries of `modificationL2Generation`

Plan `tok/RELGEN3` (blueprint `l2:bridge`, chapter `claude-tok-l2`). With the `L²` input
`modificationL2Generation : ModificationL2GenerationStatement` proved, the conditional results of
RELGEN, LIFT and PARTIAL become unconditional:

* `relativeGlobalGeneration`: relative global generation (`tok:relgen`);
* `pushforwardAnalyticStatement`: DRWNXZ Lemma 2.8 (`tok:boucksom-pushforward`, Boucksom);
* `liftingInvarianceStatement`: item 3 of `thm:Okounkovtranmain` (`tok:lifting-invariance`);
* PARTIAL: `partialOkounkovBody_birational` (DRWNXZ Lemma 5.5), the book's `lma:Okounkov:L1426`
  (`analyticPartialBodyOf_eq_of_resolutionData`, independence of the resolution data in
  `def:POBanalsing`), `lma:liftOkounana` (`analyticPartialBody_pullback`), the inclusions of
  `lma:Okounkovanalycomp` (`analyticPartialBody_subset`), and `A_n ⇒ B_n`
  (`partialVolumeIdentity_of_volumeIdentityAll`); the volume formula of `lma:Okounkovanalycomp`
  (`volume_analyticPartialBody`) remains conditional only on item 1 (`VolumeIdentityAllStatement`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory
open scoped ENNReal Topology Matrix Pointwise Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen SGPT.Okounkov.TranscendentalPartial

/-! ### RELGEN and LIFT -/

/-- **Relative global generation** (blueprint `tok:relgen`), unconditional. -/
theorem relativeGlobalGeneration : RelativeGlobalGenerationStatement.{u} :=
  relativeGlobalGeneration_of_modificationL2Generation modificationL2Generation

/-- **DRWNXZ Lemma 2.8** (Boucksom; blueprint `tok:boucksom-pushforward`), unconditional:
pushforwards of potentials with analytic singularities along analytic modifications have
analytic singularities. -/
theorem pushforwardAnalyticStatement : PushforwardAnalyticStatement.{u} :=
  pushforwardAnalyticStatement_of_modificationL2Generation modificationL2Generation

/-- **Item 3 of `thm:Okounkovtranmain`** (lifting invariance, blueprint `tok:lifting-invariance`),
unconditional. -/
theorem liftingInvarianceStatement {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.LiftingInvarianceStatement F :=
  liftingInvarianceStatement_of_modificationL2Generation modificationL2Generation F

/-! ### PARTIAL -/

section Partial

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **DRWNXZ Lemma 5.5** (`tok:partial-birational`), unconditional. -/
theorem partialOkounkovBody_birational {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    {hπ : IsFlagLifting F W π} {D : MeteredEffectiveQDivisor (m + 1) W.carrier}
    {b : W.carrier → EReal} (hR : IsResolutionData θ ψ hπ D b)
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    SGPT.PSH.BookCurrent.IsBig
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)) ∧
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ =
        flagValuation W D.weight +ᵥ
          tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) :=
  TranscendentalPartial.partialOkounkovBody_birational pushforwardAnalyticStatement hR hK hA

/-- **`lma:Okounkov:L1426`** (independence of the modification in `def:POBanalsing`),
unconditional: two choices of resolution data of a Kähler current `T ∈ 𝒜(ξ)` give the same body. -/
theorem analyticPartialBodyOf_eq_of_resolutionData {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ)
    {W₁ : OriginalFlagGeometry.{u} (m + 1)} {π₁ : W₁.carrier → F.carrier}
    {hπ₁ : IsFlagLifting F W₁ π₁} {D₁ : MeteredEffectiveQDivisor (m + 1) W₁.carrier}
    {b₁ : W₁.carrier → EReal} (hR₁ : IsResolutionData θ ψ hπ₁ D₁ b₁)
    {W₂ : OriginalFlagGeometry.{u} (m + 1)} {π₂ : W₂.carrier → F.carrier}
    {hπ₂ : IsFlagLifting F W₂ π₂} {D₂ : MeteredEffectiveQDivisor (m + 1) W₂.carrier}
    {b₂ : W₂.carrier → EReal} (hR₂ : IsResolutionData θ ψ hπ₂ D₂ b₂) :
    analyticPartialBodyOf θ hπ₁ D₁ = analyticPartialBodyOf θ hπ₂ D₂ :=
  TranscendentalPartial.analyticPartialBodyOf_eq_of_resolutionData pushforwardAnalyticStatement
    hK hA hR₁ hR₂

/-- **The book's body of `def:POBanalsing` is the DRWNXZ partial body**, unconditional. -/
theorem analyticPartialBody_eq_partialOkounkovBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) :
    analyticPartialBody F θ ψ = partialOkounkovBody F θ ψ :=
  TranscendentalPartial.analyticPartialBody_eq_partialOkounkovBody pushforwardAnalyticStatement
    hψ hK

/-- **`lma:liftOkounana`**, unconditional: `Δ_{W•}(π^*T) = Δ_{Y•}(T) g`. -/
theorem analyticPartialBody_pullback {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) {W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    analyticPartialBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) (fun y => ψ (π y)) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' analyticPartialBody F θ ψ :=
  TranscendentalPartial.analyticPartialBody_pullback pushforwardAnalyticStatement hψ hK hπ

/-- **`lma:Okounkovanalycomp`, inclusions**, unconditional: for Kähler currents `T ⪯ S` in
`𝒜ᵍ(ξ)`, `Δ_{Y•}(T) ⊆ Δ_{Y•}(S) ⊆ Δ_{Y•}(α)`. -/
theorem analyticPartialBody_subset {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {χ ψ : F.carrier → EReal} (hχ : χ ∈ globalAnalyticCurrents θ)
    (hKχ : IsKahlerCurrentPotential θ χ) (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hKψ : IsKahlerCurrentPotential θ ψ) (hχψ : SingularityLE χ ψ) :
    analyticPartialBody F θ χ ⊆ analyticPartialBody F θ ψ ∧
      analyticPartialBody F θ ψ ⊆ tradOkounkovBody F θ :=
  TranscendentalPartial.analyticPartialBody_subset pushforwardAnalyticStatement hχ hKχ hψ hKψ hχψ

/-- **`lma:Okounkovanalycomp`, volume**, conditional only on the volume identity in dimension `n`
(`thm:Okounkovtranmain` (1)). -/
theorem volume_analyticPartialBody (hA : VolumeIdentityAllStatement.{u} m)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ ψ) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    volume (analyticPartialBody F θ ψ) = diagonalPotentialMass θ ψ hψ.1 / ((m + 1)! : ℝ≥0∞) :=
  TranscendentalPartial.volume_analyticPartialBody pushforwardAnalyticStatement hA hψ hK

end Partial

/-- **`tok:A-iff-B`, `A_n ⇒ B_n`** (DRWNXZ Lemma 5.6), unconditional. -/
theorem partialVolumeIdentity_of_volumeIdentityAll {m : ℕ}
    (hA : VolumeIdentityAllStatement.{u} m) : PartialVolumeIdentityStatement.{u} m :=
  TranscendentalPartial.partialVolumeIdentity_of_volumeIdentityAll pushforwardAnalyticStatement hA

/-- **`tok:A-iff-B`** (DRWNXZ Lemma 5.6), unconditional: `A_n ⟺ B_n`. -/
theorem volumeIdentity_iff_partialVolumeIdentity (m : ℕ) :
    VolumeIdentityAllStatement.{u} m ↔ PartialVolumeIdentityStatement.{u} m :=
  TranscendentalPartial.volumeIdentity_iff_partialVolumeIdentity pushforwardAnalyticStatement m

end SGPT.Okounkov.TranscendentalL2
