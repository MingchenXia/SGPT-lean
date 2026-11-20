import SGPT.Okounkov.TranscendentalPartialDefs
import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Foundations.Analysis.Pending.DiagonalMass

/-!
# Partial Okounkov bodies: published statements

Statements only (`def … : Prop`), for the interface rule of the transcendental Okounkov
packages (blueprint `claude-okounkov-transcendental`, PLAN §4).

* `PartialVolumeIdentityStatement m` (DRWNXZ Lemma 5.6, property `B_n`, `n = m + 1`, blueprint
  `tok:A-iff-B`): for every compact connected Kähler manifold of dimension `n` with a smooth flag,
  every class `ξ = {θ}` and every Kähler current `R = θ + dd^c ψ ∈ 𝒜ᵍ(ξ)`,
  `vol Δ(ξ; R) = (1/n!) ∫_X ⟨R^n⟩`.
* `VolumeIdentityAllStatement m` (property `A_n`): `thm:Okounkovtranmain` (1),
  `TranscendentalMain.VolumeIdentityStatement F`, for every flag geometry of dimension `n`.
* `DivisorResidualStatement` (the divisor case of `tok:siu-analytic` used by
  `tok:partial-birational`): if `φ ∈ 𝒜(θ)` is more singular than the weight `ψ_D` of an effective
  `ℚ`-divisor `D` with a smooth metric (`MeteredEffectiveQDivisor`), then `φ = ψ_D + w` with
  `w ∈ 𝒜(θ - Θ_D)`. (DRWNXZ use Siu's decomposition: the generic Lelong numbers of `φ` along the
  components of `D` are at least their coefficients.) It is **proved** in
  `TranscendentalPartialResidual.lean` (`divisorResidualStatement`).

`B_n ⇒ A_n` is proved unconditionally and `A_n ⇒ B_n` conditionally on RELGEN's
`PushforwardAnalyticStatement` in `TranscendentalPartialVolumeIdentity.lean`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set MeasureTheory
open scoped ENNReal Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.PSH SGPT.Okounkov.TranscendentalCore

/-- **Property `B_n`** (DRWNXZ Lemma 5.6, blueprint `tok:A-iff-B`), `n = m + 1`: for every flag
geometry `(X, Y•)` of dimension `n`, every closed real `(1,1)`-form `θ` and every Kähler current
`R = θ + dd^c ψ` with analytic singularities of a global type (`ψ ∈ 𝒜ᵍ(θ)`),
`vol Δ_{Y•}({θ}; R) = (1/n!) ∫_X ⟨R^n⟩` (Lebesgue measure on `ℝⁿ`; non-pluripolar mass for the
Borel structure of `X`). -/
def PartialVolumeIdentityStatement (m : ℕ) : Prop :=
  ∀ (F : OriginalFlagGeometry.{u} (m + 1)) (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (ψ : F.carrier → EReal) (hψ : ψ ∈ globalAnalyticCurrents θ), IsKahlerCurrentPotential θ ψ →
      letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      volume (partialOkounkovBody F θ ψ) =
        Pending.DiagonalMass.diagonalPotentialMass θ ψ hψ.1 / ((m + 1)! : ℝ≥0∞)

/-- **Property `A_n`** (DRWNXZ Lemma 5.6), `n = m + 1`: the volume identity
`vol Δ_{Y•}(α) = vol α / n!` (`thm:Okounkovtranmain` (1)) for every flag geometry of dimension
`n` and every big class `α`. -/
def VolumeIdentityAllStatement (m : ℕ) : Prop :=
  ∀ F : OriginalFlagGeometry.{u} (m + 1), TranscendentalMain.VolumeIdentityStatement F

/-- **Subtraction of a dominated divisor** (the case of `tok:siu-analytic` used by
`tok:partial-birational`, DRWNXZ Lemma 2.3 / Lemma 5.5): on a compact complex manifold, if
`φ ∈ 𝒜(θ)` and `φ ⪯ ψ_D` for the weight `ψ_D` of a metered effective `ℚ`-divisor `D` (curvature
`Θ_D`), then `φ = ψ_D + w` for some `w ∈ 𝒜(θ - Θ_D)`, i.e. `T - [D]` is a closed positive current
in `{θ} - {D}` with analytic singularities. -/
def DivisorResidualStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] (θ : ClosedRealOneOneForm n M)
    (D : MeteredEffectiveQDivisor n M) (v : M → EReal), v ∈ analyticCurrents θ →
      SingularityLE v D.weight →
        ∃ w ∈ analyticCurrents (θ - D.curvature), ∀ x, v x = D.weight x + w x

end SGPT.Okounkov.TranscendentalPartial
