import SGPT.Okounkov.TranscendentalDensityPartial
import SGPT.Okounkov.TranscendentalSkodaManifold

/-!
# Density of gentle Kähler currents: the unconditional theorems

Blueprint nodes `tok:density` (DRWNXZ Lemma 3.1 and Definition 3.2) and `tok:partial-analytic`
(DRWNXZ Lemma 5.3). The results of `TranscendentalDensity.lean` and
`TranscendentalDensityPartial.lean` are proved from Skoda's theorem in its manifold form
`ManifoldSkodaStatement`; the SKODA package proves that statement
(`SGPT.Okounkov.TranscendentalSkoda.manifoldSkodaStatement`, `TranscendentalSkodaManifold.lean`).
This file discharges the hypothesis.

## Main results

* `densityStatement : DensityStatement` (`tok:density`): `ν(T) ∈ closure ν(Ω(ξ))` for
  `T ∈ 𝒜(ξ)` when `Ω(ξ) ≠ ∅`.
* `bodyEqualityStatement : BodyEqualityStatement`: `Δ(ξ) = closure ν(Ω(ξ)) = closure ν(𝒜(ξ))`
  for big `ξ`.
* `partialAnalyticStatement : PartialAnalyticStatement` (`tok:partial-analytic`):
  `closure ν(Ω(ξ; R)) = closure ν(𝒜(ξ; R))` for a Kähler current `R ∈ 𝒜(ξ)`.
* `tradOkounkovBody_eq_closure_gentleKahlerCurrents`,
  `tradOkounkovBody_eq_closure_analyticCurrents`: the body equalities for a given big class.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalDensity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSkoda

/-- **`tok:density`** (DRWNXZ Lemma 3.1): if `Ω(ξ) ≠ ∅`, every `T ∈ 𝒜(ξ)` satisfies
`ν(T) ∈ closure ν(Ω(ξ))`. -/
theorem densityStatement : DensityStatement.{u} :=
  densityStatement_of_manifoldSkoda manifoldSkodaStatement

/-- **`tok:density`, consequence** (DRWNXZ Definition 3.2): for a big class,
`Δ(ξ) = closure ν(Ω(ξ)) = closure ν(𝒜(ξ))`. -/
theorem bodyEqualityStatement : BodyEqualityStatement.{u} :=
  bodyEqualityStatement_of_manifoldSkoda manifoldSkodaStatement

/-- **`tok:partial-analytic`** (DRWNXZ Lemma 5.3): for a Kähler current `R = θ + dd^c u` with
analytic singularities, `Δ(ξ; R) = closure ν(Ω(ξ; R)) = closure ν(𝒜(ξ; R))`. -/
theorem partialAnalyticStatement : PartialAnalyticStatement.{u} :=
  partialAnalyticStatement_of_manifoldSkoda manifoldSkodaStatement

/-- `Δ(ξ) = closure ν(Ω(ξ))` for a big class `ξ = {θ}`. -/
theorem tradOkounkovBody_eq_closure_gentleKahlerCurrents {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody F θ = closure (flagValuation F '' gentleKahlerCurrents θ) :=
  (bodyEqualityStatement m F θ hbig).1

/-- `Δ(ξ) = closure ν(𝒜(ξ))` for a big class `ξ = {θ}`. -/
theorem tradOkounkovBody_eq_closure_analyticCurrents {m : ℕ}
    {F : OriginalFlagGeometry.{u} (m + 1)} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody F θ = closure (flagValuation F '' analyticCurrents θ) :=
  (bodyEqualityStatement m F θ hbig).2

end SGPT.Okounkov.TranscendentalDensity
