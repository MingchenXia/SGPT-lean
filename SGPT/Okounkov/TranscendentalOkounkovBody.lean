import SGPT.Okounkov.CurrentFlagValuation
import SGPT.PSH.SourceGentleApproximation
import SGPT.Foundations.Analysis.Pending.DiagonalMass

/-!
# The transcendental Okounkov body of a cohomology class

Source `def:tradOk` (chapter *The theory of Okounkov bodies*, Section *Transcendental partial
Okounkov bodies*, *The traditional approach to the Okounkov body problem*). Let `X` be a
connected compact Kähler manifold of dimension `n > 0` with a smooth flag `Y•`, and let `α` be
a big cohomology class on `X`. The Okounkov body of `α` is

`Δ_{Y•}(α) = closure {ν_{Y•}(S) : S ∈ 𝒵₊(X, α), S has gentle analytic singularities}`.

## Formal setting

The manifold and its smooth flag are an `OriginalFlagGeometry`, the setting of the already
formalized current valuation `ν_{Y•}` (source `def:valcurr`, `currentFlagValuation`, and its
potential form `potentialFlagValuation`). The class `α` is represented by a closed real smooth
`(1,1)`-form `θ`; the currents in `𝒵₊(X, α)` are exactly the currents `θ + dd^c u` with
`u ∈ PSH(X, θ)` (the source convention `rmk:qpshtocurrents`), and such a current has gentle
analytic singularities when its potential does (source `def:analy-sing`, formalized as
`SGPT.PSH.SourceGentleAnalyticSingularities`; the potential is unique up to an additive
constant and the condition is insensitive to it). Thus the formal definition takes the closure
of the set of valuations `ν_{Y•}(θ + dd^c u)` of gentle potentials `u ∈ PSH(X, θ)`.
`mem_gentleCurrentValuations_iff_current` restates membership through the whole-current
valuation `currentFlagValuation` of the current `θ + dd^c u`.

The bigness of `α` is a hypothesis of the consumers (`thm:Okounkovtranmain`), not of the
definition.

## The expectation of `rmk:Okounkov:L1841`

`thm:Deltapartialint` writes the partial Okounkov body of `T ∈ 𝒵₊(X, α)_{>0}` as the closure of
the valuations `ν_{Y•}(S)` of the currents `S ∈ 𝒵₊(X, α)` with `S ⪯_𝓘 T`; the remark
`rmk:Okounkov:L1841` expects that this closure is not necessary, i.e. that the set of these
valuations is already closed. `valuativeClosureUnnecessaryStatement` is that expectation as a
proposition (a statement only, not a proof).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open NaturalThetaPshClosedCurrent

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)

/-- A quasi-psh potential has gentle analytic singularities (of some type `(c, 𝓘)`), source
`def:analy-sing`. -/
def HasSourceGentleAnalyticSingularities (v : F.carrier → EReal) : Prop :=
  ∃ (c : ℚ) (𝔞 : GermIdeal n F.carrier), SGPT.PSH.SourceGentleAnalyticSingularities v c 𝔞

/-- The valuations `ν_{Y•}(θ + dd^c u)` of the currents of the class `{θ}` with gentle analytic
singularities. -/
def gentleCurrentValuations (θ : ClosedRealOneOneForm n F.carrier) : Set (Fin n → ℝ) :=
  {x | ∃ (v : F.carrier → EReal) (hv : IsThetaPshPotential θ.val v),
    HasSourceGentleAnalyticSingularities F v ∧
      x = fun i => ((potentialFlagValuation F hv i : ℝ≥0) : ℝ)}

/-- Source `def:tradOk`: the Okounkov body `Δ_{Y•}(α)` of the class `α = {θ}` with respect to the
smooth flag of `F`, the closure of the valuations of the currents in `𝒵₊(X, α)` with gentle
analytic singularities. -/
def tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) : Set (Fin n → ℝ) :=
  closure (gentleCurrentValuations F θ)

variable {F}

theorem isClosed_tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) :
    IsClosed (tradOkounkovBody F θ) :=
  isClosed_closure

theorem gentleCurrentValuations_subset_tradOkounkovBody
    (θ : ClosedRealOneOneForm n F.carrier) :
    gentleCurrentValuations F θ ⊆ tradOkounkovBody F θ :=
  subset_closure

/-- The valuation of a gentle current of the class lies in the Okounkov body. -/
theorem potentialFlagValuation_mem_tradOkounkovBody {θ : ClosedRealOneOneForm n F.carrier}
    {v : F.carrier → EReal} (hv : IsThetaPshPotential θ.val v)
    (hgentle : HasSourceGentleAnalyticSingularities F v) :
    (fun i => ((potentialFlagValuation F hv i : ℝ≥0) : ℝ)) ∈ tradOkounkovBody F θ :=
  subset_closure ⟨v, hv, hgentle, rfl⟩

/-- The Okounkov body lies in the closed nonnegative orthant `ℝⁿ_{≥ 0}`. -/
theorem tradOkounkovBody_subset_nonneg (θ : ClosedRealOneOneForm n F.carrier) :
    tradOkounkovBody F θ ⊆ {x | ∀ i, 0 ≤ x i} := by
  have hclosed : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  refine closure_minimal ?_ hclosed
  rintro x ⟨v, hv, -, rfl⟩ i
  exact NNReal.coe_nonneg _

/-- Membership in the generating set through the whole-current valuation `ν_{Y•}(S)` of the
current `S = θ + dd^c v` (source `def:valcurr`). -/
theorem mem_gentleCurrentValuations_iff_current {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (x : Fin (m + 1) → ℝ) :
    x ∈ gentleCurrentValuations F θ ↔
      ∃ (v : F.carrier → EReal) (hv : IsThetaPshPotential θ.val v),
        HasSourceGentleAnalyticSingularities F v ∧
          x = fun i => ((currentFlagValuation F (thetaPotentialCurrent θ.val v hv)
            (thetaPotentialCurrent_closed_type_positive θ.val v hv).1
            (thetaPotentialCurrent_closed_type_positive θ.val v hv).2.1
            (thetaPotentialCurrent_closed_type_positive θ.val v hv).2.2 i : ℝ≥0) : ℝ) := by
  have key : ∀ (v : F.carrier → EReal) (hv : IsThetaPshPotential θ.val v),
      currentFlagValuation F (thetaPotentialCurrent θ.val v hv)
        (thetaPotentialCurrent_closed_type_positive θ.val v hv).1
        (thetaPotentialCurrent_closed_type_positive θ.val v hv).2.1
        (thetaPotentialCurrent_closed_type_positive θ.val v hv).2.2 =
      potentialFlagValuation F hv := fun v hv =>
    currentFlagValuation_eq_potentialFlagValuation F _ _ _ _ hv rfl
  constructor
  · rintro ⟨v, hv, hg, rfl⟩
    exact ⟨v, hv, hg, by rw [key v hv]⟩
  · rintro ⟨v, hv, hg, rfl⟩
    exact ⟨v, hv, hg, by rw [key v hv]⟩

section ClosureExpectation

open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.DiagonalMass

variable (F)

/-- The valuations `ν_{Y•}(S)` of the currents `S = θ + dd^c v ∈ 𝒵₊(X, {θ})` that are more
singular than `T = θ + dd^c u` in the multiplier-ideal sense (`S ⪯_𝓘 T`, i.e.
`𝓘(cv) ⊆ 𝓘(cu)` for all `c > 0`): the set whose closure is the partial Okounkov body in source
`thm:Deltapartialint`. -/
def iMoreSingularValuations (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal) :
    Set (Fin n → ℝ) :=
  {x | ∃ (v : F.carrier → EReal) (hv : IsThetaPshPotential θ.val v),
    IOrderOnManifold (n := n) v u ∧ x = fun i => ((potentialFlagValuation F hv i : ℝ≥0) : ℝ)}

/-- Source `rmk:Okounkov:L1841` (an expectation, stated as a proposition, not proved): for every
current `T = θ + dd^c u` of positive non-pluripolar mass (`T ∈ 𝒵₊(X, α)_{>0}`, so `α = {θ}` is
big), the set of valuations `ν_{Y•}(S)` of the currents `S ∈ 𝒵₊(X, α)` with `S ⪯_𝓘 T` is closed,
so that the closure in source `thm:Deltapartialint` is unnecessary. -/
def valuativeClosureUnnecessaryStatement : Prop :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  ∀ (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u), HasPositivePotentialMass θ u hu →
      IsClosed (iMoreSingularValuations F θ u)

end ClosureExpectation

end SGPT.Okounkov
