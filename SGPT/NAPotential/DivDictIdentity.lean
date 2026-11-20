import SGPT.NAPotential.DivDictValuation
import SGPT.NAPotential.GAGAMult2Limit
import SGPT.PSH.CompactPrimeMultiplierLimit

/-! # `φ^An(t ord_E) = -t ν(φ, E)` on divisorial valuations

Source: `chapter_NApotential.tex`, the sentence after `def:NApotential:L975` (`eq:varphiAnalt`):
*when `v = t ord_E` for some prime divisor `E` over `X`, `φ^An(v) = -t ν(φ, E)` by
`prop:Lelongnumfrommis`.*  Blueprint `claude-div-dict:realization`, `claude-div-dict:identity`.

## The dictionary

In the book a prime divisor `E` over the projective manifold `X` is at the same time

* an algebraic object: a prime divisor on a normal model `Y → X`, which gives the divisorial
  valuation `ord_E` of `ℂ(X)` and the values `ord_E(𝔞)` on coherent ideal sheaves (`eq:va`);
  in the workspace this is `SGPT.NAPotential.Berkovich.PrimeDivisorOver X` with
  `PrimeDivisorOver.ordVal` and `PrimeDivisorOver.ordIdeal`;
* an analytic object: a smooth connected hypersurface in a modification of `X(ℂ)`, along which
  generic Lelong numbers `ν(φ, E)` are taken (`def:pshfunctions:L1112`); in the workspace this is
  `SGPT.PSH.CompactPrimeOver.PrimePresentation` with `presentationReader`.

The two are linked by the valuation they induce on ideal sheaves:
`PrimeDivisorOver.IsRealizedBy D p` says that for every (quasi-coherent) ideal sheaf `𝔞` of `X`
the algebraic value `ord_D(𝔞)` equals the analytic order of vanishing along the hypersurface of
`p` of the pulled back analytic ideal `𝔞^an 𝒪` (the order `originalStalkNormalOrder` of
`SGPT.Foundations.Analysis`, read at every point of the hypersurface).  This is the precise form of
"`ord_E(𝔞)` can be computed analytically at a point of `E`".

## Main results

* `BerkovichPoint.potentialVal_ordVal`, `potentialAn_ordVal`: if `D` is realized by `p`, then for
  every `φ ∈ PSH(X, θ)` and `t > 0`, `φ^An(t ord_D) = -t ν(φ, p)`, conditionally on the
  algebraicity of multiplier ideals `MultiplierIdealAlgebraic` (GAGA; it gives the existence of
  the limit in `def:NApotential:L975` and `alg(𝓘(kφ))^an = 𝓘(kφ)`).  The proof is the book's:
  `(t ord_D)(𝓘(kφ)) = t ord_D(𝓘(kφ))` and the valuative formula `prop:Lelongnumfrommis`
  (`tendsto_presentationMultiplierOrder_ratio`).
* `potentialAn_ordVal_eq_of_realized`: two realized pairs with the same generic Lelong numbers
  have the same analytification value.

The existence of realizations (an analytic presentation for a given algebraic prime divisor:
resolution of singularities and analytification of normal models; an algebraic prime divisor
for a given analytic presentation: algebraicity of modifications of a projective manifold) is
not part of this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder MultiplierIdealLowerBound
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder
  SGPT.PSH.CompactPrimeMultiplierLimit

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (m : ℕ) [SmoothOfRelativeDimension (m + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance divDictPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDictPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDictPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The smooth connected hypersurface of a presentation, in dimension `m + 1`. -/
theorem primePresentation_smooth_hypersurface {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (p : PrimePresentation (m + 1) M) : IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
  have hdim : p.divisorDimension = m := by
    have h := p.codimension_one
    omega
  simpa only [hdim] using p.smooth

/-- **The dictionary between algebraic and analytic prime divisors over `X`.**  The algebraic
prime divisor `D` over the scheme `X` is *realized* by the analytic presentation `p` (a
modification of `X(ℂ)` with a smooth connected hypersurface) if they induce the same valuation
on ideal sheaves: for every ideal sheaf `𝔞` of `X`, the value `ord_D(𝔞)` (`eq:va`) is the order
of vanishing along the hypersurface of `p`, at each of its points, of the pull-back of the
analytification `𝔞^an`. -/
def PrimeDivisorOver.IsRealizedBy (D : PrimeDivisorOver X)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) : Prop :=
  ∀ (𝔞 : X.IdealSheafData) (y : p.model) (_ : y ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor y),
    ((originalStalkNormalOrder Φ (GermIdeal.pullback (m := m + 1) p.projection
      (analytificationIdeal f (m + 1) E 𝔞)) : ℕ∞) : ℝ≥0∞) = D.ordIdeal f 𝔞

variable {m E}

/-- For a realized pair, the algebraic order of the algebraic model of the multiplier ideal
`𝓘(cφ)` along `D` is the analytic order of `𝓘(cφ)` along the hypersurface of `p`
(under `MultiplierIdealAlgebraic`). -/
theorem PrimeDivisorOver.IsRealizedBy.ordIdeal_algebraization_multiplierIdeal
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ)
    {c : ℝ} (hc : 0 < c) :
    D.ordIdeal f (algebraization f (m + 1) E (multiplierIdeal (n := m + 1) c φ)) =
      (presentationMultiplierOrder hφ hc p : ℝ≥0∞) := by
  have hE := primePresentation_smooth_hypersurface m p
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  rw [← hDp _ y hy Φ, analytificationIdeal_algebraization_eq f (m + 1) E hA hφ hc,
    originalStalkNormalOrder_eq_actualMultiplierCoefficient p.modification hE hφ hc y hy Φ]
  rfl

namespace BerkovichPoint

/-- **`v(φ) = t ν(φ, E)` for `v = t ord_E`** (the sentence after `eq:varphiAnalt`), for a prime
divisor `D` over `X` realized by the analytic presentation `p`, conditionally on
`MultiplierIdealAlgebraic`. -/
theorem potentialVal_ordVal (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (t : ℝ) (ht : 0 < t) :
    (D.ordVal f t ht).potentialVal (m + 1) E φ = ENNReal.ofReal t * presentationReader φ p := by
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  have h1 := tendsto_potentialVal_of_multiplierIdealAlgebraic (m + 1) E hA hφ (D.ordVal f t ht)
  have h1' := (tendsto_add_atTop_iff_nat 1).mpr h1
  have h2 := tendsto_presentationMultiplierOrder_ratio hq p
  have h3 : Tendsto (fun k : ℕ => ENNReal.ofReal t *
      ((presentationMultiplierOrder hq (show (0 : ℝ) < (k + 1 : ℕ) by positivity) p : ℝ≥0∞) /
        (k + 1 : ℕ))) atTop (𝓝 (ENNReal.ofReal t * presentationReader φ p)) :=
    ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_nhds_unique h1' (h3.congr fun k => ?_)
  unfold multiplierIdealVal
  rw [D.idealVal_ordVal t ht,
    hDp.ordIdeal_algebraization_multiplierIdeal hA hq (show (0 : ℝ) < (k + 1 : ℕ) by positivity),
    mul_div_assoc]

end BerkovichPoint

/-- **Source, after `def:NApotential:L975`: `φ^An(t ord_E) = -t ν(φ, E)`**, for a prime divisor
`D` over `X` realized by the analytic presentation `p` and `φ ∈ PSH(X, θ)`, conditionally on
`MultiplierIdealAlgebraic`. -/
theorem potentialAn_ordVal (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) =
      -((t : EReal) * ((presentationReader φ p : ℝ≥0∞) : EReal)) := by
  unfold potentialAn
  rw [BerkovichPoint.potentialVal_ordVal hA hDp hφ t ht, EReal.coe_ennreal_mul,
    EReal.coe_ennreal_ofReal, max_eq_left ht.le]

/-- The value `φ^An(t ord_D)` is real (not `-∞`) on a compact `X(ℂ)`: generic Lelong numbers are
finite. -/
theorem potentialAn_ordVal_eq_coe (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (hfin : presentationReader φ p ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) =
      ((-(t * (presentationReader φ p).toReal) : ℝ) : EReal) := by
  rw [potentialAn_ordVal hA hDp hφ t ht, ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_mul,
    ← EReal.coe_neg]

/-- Independence of the realization: two prime divisors over `X` realized by presentations with
the same generic Lelong number of `φ` give the same value of `φ^An`. -/
theorem potentialAn_ordVal_eq_of_realized (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D D' : PrimeDivisorOver X} {p p' : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) (hDp' : D'.IsRealizedBy m E p')
    {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (hν : presentationReader φ p = presentationReader φ p') (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) = potentialAn (m + 1) E φ (D'.ordVal f t ht) := by
  rw [potentialAn_ordVal hA hDp hφ t ht, potentialAn_ordVal hA hDp' hφ t ht, hν]

end SGPT.NAPotential.Berkovich

end
