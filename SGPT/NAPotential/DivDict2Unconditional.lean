import SGPT.NAPotential.DivDictPLCurve
import SGPT.GAGA.H0SSchemeGAGA

/-! # The divisorial dictionary without the GAGA hypothesis

Source `chapter_NApotential.tex`, Section *The analytifications* and *The comparison theorem*:
the sentence after `def:NApotential:L975` (`φ^An(t ord_E) = -t ν(φ, E)`), `eq:Gammamax`,
`lma:anaorder`, `prop:anpreinf`, `lma:psieqpsiprimeondiv` and the injectivity part of `thm:DXZ`.
Blueprint `claude-div-dict2:unconditional`.

Lane DIV-DICT proved these statements conditionally on `MultiplierIdealAlgebraic` (GAGA for
multiplier ideals).  Lane H0-GAGA2 proved `MultiplierIdealAlgebraic` for every smooth projective
complex scheme with a closed projective embedding (`SGPT.GAGA.H0S.multiplierIdealAlgebraic`).
This file restates the results with that hypothesis discharged; the only remaining hypotheses are
the genuine ones of the source (and, where the whole of `X^Div` is concerned, the relevant half of
the dictionary between algebraic and analytic prime divisors, `AnalyticPrimesRealized` or
`AlgebraicPrimesRealized`, which are statements and are never assumed globally).

## Main results

* `potentialAn_ordVal`: `φ^An(t ord_D) = -t ν(φ, p)` for `D` realized by `p`.
* `potentialAn_trivial`, `naPotentialAnAt_trivial`: `φ^An(v_triv) = 0`, `Γ^An(v_triv) = Γ_max`.
* `naPotentialAnAt_mono`: `Γ ↦ Γ^An` is order preserving on `X^An` (`lma:anaorder`).
* `naPotentialAnAt_ordVal`: `Γ^An(t ord_D) = sup_{τ < Γ_max} (τ - t ν(Γ_τ, p))`.
* `sourceNAPOrder_iff_naPotentialAnDiv_le`, `naPotentialAnDiv_injective`,
  `naPotentialAnAt_injective`: order reflection and injectivity (`lma:anaorder`, `thm:DXZ`), under
  `AnalyticPrimesRealized`.
* `naPotentialAnAt_ordVal_decreasingInf`, `naPotentialAnDiv_decreasingInf`: `prop:anpreinf` at
  realized divisorial points, and on `X^Div` under `AlgebraicPrimesRealized`.
* `curveAn_le_naPotentialAnAt_hull`, `curveAn_eq_naPotentialAnAt_hull`:
  `lma:psieqpsiprimeondiv` (`eq:psieqsiprime`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.DivDict2

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder
open SGPT.NAPotential.BJPrep SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData

/-! ### Potentials: the identity on divisorial valuations and the trivial valuation -/

section Potential

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance divDict2PointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDict2PointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDict2PointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **`alg(𝓘(cφ))^an = 𝓘(cφ)`** for every quasi-psh `φ` on `X(ℂ)` and `c > 0`: multiplier ideals
are analytifications of algebraic ideal sheaves. -/
theorem analytificationIdeal_algebraization_multiplierIdeal {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) {c : ℝ} (hc : 0 < c) :
    analytificationIdeal f (m + 1) E (algebraization f (m + 1) E
        (multiplierIdeal (n := m + 1) c φ)) = multiplierIdeal (n := m + 1) c φ :=
  analytificationIdeal_algebraization_eq f (m + 1) E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ hc

/-- For a realized pair `(D, p)`, the order along `D` of the algebraic model of `𝓘(cφ)` is the
order of `𝓘(cφ)` along the hypersurface of `p`. -/
theorem ordIdeal_algebraization_multiplierIdeal {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ)
    {c : ℝ} (hc : 0 < c) :
    D.ordIdeal f (algebraization f (m + 1) E (multiplierIdeal (n := m + 1) c φ)) =
      (presentationMultiplierOrder hφ hc p : ℝ≥0∞) :=
  hDp.ordIdeal_algebraization_multiplierIdeal
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ hc

/-- **`v(φ) = t ν(φ, E)` for `v = t ord_E`** (the sentence after `eq:varphiAnalt`), for a prime
divisor `D` over `X` realized by the analytic presentation `p`. -/
theorem potentialVal_ordVal {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) (t : ℝ) (ht : 0 < t) :
    (D.ordVal f t ht).potentialVal (m + 1) E φ = ENNReal.ofReal t * presentationReader φ p :=
  BerkovichPoint.potentialVal_ordVal (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hDp hφ
    t ht

/-- **Source, after `def:NApotential:L975`: `φ^An(t ord_E) = -t ν(φ, E)`**, for `φ ∈ PSH(X, θ)`,
`t > 0` and a prime divisor `D` over `X` realized by the analytic presentation `p`. -/
theorem potentialAn_ordVal {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) =
      -((t : EReal) * ((presentationReader φ p : ℝ≥0∞) : EReal)) :=
  Berkovich.potentialAn_ordVal (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hDp hφ t ht

/-- The value `φ^An(t ord_D) = -t ν(φ, p)` is a real number. -/
theorem potentialAn_ordVal_eq_coe {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) (hfin : presentationReader φ p ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) =
      ((-(t * (presentationReader φ p).toReal) : ℝ) : EReal) :=
  Berkovich.potentialAn_ordVal_eq_coe (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hDp hφ
    hfin t ht

/-- Two realized pairs with the same generic Lelong number of `φ` give the same value of
`φ^An`. -/
theorem potentialAn_ordVal_eq_of_realized {D D' : PrimeDivisorOver X}
    {p p' : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) (hDp' : D'.IsRealizedBy m E p')
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) (hν : presentationReader φ p = presentationReader φ p')
    (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (D.ordVal f t ht) = potentialAn (m + 1) E φ (D'.ordVal f t ht) :=
  Berkovich.potentialAn_ordVal_eq_of_realized (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1))
    hDp hDp' hφ hν t ht

/-- The algebraic model of the multiplier ideal `𝓘(cφ)` of a quasi-psh function on the nonempty
`X(ℂ)` is not the zero ideal sheaf. -/
theorem algebraization_multiplierIdeal_ne_bot [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal} (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ)
    {c : ℝ} (hc : 0 < c) :
    algebraization f (m + 1) E (multiplierIdeal (n := m + 1) c φ) ≠ ⊥ :=
  Berkovich.algebraization_multiplierIdeal_ne_bot
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ hc

/-- **`φ^An(v_triv) = 0`** for `φ ∈ PSH(X, θ)`. -/
theorem potentialAn_trivial [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) :
    potentialAn (m + 1) E φ (BerkovichPoint.trivial f) = 0 :=
  Berkovich.potentialAn_trivial (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ

end Potential

/-! ### Non-Archimedean potentials -/

section NA

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance divDict2NAPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDict2NAPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDict2NAPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

/-- **Order preservation** (first sentence of `lma:anaorder`): `Γ ≤ Γ'` implies
`Γ^An(v) ≤ Γ'^An(v)` for every `v ∈ X^An`. -/
theorem naPotentialAnAt_mono {Γ Γ' : SourceNAPotential θ} (h : SourceNAPOrder Γ Γ')
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v :=
  Berkovich.naPotentialAnAt_mono (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) h ω v

/-- **Source `eq:Gammamax`: `Γ^An(v_triv) = Γ_max`.** -/
theorem naPotentialAnAt_trivial [IsIntegral X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    naPotentialAnAt (m + 1) E Γ ω (BerkovichPoint.trivial f) =
      (((Γ.component ω).val.max : ℝ) : EReal) :=
  Berkovich.naPotentialAnAt_trivial (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) Γ ω

/-- **`Γ^An` at a divisorial valuation**: for a prime divisor `D` over `X` realized by the
analytic presentation `p`, `Γ^An(t ord_D) = sup_{τ < Γ_max} (τ - t ν(Γ_τ^{θ+ω}, p))`. -/
theorem naPotentialAnAt_ordVal {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    (Γ : SourceNAPotential θ) (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (t : ℝ)
    (ht : 0 < t) :
    naPotentialAnAt (m + 1) E Γ ω (D.ordVal f t ht) = naDivisorialTransform Γ ω p t :=
  Berkovich.naPotentialAnAt_ordVal (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hDp Γ ω
    t ht

section Infimum

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **`prop:anpreinf` at a realized divisorial point**: for a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` satisfying `eq:decnetcontition`, `(inf_i Γ_i)^An(t ord_D) = inf_i Γ_i^An(t ord_D)`. -/
theorem naPotentialAnAt_ordVal_decreasingInf {D : PrimeDivisorOver X}
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hDp : D.IsRealizedBy m E p)
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (t : ℝ) (ht : 0 < t) :
    naPotentialAnAt (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω
        (D.ordVal f t ht) =
      ⨅ i, naPotentialAnAt (m + 1) E (Γ i) ω (D.ordVal f t ht) :=
  Berkovich.naPotentialAnAt_ordVal_decreasingInf
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hDp omega Γ ha hb ω t ht

end Infimum

variable [IsIntegral X]

/-- **Order reflection on `X^Div`** (`lma:anaorder`), under the analytic half of the dictionary:
if `Γ^An ≤ Γ'^An` on `X^Div`, then `Γ ≤ Γ'`. -/
theorem sourceNAPOrder_of_naPotentialAnDiv_le (han : AnalyticPrimesRealized (f := f) m E)
    {Γ Γ' : SourceNAPotential θ} (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (h : ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v) :
    SourceNAPOrder Γ Γ' :=
  Berkovich.sourceNAPOrder_of_naPotentialAnDiv_le
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) han ω h

/-- **`lma:anaorder` on `X^Div`**: `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^Div`, under the analytic half
of the dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnDiv_le (han : AnalyticPrimesRealized (f := f) m E)
    {Γ Γ' : SourceNAPotential θ} (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v :=
  Berkovich.sourceNAPOrder_iff_naPotentialAnDiv_le
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) han ω

/-- **Injectivity of `Γ ↦ Γ^An` on `X^Div`** (`lma:anaorder`, `thm:DXZ`), under the analytic half
of the dictionary. -/
theorem naPotentialAnDiv_injective (han : AnalyticPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnDiv (m + 1) E Γ ω :=
  Berkovich.naPotentialAnDiv_injective (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) han ω

/-- **`lma:anaorder` for functions on `X^An`**, under the analytic half of the dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le (han : AnalyticPrimesRealized (f := f) m E)
    {Γ Γ' : SourceNAPotential θ} (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v :=
  Berkovich.sourceNAPOrder_iff_naPotentialAnAt_le
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) han ω

/-- **Injectivity of `Γ ↦ Γ^An` as functions on `X^An`** (`lma:anaorder`, `thm:DXZ`), under the
analytic half of the dictionary. -/
theorem naPotentialAnAt_injective (han : AnalyticPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt (m + 1) E Γ ω :=
  Berkovich.naPotentialAnAt_injective (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) han ω

/-- **`prop:anpreinf` on `X^Div`**: `(inf_i Γ_i)^An = inf_i Γ_i^An` on `X^Div`, under the
algebraic half of the dictionary of prime divisors. -/
theorem naPotentialAnDiv_decreasingInf {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (halg : AlgebraicPrimesRealized (f := f) m E)
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    naPotentialAnDiv (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω v =
      ⨅ i, naPotentialAnDiv (m + 1) E (Γ i) ω v :=
  Berkovich.naPotentialAnDiv_decreasingInf (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1))
    halg omega Γ ha hb ω v

omit [IsIntegral X] in
/-- **`A^An ≤ Ã^An` on `X^An`** for a piecewise linear curve `A` and its `𝓘`-projected
regularized concave envelope `Ã` (`lma:psieqpsiprimeondiv`). -/
theorem curveAn_le_naPotentialAnAt_hull (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    D.curveAn (m + 1) E v ≤ naPotentialAnAt (m + 1) E (hullNAPotential D) ω v :=
  Berkovich.curveAn_le_naPotentialAnAt_hull (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1))
    D ω v

/-- **Source `lma:psieqpsiprimeondiv`, `eq:psieqsiprime`: `A^An = Ã^An` on `X^Div`**, under the
algebraic half of the dictionary of prime divisors. -/
theorem curveAn_eq_naPotentialAnAt_hull (halg : AlgebraicPrimesRealized (f := f) m E)
    (D : PiecewiseLinearData θ) (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (v : sourceDivisorialSet f) :
    D.curveAn (m + 1) E v = naPotentialAnAt (m + 1) E (hullNAPotential D) ω v :=
  Berkovich.curveAn_eq_naPotentialAnAt_hull (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1))
    halg D ω v

end NA

end SGPT.NAPotential.DivDict2

end
