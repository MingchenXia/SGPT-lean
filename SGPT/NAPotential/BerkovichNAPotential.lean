import SGPT.NAPotential.BerkovichAnalytification
import SGPT.NAPotential.BerkovichDivisorial
import SGPT.PSH.SourceNonArchimedeanPotentials

/-! # The analytification `Γ^An` of a non-Archimedean potential

Source `def:Gammaana` (`chapter_NApotential.tex`, Section *The transcendental setting*): for
`Γ ∈ PSH^NA(X, θ)` and `ω ∈ Kah(X)`,

`Γ^An(v) := sup_{τ ≤ Γ_max} (Γ^{θ+ω, An}_τ(v) + τ)`,   `v ∈ X^Div`,

*clearly independent of the choice of `ω`*.

## Formal setting

`X(ℂ) = SchemeComplexPoint f` for a scheme `X` smooth of relative dimension `k` over `ℂ` with a
closed projective embedding `E`, with its complex-manifold structure; `PSH^NA(X, θ)` is the
existing `SGPT.PSH.VariableComplexAtlas.SourceNAPotential θ` on `X(ℂ)` (which needs a Borel
measurable structure, compactness and connectedness of `X(ℂ)`, taken as instance hypotheses),
`φ^An` is `SGPT.NAPotential.Berkovich.potentialAn` and `X^Div` is `divisorialSet f`.
The workspace's test curves record the slices `Γ_τ` for `τ < Γ_max` only, so the supremum runs
over `τ < Γ_max` (the book itself notes, in the proof of `prop:anpreinf`, that the endpoint
`τ = Γ_max` does not change the supremum on `X^Div`).

## Main definitions

* `naPotentialAnAt Γ ω v`: the right-hand side of `eq:psiandef` at the Kähler index `ω`, for
  every `v ∈ X^An`.
* `naPotentialAn Γ ω : X^Div → [-∞, ∞)`: its restriction to `X^Div` (source `def:Gammaana`).
* `naPotentialAnAt_cutoff`: the cutoff `Γ_max` entering the formula does not depend on `ω`.

The independence of the whole formula from `ω` is not formalized: it needs that the
`𝓘`-projections relating the components preserve the multiplier ideals `𝓘(kφ)` of
`SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.multiplierIdeal` (the existing
`𝓘`-order `SGPT.PSH.VariableComplexAtlas.sourceIOrder` is formulated chartwise and the bridge to
these germ ideals is missing).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance berkovichNAPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance berkovichNAPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance berkovichNAPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

/-- `sup_{τ < Γ_max} (Γ^{θ+ω, An}_τ(v) + τ)` at the Kähler index `ω`, for `v ∈ X^An`. -/
def naPotentialAnAt (Γ : SourceNAPotential θ) (ω : SourceKahlerForm k (SchemeComplexPoint f))
    (v : BerkovichPoint f) : EReal :=
  ⨆ τ : Iio (Γ.component ω).val.max,
    potentialAn k E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)

/-- Source `def:Gammaana`: `Γ^An : X^Div → [-∞, ∞)`, computed at the Kähler index `ω`. -/
def naPotentialAn (Γ : SourceNAPotential θ) (ω : SourceKahlerForm k (SchemeComplexPoint f)) :
    divisorialSet f → EReal :=
  fun v => naPotentialAnAt k E Γ ω v.1

/-- The cutoff `Γ_max` in `eq:psiandef` is the same for every Kähler index. -/
theorem naPotentialAnAt_cutoff (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm k (SchemeComplexPoint f)) :
    (Γ.component ω).val.max = (Γ.component η).val.max :=
  Γ.component_max_eq ω η

/-- Every slice contributes: `Γ^{θ+ω, An}_τ(v) + τ ≤ Γ^An(v)` for `τ < Γ_max`. -/
theorem le_naPotentialAnAt (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f)
    (τ : Iio (Γ.component ω).val.max) :
    potentialAn k E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal) ≤
      naPotentialAnAt k E Γ ω v :=
  le_iSup (fun τ : Iio (Γ.component ω).val.max =>
    potentialAn k E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)) τ

end SGPT.NAPotential.Berkovich

end
