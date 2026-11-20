import SGPT.NAPotential.AnTransIndependence
import SGPT.NAPotential.PLCurveNAPotential

/-! # The analytification of the envelope metric `Ã` of a piecewise linear curve

Source `lma:psieqpsiprimeondiv` (`chapter_NApotential.tex`), proof of `eq:psieqsiprime`: for a
piecewise linear curve `A` in `PSH(X, θ)` with regularized concave envelope `A'`
(`rmk:pwlinhull`) and `Ã^{θ+ω}_τ = P_{θ+ω}[A'_τ]_𝓘`, the book uses that *`𝓘`-projection
preserves the valuations*, i.e. `Ã^An(v) = sup_{τ < τ_0} (A'_τ^An(v) + τ)`.  This is proved here
on all of `X^An` (`naPotentialAnAt_hullNAPotential`), from `potentialAn_sourceIEnvelope`.

The remaining step of `eq:psieqsiprime`, `sup_{τ < τ_0} (A'_τ^An(v) + τ) = max_i (A_i^An(v) + τ_i)`
for `v ∈ X^Div`, uses that analytification commutes with finite maxima and positive linear
combinations on divisorial valuations (`φ^An(t ord_E) = -t ν(φ, E)`, `prop:Lelongnumfrommis`).
For the workspace analytification `potentialAn` (defined through the algebraic models of the
multiplier ideals, `BerkovichAnalytification.lean`) this needs the existence of the limit
`lim_k k⁻¹ v(𝓘(kφ))`, i.e. GAGA for multiplier ideals; it is not formalized here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open PiecewiseLinearData SimplexRevision SimplexRevision.WholeHull

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance anTransPLPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance anTransPLPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance anTransPLPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

/-- The `𝓘`-projections in `Ã` do not change the analytification:
`Ã^An(v) = sup_{τ < τ_0} (A'_τ^An(v) + τ)` for every `v ∈ X^An` and every Kähler index, where
`A'_τ` is the regularized concave envelope of `rmk:pwlinhull`. -/
theorem naPotentialAnAt_hullNAPotential (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt k E (hullNAPotential D) ω v =
      ⨆ τ : Iio (D.τ 0), potentialAn k E (uscRegularization (D.pointwiseUpperConcaveEnvelope τ)) v +
        ((τ : ℝ) : EReal) := by
  unfold naPotentialAnAt
  apply iSup_congr
  intro τ
  rw [(source_pwlinhull_whole D).2.1 τ]
  change potentialAn k E (sourceIEnvelope (sourceNAComponentBackground θ ω) (simplexValue D τ)) v +
    _ = _
  rw [potentialAn_sourceIEnvelope k E (simplexValue_componentPSH D ω τ.2.le)]

end SGPT.NAPotential.Berkovich

end
