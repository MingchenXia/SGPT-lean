import SGPT.NAPotential.AnTransIndependence
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations
import SGPT.PSH.SourceNAOrder

/-! Original intrinsic-order invariance, with no representative-change import.
The proof is the original AnTransBimero argument in a separate narrow consumer namespace.
Blueprint: source-dxz-porder-narrow.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ.SourceDXZPOrder

open SGPT.NAPotential.Berkovich

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance anTransBimeroPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance anTransBimeroPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance anTransBimeroPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

omit [BorelSpace (SchemeComplexPoint f)] in
/-- Globally `P`-equivalent quasi-psh potentials have the same analytification. -/
theorem potentialAn_eq_of_sourcePEquivalent {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : (ofFixedModel k (SchemeComplexPoint f)).IsQPSH φ)
    (hψ : (ofFixedModel k (SchemeComplexPoint f)).IsQPSH ψ)
    (h1 : SGPT.PSH.GlobalPComparison.sourcePOrder (n := k) φ ψ)
    (h2 : SGPT.PSH.GlobalPComparison.sourcePOrder (n := k) ψ φ) :
    potentialAn k E φ = potentialAn k E ψ :=
  potentialAn_eq_of_sourceIEquivalent k E
    ⟨sourceIOrder_of_sourcePOrder hφ hψ h1, sourceIOrder_of_sourcePOrder hψ hφ h2⟩

omit [BorelSpace (SchemeComplexPoint f)] in
/-- Intrinsically equivalent test curves have the same analytification slice by slice. -/
theorem potentialAn_eq_of_curvePOrder_equivalent {G : SourceTestCurve θ} {H : SourceTestCurve σ}
    (h1 : SourceTestCurvePOrder G H) (h2 : SourceTestCurvePOrder H G) (r : ℝ) (hr : r < G.max)
    (hs : r < H.max) :
    potentialAn k E (G.potential ⟨r, hr⟩) = potentialAn k E (H.potential ⟨r, hs⟩) :=
  potentialAn_eq_of_sourcePEquivalent k E ⟨θ, G.thetaPSH ⟨r, hr⟩⟩ ⟨σ, H.thetaPSH ⟨r, hs⟩⟩
    (h1.slice_le r hr) (h2.slice_le r hs)

/-- Intrinsically equivalent non-Archimedean metrics (each below the other in the order of
`def:NApotential:L274`, possibly in different classes) have the same analytification `Γ^An`
on `X^An`. -/
theorem naPotentialAnAt_eq_of_POrder_equivalent {Γ : SourceNAPotential θ}
    {Δ : SourceNAPotential σ} (h1 : SourceNAPOrder Γ Δ) (h2 : SourceNAPOrder Δ Γ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt k E Γ ω v = naPotentialAnAt k E Δ ω v := by
  have c1 := (sourceNAPOrder_iff_component Γ Δ ω).mp h1
  have c2 := (sourceNAPOrder_iff_component Δ Γ ω).mp h2
  unfold naPotentialAnAt
  apply le_antisymm
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hs : r < (Δ.component ω).val.max := lt_of_lt_of_le hr c1.cutoff_le
    rw [potentialAn_eq_of_curvePOrder_equivalent k E c1 c2 r hr hs]
    exact le_iSup (fun τ : Iio (Δ.component ω).val.max =>
      potentialAn k E ((Δ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)) ⟨r, hs⟩
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hs : r < (Γ.component ω).val.max := lt_of_lt_of_le hr c2.cutoff_le
    rw [potentialAn_eq_of_curvePOrder_equivalent k E c2 c1 r hr hs]
    exact le_iSup (fun τ : Iio (Γ.component ω).val.max =>
      potentialAn k E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)) ⟨r, hs⟩

end SGPT.NAPotential.BJ.SourceDXZPOrder

end
