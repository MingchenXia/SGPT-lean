import SGPT.NAPotential.OriginalProductGraphData
import SGPT.NAPotential.DivDict2Unconditional

/-! The actual algebraic-prime dictionary and its original source consequences.

The product graph data are constructed from the original divisor. No graph
data, analytic realization, or desired comparison statement is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.NAPotential.AlgebraicPrimeDictionary

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJPrep
open SGPT.NAPotential.Berkovich.PiecewiseLinearData

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance pointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- Every original algebraic prime is actually realized analytically. -/
theorem algebraicPrimesRealized (E : ClosedProjectiveEmbedding f) :
    AlgebraicPrimesRealized (f := f) m E :=
  AlgPrimes3.algebraicPrimesRealized_of_highCodimProductGraphData
    (E := E) (OriginalProductGraphData.highCodimProductGraphData (m := m) E)

/-- The original divisorial potential formula, with the analytic presentation
produced from the original algebraic divisor. -/
theorem exists_potentialAn_ordVal (E : ClosedProjectiveEmbedding f) (D : PrimeDivisorOver X)
    {φ : SchemeComplexPoint f → EReal} {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2}
    (hφ : IsThetaPshPotential θ φ) (t : ℝ) (ht : 0 < t) :
    ∃ p : PrimePresentation (m + 1) (SchemeComplexPoint f), D.IsRealizedBy m E p ∧
      potentialAn (m + 1) E φ (D.ordVal f t ht) =
        -((t : EReal) * ((presentationReader φ p : ℝ≥0∞) : EReal)) := by
  obtain ⟨p, hp⟩ := algebraicPrimesRealized (m := m) E D
  exact ⟨p, hp, DivDict2.potentialAn_ordVal hp hφ t ht⟩

section Potentials

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

/-- The actual piecewise-linear curve and its original hull agree at every
original divisorial valuation, including the trivial valuation. -/
theorem curveAn_eq_naPotentialAnAt_hull (E : ClosedProjectiveEmbedding f)
    (D : PiecewiseLinearData θ) (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (v : sourceDivisorialSet f) :
    D.curveAn (m + 1) E v = naPotentialAnAt (m + 1) E (hullNAPotential D) ω v :=
  DivDict2.curveAn_eq_naPotentialAnAt_hull (algebraicPrimesRealized (m := m) E) D ω v

/-- Decreasing infima commute with analytification on the entire original
divisorial set for arbitrary backgrounds. -/
theorem naPotentialAnDiv_decreasingInf (E : ClosedProjectiveEmbedding f)
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    naPotentialAnDiv (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω v =
      ⨅ i, naPotentialAnDiv (m + 1) E (Γ i) ω v :=
  DivDict2.naPotentialAnDiv_decreasingInf (algebraicPrimesRealized (m := m) E)
    omega Γ ha hb ω v

end Potentials
end SGPT.NAPotential.AlgebraicPrimeDictionary
