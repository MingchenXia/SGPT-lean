import SGPT.NAPotential.AlgebraicPrimeDictionaryMain
import SGPT.Checks.Comparison.SourceNet
import SGPT.Checks.Comparison.SourceInfDimZero

/-! Unconditional full-analytification comparison in the book's rational background.

The original line bundle, metric, positive denominator and Chern-class
compatibility are retained. The algebraic-prime dictionary is proved.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

namespace SGPT.NAPotential.AlgebraicPrimeComparison

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]

local instance proper : IsProper f :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective f).isProper

variable (n : ℕ) [SmoothOfRelativeDimension n f]

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance pointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {q : ℕ}
  (hq : 0 < q) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((q : ℝ)⁻¹) • HM.curvature b).val)

include hq hθ in
/-- The source decreasing-infimum identity on all Berkovich points, in every
dimension and the original rational Chern background. -/
theorem naPotentialAnAt_decreasingInf {I : Type u} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (omega : KahlerBackground n (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    naPotentialAnAt n E (SourceNAPotential.decreasingInf omega Γ ha hb) ω =
      fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v := by
  cases n with
  | zero => exact BJ.SourceInfDimZero.naPotentialAnAt_decreasingInf_of_dim_zero E omega Γ ha hb ω
  | succ k =>
    exact BJ.SourceNet.naPotentialAnAt_decreasingInf f k E b HM hq hθ
      (AlgebraicPrimeDictionary.algebraicPrimesRealized (m := k) E) omega Γ ha hb ω

end SGPT.NAPotential.AlgebraicPrimeComparison
