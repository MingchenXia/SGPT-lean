import SGPT.Checks.Comparison.ThinApprox.SourceDivUnique
import SGPT.Checks.Comparison.SourceInfPsh
import SGPT.Checks.Comparison.SourceAnalytificationMap
import SGPT.NAPotential.DivDict2Unconditional

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-! Full analytification equality from actual original divisorial uniqueness.
Blueprint: source-comparison-slices.tex. -/
run_cmd Lean.logInfo "SOURCE_NET_SPLIT: imports-ready"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
open SGPT.NAPotential.BJ.SourceNet

open SGPT.NAPotential.BJ.Exist SGPT.NAPotential.BJ.SourceDivUnique SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.DivDict2
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

section Anpreinf

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existAnpProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existAnpPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existAnpPointCharts :
    ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance existAnpPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)


run_cmd Lean.logInfo "SOURCE_NET_SPLIT: theorem-signature-next"

include hm hθ in
/-- **`prop:anpreinf` on `X^An`**: for a decreasing net `(Γ_i)` in `PSH^NA(X, θ)` satisfying
`eq:decnetcontition`, `(inf_i Γ_i)^An = inf_i Γ_i^An` at every point of `X^An`, under the algebraic
half of the dictionary of prime divisors (`AlgebraicPrimesRealized`, as for the existing `X^Div`
statement). Both sides lie in `PSH(L^An)` and agree on `X^Div`. -/
theorem naPotentialAnAt_decreasingInf (halg : AlgebraicPrimesRealized (f := f) k E) {I : Type u}
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground (k + 1) (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    naPotentialAnAt (k + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω =
      fun v => ⨅ i, naPotentialAnAt (k + 1) E (Γ i) ω v :=
  eq_of_eqOn_sourceDivisorialSet f
    (naPotentialAnAt_isModuleTopologyPSH.{0} f (k + 1) E b HM hm hθ
      (SourceNAPotential.decreasingInf omega Γ ha hb) ω)
    (SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.shrink f
      (iInf_naPotentialAnAt_isModuleTopologyPSH.{u} f (k + 1) E b HM hm hθ
        omega Γ ha hb ω))
    (fun v hv => naPotentialAnDiv_decreasingInf halg omega Γ ha hb ω ⟨v, hv⟩)

run_cmd Lean.logInfo "SOURCE_NET_SPLIT: theorem-checked"

end Anpreinf


end SGPT.NAPotential.ThinApprox.BJ.SourceNet
