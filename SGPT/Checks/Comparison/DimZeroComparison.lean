import SGPT.Checks.Comparison.BJExistNet
import SGPT.NAPotential.DimZeroAnalytification

/-!
# `prop:anpreinf` and `lma:anaorder` for `X` of every dimension

Source: `chapter_NApotential.tex`, *The comparison theorem* (`X` a connected projective manifold
of any dimension `n`, `L = m⁻¹ [M]`, `θ = c₁(L, h)`). Blueprint `claude-dim-zero.tex`, nodes
`claude-dim-zero:anpreinf-all` and `claude-dim-zero:anaorder-all`.

* `naPotentialAnAt_decreasingInf_dim`: **`prop:anpreinf` on `X^An` for `X` of every relative
  dimension `n`**: for a decreasing net `(Γ_i)` in `PSH^NA(X, θ)` satisfying `eq:decnetcontition`,
  `(inf_i Γ_i)^An = inf_i Γ_i^An` on `X^An`. In dimension `0` this is unconditional
  (`DimZero.naPotentialAnAt_decreasingInf_of_dim_zero`); in dimension `k + 1` it is lane
  BJ-EXIST's `BJ.Exist.naPotentialAnAt_decreasingInf`, under the resolution-dependent hypothesis
  `AlgebraicPrimesRealized` (assumed only for `X` of positive relative dimension).
* `naAnalytification_le_iff_dim`, `naAnalytification_injective_dim`: **`lma:anaorder`** for the
  map `eq:analymap` `PSH^NA(X, θ) → PSH(L^An)` (`BJ.Exist.naAnalytification`) for `X` of every
  relative dimension, with no dictionary hypothesis: `Γ^An ≤ Γ'^An` iff `Γ ≤ Γ'`, and the map is
  injective (`DimZero.sourceNAPOrder_iff_naPotentialAnAt_le_dim`: dimension `0` from this lane,
  positive dimension from lane TOWER-ALG).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.DimZero

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance dimZeroCmpProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance dimZeroCmpPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroCmpPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dimZeroCmpPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`prop:anpreinf` on `X^An`, every dimension.** Let `X` be smooth projective of relative
dimension `n` over `ℂ` (integral, closed projective embedding, `X(ℂ)` connected), `L = m⁻¹ [M]`
with `θ = c₁(L, h)`. Assume the algebraic half of the dictionary of prime divisors
(`AlgebraicPrimesRealized`) whenever `X` has positive relative dimension `k + 1`. Then for every
decreasing net `(Γ_i)` in `PSH^NA(X, θ)` satisfying `eq:decnetcontition`,
`(inf_i Γ_i)^An = inf_i Γ_i^An` on `X^An`. -/
theorem naPotentialAnAt_decreasingInf_dim
    (halg : ∀ (k : ℕ) [SmoothOfRelativeDimension (k + 1) f], AlgebraicPrimesRealized (f := f) k E)
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    naPotentialAnAt n E (SourceNAPotential.decreasingInf omega Γ ha hb) ω =
      fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v := by
  cases n with
  | zero => exact naPotentialAnAt_decreasingInf_of_dim_zero E omega Γ ha hb ω
  | succ k => exact BJ.Exist.naPotentialAnAt_decreasingInf f k E b HM hm hθ (halg k) omega Γ ha hb ω

include hm hθ in
/-- **`lma:anaorder` for the map `eq:analymap`, every dimension, no dictionary hypothesis**:
`Γ^An ≤ Γ'^An` on `X^An` (as elements of `PSH(L^An)`) iff `Γ ≤ Γ'`. -/
theorem naAnalytification_le_iff_dim (ω : SourceKahlerForm n (SchemeComplexPoint f))
    {Γ Γ' : SourceNAPotential θ} :
    (∀ v, (BJ.Exist.naAnalytification f n E b HM hm hθ ω Γ).1 v ≤
      (BJ.Exist.naAnalytification f n E b HM hm hθ ω Γ').1 v) ↔ SourceNAPOrder Γ Γ' :=
  (sourceNAPOrder_iff_naPotentialAnAt_le_dim n E Γ Γ' ω).symm

include hm hθ in
/-- **`lma:anaorder`, last sentence (`thm:DXZ`, injectivity), every dimension, no dictionary
hypothesis**: the map `eq:analymap` `PSH^NA(X, θ) → PSH(L^An)` is injective. -/
theorem naAnalytification_injective_dim (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    Function.Injective (BJ.Exist.naAnalytification (θ := θ) f n E b HM hm hθ ω) := by
  intro Γ Γ' h
  exact naPotentialAnAt_injective_dim n E ω (congrArg Subtype.val h)

end SGPT.NAPotential.DimZero
