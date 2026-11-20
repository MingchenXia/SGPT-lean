import SGPT.Checks.Comparison.SourceZeroModels
import SGPT.NAPotential.DecreasingInfimum

/-! Original cutoff and zero-dimensional full-analytification infimum proof.
This fresh source port avoids the independent point-order/point-trace API.
Blueprint: source-infimum-zero-narrow.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ.SourceInfDimZero

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

/-! ### The cutoff of a decreasing infimum (every dimension) -/

section Cutoff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The cutoff of the infimum of a decreasing net in `PSH^NA(X, θ)` is the infimum of the cutoffs
(any dimension, any Kähler index). -/
theorem coe_decreasingInf_max_dim (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n M) :
    ((((SourceNAPotential.decreasingInf omega Γ ha hb).component ω).val.max : ℝ) : EReal) =
      ⨅ i, ((((Γ i).component ω).val.max : ℝ) : EReal) := by
  have hGb := sourceNAFamily_component_bddBelow omega Γ hb ω
  have hmax : ((SourceNAPotential.decreasingInf omega Γ ha hb).component ω).val.max =
      sInf (range fun i => ((Γ i).component ω).val.max) := rfl
  rw [hmax]
  apply le_antisymm
  · exact le_iInf fun i => EReal.coe_le_coe_iff.mpr (csInf_le hGb (mem_range_self i))
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    obtain ⟨b, ⟨i, rfl⟩, hi⟩ := exists_lt_of_csInf_lt (range_nonempty _)
      (EReal.coe_lt_coe_iff.mp hq1)
    exact absurd ((iInf_le _ i).trans (EReal.coe_le_coe_iff.mpr hi.le)) (not_le.mpr hq2)

end Cutoff

section Scheme

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance dimZeroAnPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroAnPointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance dimZeroAnPointManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

section Infimum

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **`prop:anpreinf` in dimension zero, on `X^An`** (unconditional). For `X` smooth projective of
relative dimension `0` with `X(ℂ)` connected (a point) and a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` satisfying `eq:decnetcontition` (cutoffs bounded below),
`(inf_i Γ_i)^An(v) = inf_i Γ_i^An(v)` for every `v ∈ X^An`. -/
theorem naPotentialAnAt_decreasingInf_of_dim_zero
    (omega : KahlerBackground 0 (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    naPotentialAnAt 0 E (SourceNAPotential.decreasingInf omega Γ ha hb) ω =
      fun v => ⨅ i, naPotentialAnAt 0 E (Γ i) ω v := by
  funext v
  rw [SourceZeroModels.naPotentialAnAt_eq_of_dim_zero, coe_decreasingInf_max_dim omega Γ ha hb ω]
  simp_rw [SourceZeroModels.naPotentialAnAt_eq_of_dim_zero]

/-- **`prop:anpreinf` in dimension zero, on `X^Div`** (unconditional; the statement of the book's
proof before `thm:pshdetbydiv`). -/
theorem naPotentialAnDiv_decreasingInf_of_dim_zero [IrreducibleSpace X]
    (omega : KahlerBackground 0 (SchemeComplexPoint f)) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    naPotentialAnDiv 0 E (SourceNAPotential.decreasingInf omega Γ ha hb) ω v =
      ⨅ i, naPotentialAnDiv 0 E (Γ i) ω v :=
  congrFun (naPotentialAnAt_decreasingInf_of_dim_zero E omega Γ ha hb ω) v.1

end Infimum

end Scheme

end SGPT.NAPotential.BJ.SourceInfDimZero

end
