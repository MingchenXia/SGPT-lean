import SGPT.NAPotential.QwNANonTrivRestZero
import SGPT.NAPotential.DecreasingInfimum
import SGPT.Trace.PointTrace
import SGPT.NAPotential.TowerAlgReflect

/-!
# `prop:anpreinf` and `lma:anaorder` in dimension zero

Source: `chapter_NApotential.tex`, *The comparison theorem* (`X` a connected projective manifold
of dimension `n`, `L` a pseudo-effective `ℚ`-line bundle, `θ = c₁(L, h)`; `n = 0` is not
excluded). Blueprint `claude-dim-zero.tex`, nodes `claude-dim-zero:anpreinf` and
`claude-dim-zero:anaorder`.

* `prop:anpreinf`: *for a decreasing net `(Γ_i)_{i ∈ I}` in `PSH^NA(X, θ)` satisfying
  `eq:decnetcontition`, `(inf_i Γ_i)^An = inf_i Γ_i^An`.* The workspace proves it on `X^Div` and on
  `X^An` for `X` of relative dimension `m + 1 ≥ 1` (lanes NA-DICT2 and BJ-EXIST, conditionally on
  `AlgebraicPrimesRealized`). Here the dimension-zero case, **unconditionally**:
  `naPotentialAnAt_decreasingInf_of_dim_zero` (on `X^An`) and
  `naPotentialAnDiv_decreasingInf_of_dim_zero` (on `X^Div`). In dimension zero
  `Γ^An ≡ Γ_max` (`NANS.naPotentialAnAt_eq_of_dim_zero`) and the cutoff of the infimum is the
  infimum of the cutoffs (`coe_decreasingInf_max_dim`, valid in every dimension).
* `lma:anaorder`: *`Γ ↦ Γ^An` is order preserving; `Γ^An ≤ Γ'^An` implies `Γ ≤ Γ'`; hence the map
  is injective.* The workspace proves the reflection and injectivity for `X` of relative
  dimension `m + 1` (`TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le`,
  `TowerAlg.naPotentialAnAt_injective`). Here the dimension-zero case:
  `sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero`, `naPotentialAnAt_injective_of_dim_zero`
  (and the same with `X^Div` in place of `X^An`); with TOWER-ALG's positive-dimensional theorems,
  `sourceNAPOrder_iff_naPotentialAnAt_le_dim` and `naPotentialAnAt_injective_dim` state
  `lma:anaorder` on `X^An` for `X` of every relative dimension. On a point every slice of every element of
  `PSH^NA(X, θ)` is a finite function, any two finite functions are `P`-equivalent
  (`Trace.sourcePEquivalent_of_finite_of_dim_zero`), so `Γ ≤ Γ'` iff `Γ_max ≤ Γ'_max`
  (`sourceNAPOrder_iff_max_le_of_dim_zero`), and `Γ_max = Γ^An(v)` for every `v ∈ X^An`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.DimZero

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

/-! ### The order on `PSH^NA(X, θ)` in dimension zero -/

section Order

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)}

/-- **The order of `PSH^NA(X, θ)` on a point**: for `X` connected of dimension `0`,
`Γ ≤ Γ'` iff `Γ_max ≤ Γ'_max` (read at any Kähler index `ω`). -/
theorem sourceNAPOrder_iff_max_le_of_dim_zero (Γ Γ' : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 M) :
    SourceNAPOrder Γ Γ' ↔ (Γ.component ω).val.max ≤ (Γ'.component ω).val.max := by
  rw [sourceNAPOrder_iff_component Γ Γ' ω]
  refine ⟨fun h => h.cutoff_le, fun h => ⟨h, fun r hr => ?_⟩⟩
  have hfin : ∀ (G : SourceNAPotential θ) (s : ℝ) (hs : s < (G.component ω).val.max) (y : M),
      (G.component ω).val.potential ⟨s, hs⟩ y ≠ ⊤ ∧
        (G.component ω).val.potential ⟨s, hs⟩ y ≠ ⊥ := fun G s hs =>
    (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero _ _).mp ((G.component ω).val.thetaPSH ⟨s, hs⟩)
  exact (SGPT.Trace.sourcePEquivalent_of_finite_of_dim_zero (sourceKahlerFormRepresentative ω)
    (hfin Γ r hr) (hfin Γ' r (hr.trans_le h))).1

end Order

/-! ### `Γ^An` in dimension zero -/

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
  rw [NANS.naPotentialAnAt_eq_of_dim_zero, coe_decreasingInf_max_dim omega Γ ha hb ω]
  simp_rw [NANS.naPotentialAnAt_eq_of_dim_zero]

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

/-- **`lma:anaorder` in dimension zero, on `X^An`**: `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^An`. -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero [IrreducibleSpace X]
    (Γ Γ' : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt 0 E Γ ω v ≤ naPotentialAnAt 0 E Γ' ω v := by
  simp_rw [NANS.naPotentialAnAt_eq_of_dim_zero, EReal.coe_le_coe_iff]
  rw [sourceNAPOrder_iff_max_le_of_dim_zero Γ Γ' ω]
  exact ⟨fun h _ => h, fun h => h (BerkovichPoint.trivial f)⟩

/-- **`lma:anaorder` in dimension zero, on `X^Div`**: `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^Div`. -/
theorem sourceNAPOrder_iff_naPotentialAnDiv_le_of_dim_zero [IrreducibleSpace X]
    (Γ Γ' : SourceNAPotential θ) (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv 0 E Γ ω v ≤ naPotentialAnDiv 0 E Γ' ω v := by
  rw [sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero E Γ Γ' ω]
  refine ⟨fun h v => h v.1, fun h v => ?_⟩
  have ht := h ⟨BerkovichPoint.trivial f, Or.inl rfl⟩
  simp only [naPotentialAnDiv, NANS.naPotentialAnAt_eq_of_dim_zero] at ht ⊢
  exact ht

/-- **`lma:anaorder` in dimension zero, injectivity**: `Γ ↦ Γ^An` is injective as functions on
`X^An`. -/
theorem naPotentialAnAt_injective_of_dim_zero [IrreducibleSpace X] (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt 0 E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v, naPotentialAnAt 0 E Γ ω v = naPotentialAnAt 0 E Γ' ω v := fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    ((sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero E Γ Γ' ω).mpr fun v => (h' v).le)
    ((sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero E Γ' Γ ω).mpr fun v => (h' v).ge)

/-- **`lma:anaorder` in dimension zero, injectivity on `X^Div`**. -/
theorem naPotentialAnDiv_injective_of_dim_zero [IrreducibleSpace X]
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnDiv 0 E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v, naPotentialAnDiv 0 E Γ ω v = naPotentialAnDiv 0 E Γ' ω v := fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    ((sourceNAPOrder_iff_naPotentialAnDiv_le_of_dim_zero E Γ Γ' ω).mpr fun v => (h' v).le)
    ((sourceNAPOrder_iff_naPotentialAnDiv_le_of_dim_zero E Γ' Γ ω).mpr fun v => (h' v).ge)

/-- `eq:Gammamax` in dimension zero: `Γ^An(v_triv) = Γ_max`. -/
theorem naPotentialAnAt_trivial_of_dim_zero [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    naPotentialAnAt 0 E Γ ω (BerkovichPoint.trivial f) = ((Γ.component ω).val.max : EReal) :=
  NANS.naPotentialAnAt_eq_of_dim_zero Γ ω _

end Scheme

/-! ### `lma:anaorder` in every dimension -/

section AllDimensions

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f] [IsIntegral X]

local instance dimZeroAnAllTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroAnAllCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dimZeroAnAllManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- **`lma:anaorder` on `X^An`, every dimension**: for `X` smooth projective of any relative
dimension `n` (integral, `X(ℂ)` connected), `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^An`. Dimension `0`:
`sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero`; dimension `m + 1`: TOWER-ALG's
`TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le` (no dictionary hypothesis). -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le_dim (Γ Γ' : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt n E Γ ω v ≤ naPotentialAnAt n E Γ' ω v := by
  cases n with
  | zero => exact sourceNAPOrder_iff_naPotentialAnAt_le_of_dim_zero E Γ Γ' ω
  | succ m => exact SGPT.NAPotential.TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le ω

/-- **`lma:anaorder`, injectivity on `X^An`, every dimension.** -/
theorem naPotentialAnAt_injective_dim (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt n E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v, naPotentialAnAt n E Γ ω v = naPotentialAnAt n E Γ' ω v := fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    ((sourceNAPOrder_iff_naPotentialAnAt_le_dim n E Γ Γ' ω).mpr fun v => (h' v).le)
    ((sourceNAPOrder_iff_naPotentialAnAt_le_dim n E Γ' Γ ω).mpr fun v => (h' v).ge)

end AllDimensions

end SGPT.NAPotential.DimZero

end
