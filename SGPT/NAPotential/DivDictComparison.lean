import SGPT.NAPotential.DivDictIdentity
import SGPT.NAPotential.DivDictTrivial
import SGPT.NAPotential.BJPrepInfimum

/-! # `Γ^An` on `X^Div` through the dictionary of prime divisors

Source `chapter_NApotential.tex`, Section *The comparison theorem*: `lma:anaorder`
(order reflection and injectivity of `Γ ↦ Γ^An`), `prop:anpreinf` (compatibility with decreasing
infima) and the injectivity part of `thm:DXZ`, on the domain `X^Div` of `def:Gammaana` (the
divisorial valuations `t ord_E` and the trivial valuation).
Blueprint `claude-div-dict:gamma-div`, `claude-div-dict:anaorder`, `claude-div-dict:anpreinf`.

The divisorial core of these statements was proved in Lelong-number form by
`SGPT.NAPotential.BJPrep` (`naDivisorialTransform`, on analytic presentations of prime divisors).
The identity `φ^An(t ord_D) = -t ν(φ, p)` of `DivDictIdentity` (for an algebraic prime divisor
`D` over `X` realized by the analytic presentation `p`) transfers them to the Berkovich points:

* `naPotentialAnAt_ordVal`: `Γ^An(t ord_D) = sup_{τ < Γ_max} (τ - t ν(Γ_τ, p))`;
* `naPotentialAnAt_ordVal_decreasingInf`: `(inf_i Γ_i)^An(t ord_D) = inf_i Γ_i^An(t ord_D)`
  (`prop:anpreinf` at a realized divisorial point);
* `sourceNAPOrder_of_naPotentialAnDiv_le`, `sourceNAPOrder_iff_naPotentialAnDiv_le`,
  `naPotentialAnDiv_injective`: `lma:anaorder` and the injectivity in `thm:DXZ` on `X^Div`;
* `naPotentialAnDiv_decreasingInf`: `prop:anpreinf` on `X^Div`.

All results are conditional on `MultiplierIdealAlgebraic` (GAGA for multiplier ideals).  The
statements on the whole of `X^Div` moreover use the two halves of the dictionary as explicit
hypotheses: `AnalyticPrimesRealized` (every analytic presentation is realized by an algebraic
prime divisor over `X`; used for order reflection and injectivity) and `AlgebraicPrimesRealized`
(every algebraic prime divisor over `X` has an analytic realization; used for `prop:anpreinf`).
Neither half is proved here: they need resolution of singularities, the analytification of
normal models and the algebraicity of modifications of `X(ℂ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.NAPotential.BJPrep

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (m : ℕ) [SmoothOfRelativeDimension (m + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance divDictCmpPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDictCmpPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDictCmpPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The analytic half of the dictionary: every analytic presentation of a prime divisor over
`X(ℂ)` (a smooth connected hypersurface in a modification) is realized by an algebraic prime
divisor over the scheme `X`.  (A statement, not proved in this file.) -/
def AnalyticPrimesRealized : Prop :=
  ∀ p : PrimePresentation (m + 1) (SchemeComplexPoint f),
    ∃ D : PrimeDivisorOver X, D.IsRealizedBy m E p

/-- The algebraic half of the dictionary: every algebraic prime divisor over the scheme `X` is
realized by an analytic presentation.  (A statement, not proved in this file.) -/
def AlgebraicPrimesRealized : Prop :=
  ∀ D : PrimeDivisorOver X,
    ∃ p : PrimePresentation (m + 1) (SchemeComplexPoint f), D.IsRealizedBy m E p

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

variable {m E}

/-- **`Γ^An` at a divisorial valuation** (`def:Gammaana` and the sentence after
`def:NApotential:L975`): for a prime divisor `D` over `X` realized by the analytic presentation
`p`, `Γ^An(t ord_D) = sup_{τ < Γ_max} (τ - t ν(Γ_τ^{θ+ω}, p))`, the Lelong-number form
`naDivisorialTransform` of `SGPT.NAPotential.BJPrep`.  Conditional on
`MultiplierIdealAlgebraic`. -/
theorem naPotentialAnAt_ordVal (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (t : ℝ) (ht : 0 < t) :
    naPotentialAnAt (m + 1) E Γ ω (D.ordVal f t ht) = naDivisorialTransform Γ ω p t := by
  unfold naPotentialAnAt naDivisorialTransform curveDivisorialTransform
  rw [iSup_subtype]
  refine iSup_congr fun τ => iSup_congr fun h => ?_
  rw [potentialAn_ordVal hA hDp (naComponent_potential_isThetaPshPotential (m + 1) Γ ω ⟨τ, h⟩)
    t ht, add_comm, sub_eq_add_neg]

section Infimum

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **`prop:anpreinf` at a realized divisorial point**: for a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` satisfying `eq:decnetcontition`, `(inf_i Γ_i)^An(t ord_D) = inf_i Γ_i^An(t ord_D)`.
Conditional on `MultiplierIdealAlgebraic`. -/
theorem naPotentialAnAt_ordVal_decreasingInf (hA : MultiplierIdealAlgebraic f (m + 1) E)
    {D : PrimeDivisorOver X} {p : PrimePresentation (m + 1) (SchemeComplexPoint f)}
    (hDp : D.IsRealizedBy m E p) (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (t : ℝ) (ht : 0 < t) :
    naPotentialAnAt (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω
        (D.ordVal f t ht) =
      ⨅ i, naPotentialAnAt (m + 1) E (Γ i) ω (D.ordVal f t ht) := by
  rw [naPotentialAnAt_ordVal hA hDp, naDivisorialTransform_decreasingInf omega Γ ha hb ω p ht]
  exact iInf_congr fun i => (naPotentialAnAt_ordVal hA hDp (Γ i) ω t ht).symm

end Infimum

variable [IsIntegral X]

/-- **Order reflection on `X^Div`** (second sentence of `lma:anaorder`): if
`Γ^An ≤ Γ'^An` on `X^Div` (the divisorial valuations and the trivial valuation), then `Γ ≤ Γ'`.
Conditional on `MultiplierIdealAlgebraic` and on the analytic half of the dictionary. -/
theorem sourceNAPOrder_of_naPotentialAnDiv_le (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (han : AnalyticPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (h : ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v) :
    SourceNAPOrder Γ Γ' := by
  have hmax : (Γ.component ω).val.max ≤ (Γ'.component ω).val.max := by
    have h0 := h ⟨BerkovichPoint.trivial f, trivial_mem_sourceDivisorialSet f⟩
    change naPotentialAnAt (m + 1) E Γ ω (BerkovichPoint.trivial f) ≤
      naPotentialAnAt (m + 1) E Γ' ω (BerkovichPoint.trivial f) at h0
    rw [naPotentialAnAt_trivial hA, naPotentialAnAt_trivial hA] at h0
    exact EReal.coe_le_coe_iff.mp h0
  refine sourceNAPOrder_of_naDivisorialTransform_le ω hmax fun p t ht => ?_
  obtain ⟨D, hD⟩ := han p
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [← naPotentialAnAt_ordVal hA hD Γ ω t ht', ← naPotentialAnAt_ordVal hA hD Γ' ω t ht']
  exact h ⟨D.ordVal f t ht', divisorialSet_subset_sourceDivisorialSet f ⟨D, t, ht', rfl⟩⟩

/-- **`lma:anaorder` on `X^Div`**: `Γ ≤ Γ'` if and only if `Γ^An ≤ Γ'^An` on `X^Div`.
Conditional on `MultiplierIdealAlgebraic` and on the analytic half of the dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnDiv_le (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (han : AnalyticPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v ≤ naPotentialAnDiv (m + 1) E Γ' ω v :=
  ⟨fun h v => naPotentialAnAt_mono hA h ω v.1,
    sourceNAPOrder_of_naPotentialAnDiv_le hA han ω⟩

/-- **Injectivity of `Γ ↦ Γ^An`** (last sentence of `lma:anaorder`; the injectivity in
`thm:DXZ`), on the domain `X^Div` of `def:Gammaana`.  Conditional on `MultiplierIdealAlgebraic`
and on the analytic half of the dictionary. -/
theorem naPotentialAnDiv_injective (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (han : AnalyticPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnDiv (m + 1) E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v : sourceDivisorialSet f,
      naPotentialAnDiv (m + 1) E Γ ω v = naPotentialAnDiv (m + 1) E Γ' ω v :=
    fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    (sourceNAPOrder_of_naPotentialAnDiv_le hA han ω fun v => (h' v).le)
    (sourceNAPOrder_of_naPotentialAnDiv_le hA han ω fun v => (h' v).ge)

/-- **`lma:anaorder` for functions on `X^An`**: `Γ ≤ Γ'` if and only if `Γ^An ≤ Γ'^An` on the
whole Berkovich space.  Conditional on `MultiplierIdealAlgebraic` and on the analytic half of the
dictionary. -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (han : AnalyticPrimesRealized (f := f) m E) {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v :=
  ⟨fun h v => naPotentialAnAt_mono hA h ω v,
    fun h => sourceNAPOrder_of_naPotentialAnDiv_le hA han ω fun v => h v.1⟩

/-- **Injectivity of `Γ ↦ Γ^An` as functions on `X^An`** (`lma:anaorder`, `thm:DXZ`).
Conditional on `MultiplierIdealAlgebraic` and on the analytic half of the dictionary. -/
theorem naPotentialAnAt_injective (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (han : AnalyticPrimesRealized (f := f) m E)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt (m + 1) E Γ ω := by
  intro Γ Γ' h
  exact naPotentialAnDiv_injective hA han ω (funext fun v => congrFun h v.1)

section Infimum

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

omit [IsIntegral X] in
/-- The cutoff of the infimum of a decreasing net is the infimum of the cutoffs. -/
theorem coe_decreasingInf_max (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
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

/-- **`prop:anpreinf` on `X^Div`**: for a decreasing net `(Γ_i)` in `PSH^NA(X, θ)` satisfying
`eq:decnetcontition`, `(inf_i Γ_i)^An = inf_i Γ_i^An` on `X^Div`.  Conditional on
`MultiplierIdealAlgebraic` and on the algebraic half of the dictionary. -/
theorem naPotentialAnDiv_decreasingInf (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (halg : AlgebraicPrimesRealized (f := f) m E)
    (omega : KahlerBackground (m + 1) (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    naPotentialAnDiv (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω v =
      ⨅ i, naPotentialAnDiv (m + 1) E (Γ i) ω v := by
  obtain ⟨v, hv⟩ := v
  change naPotentialAnAt (m + 1) E (SourceNAPotential.decreasingInf omega Γ ha hb) ω v =
    ⨅ i, naPotentialAnAt (m + 1) E (Γ i) ω v
  rcases hv with rfl | ⟨D, t, ht, rfl⟩
  · rw [naPotentialAnAt_trivial hA, coe_decreasingInf_max omega Γ ha hb ω]
    exact iInf_congr fun i => (naPotentialAnAt_trivial hA (Γ i) ω).symm
  · obtain ⟨p, hDp⟩ := halg D
    exact naPotentialAnAt_ordVal_decreasingInf hA hDp omega Γ ha hb ω t ht

end Infimum

end SGPT.NAPotential.Berkovich

end
