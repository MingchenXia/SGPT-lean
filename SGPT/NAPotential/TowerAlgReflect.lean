import SGPT.NAPotential.TowerAlgIdeal

/-!
# Order reflection and injectivity of `Γ ↦ Γ^An` on `X^An` without a dictionary hypothesis

Source `chapter_NApotential.tex`, `lma:anaorder` (*if `Γ^An ≤ Γ'^An` then `Γ ≤ Γ'`; in particular
`Γ ↦ Γ^An` is injective*) and the injectivity in `thm:DXZ`.  Lane TOWER-ALG, blueprint
`claude-tower-alg.tex`, nodes `claude-tower-alg:potential`, `claude-tower-alg:anaorder`.

Lanes DIV-DICT / NA-DICT2 proved order reflection on `X^An` under the hypothesis
`BlowupPrimesRealized` (every prime divisor on a blow-up tower of `X(ℂ)` is realized by an
*algebraic* prime divisor over `X`, a `PrimeDivisorOver X` on a normal proper birational model),
because the book's proof evaluates `Γ^An` at the divisorial valuations `t ord_E`.  For the
statement on `X^An` no algebraic model is needed: the divisorial valuation `t ord_E` of `ℂ(X)` is
realized directly by the analytic order along `E` (`SGPT.NAPotential.TowerAlg.anDivVal`, a point
of `X^An`), and its values on ideal sheaves are the analytic orders
(`SGPT.NAPotential.TowerAlg.idealVal_anDivVal_eq`).  This file draws the consequences:

* `potentialVal_anDivVal`, `potentialAn_anDivVal`: `φ^An(t ord_E) = -t ν(φ, E)`
  (the sentence after `def:NApotential:L975`) for the analytic divisorial valuation;
* `naPotentialAnAt_anDivVal`: `Γ^An(t ord_E) = sup_{τ < Γ_max} (τ - t ν(Γ_τ, E))`;
* **`sourceNAPOrder_of_naPotentialAnAt_le`, `sourceNAPOrder_iff_naPotentialAnAt_le`,
  `naPotentialAnAt_injective`**: `lma:anaorder` and the injectivity of `thm:DXZ` for `Γ^An` as
  functions on `X^An`, with no dictionary hypothesis (neither `BlowupPrimesRealized` nor
  `AnalyticPrimesRealized`), for every analytic presentation (not only blow-up towers).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.TowerAlg

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder
  SGPT.PSH.CompactPrimeMultiplierLimit
open SGPT.NAPotential.BJPrep SGPT.NAPotential.Berkovich
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder MultiplierIdealLowerBound

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance towerAlgReflectPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance towerAlgReflectPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance towerAlgReflectPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-! ### Potentials at the analytic divisorial valuations -/

section Potential

variable [IsIntegral X] (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
  {y₀ : p.model} (Φ₀ : DivisorFlattening (m := m) p.divisor y₀)

/-- The value of `t ord_E` on the algebraic model of the multiplier ideal `𝓘(cφ)` is
`t` times the order of `𝓘(cφ)` along `E`. -/
theorem idealVal_anDivVal_algebraization_multiplierIdeal (t : ℝ) (ht : 0 < t)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ)
    {c : ℝ} (hc : 0 < c) :
    (anDivVal p Φ₀ t ht).idealVal (algebraization f (m + 1) E (multiplierIdeal (n := m + 1) c φ)) =
      ENNReal.ofReal t * (presentationMultiplierOrder hφ hc p : ℝ≥0∞) := by
  have hE := primePresentation_smooth_hypersurface m p
  have hy₀ : y₀ ∈ p.divisor :=
    (IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Φ₀).2.1
  rw [idealVal_anDivVal_eq p Φ₀ E t ht,
    DivDict2.analytificationIdeal_algebraization_multiplierIdeal hφ hc,
    originalStalkNormalOrder_eq_actualMultiplierCoefficient p.modification hE hφ hc y₀ hy₀ Φ₀]
  rfl

/-- **`v(φ) = t ν(φ, E)` for the analytic divisorial valuation `v = t ord_E`** (the sentence after
`eq:varphiAnalt`), for `φ ∈ PSH(X, θ)`. -/
theorem potentialVal_anDivVal {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (t : ℝ) (ht : 0 < t) :
    (anDivVal p Φ₀ t ht).potentialVal (m + 1) E φ = ENNReal.ofReal t * presentationReader φ p := by
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  have h1 := BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic (m + 1) E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ (anDivVal p Φ₀ t ht)
  have h1' := (tendsto_add_atTop_iff_nat 1).mpr h1
  have h2 := tendsto_presentationMultiplierOrder_ratio hq p
  have h3 : Tendsto (fun k : ℕ => ENNReal.ofReal t *
      ((presentationMultiplierOrder hq (show (0 : ℝ) < (k + 1 : ℕ) by positivity) p : ℝ≥0∞) /
        (k + 1 : ℕ))) atTop (𝓝 (ENNReal.ofReal t * presentationReader φ p)) :=
    ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_nhds_unique h1' (h3.congr fun k => ?_)
  unfold BerkovichPoint.multiplierIdealVal
  rw [idealVal_anDivVal_algebraization_multiplierIdeal p Φ₀ t ht hq
    (show (0 : ℝ) < (k + 1 : ℕ) by positivity), mul_div_assoc]

/-- **`φ^An(t ord_E) = -t ν(φ, E)`** at the analytic divisorial valuation, for `φ ∈ PSH(X, θ)`. -/
theorem potentialAn_anDivVal {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (t : ℝ) (ht : 0 < t) :
    potentialAn (m + 1) E φ (anDivVal p Φ₀ t ht) =
      -((t : EReal) * ((presentationReader φ p : ℝ≥0∞) : EReal)) := by
  unfold potentialAn
  rw [potentialVal_anDivVal p Φ₀ hφ t ht, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left ht.le]

end Potential

/-- Every analytic presentation carries a point of its hypersurface with a flattening. -/
theorem exists_divisorFlattening (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) :
    ∃ y₀ : p.model, Nonempty (DivisorFlattening (m := m) p.divisor y₀) := by
  have hE := primePresentation_smooth_hypersurface m p
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  exact ⟨y, DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)⟩

/-! ### Non-Archimedean potentials -/

section NA

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

/-- **`Γ^An` at the analytic divisorial valuation `t ord_E`**:
`Γ^An(t ord_E) = sup_{τ < Γ_max} (τ - t ν(Γ_τ^{θ+ω}, E))`. -/
theorem naPotentialAnAt_anDivVal [IsIntegral X]
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {y₀ : p.model}
    (Φ₀ : DivisorFlattening (m := m) p.divisor y₀) (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (t : ℝ) (ht : 0 < t) :
    naPotentialAnAt (m + 1) E Γ ω (anDivVal p Φ₀ t ht) = naDivisorialTransform Γ ω p t := by
  unfold naPotentialAnAt naDivisorialTransform curveDivisorialTransform
  rw [iSup_subtype]
  refine iSup_congr fun τ => iSup_congr fun h => ?_
  rw [potentialAn_anDivVal p Φ₀
    (naComponent_potential_isThetaPshPotential (m + 1) Γ ω ⟨τ, h⟩) t ht, add_comm,
    sub_eq_add_neg]

variable [IsIntegral X]

/-- **Order reflection on `X^An`** (second sentence of `lma:anaorder`), with no dictionary
hypothesis: if `Γ^An ≤ Γ'^An` on `X^An`, then `Γ ≤ Γ'`. -/
theorem sourceNAPOrder_of_naPotentialAnAt_le {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (h : ∀ v : BerkovichPoint f, naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v) :
    SourceNAPOrder Γ Γ' := by
  have hmax : (Γ.component ω).val.max ≤ (Γ'.component ω).val.max := by
    have h0 := h (BerkovichPoint.trivial f)
    rw [DivDict2.naPotentialAnAt_trivial, DivDict2.naPotentialAnAt_trivial] at h0
    exact EReal.coe_le_coe_iff.mp h0
  refine sourceNAPOrder_of_naDivisorialTransform_le ω hmax fun p t ht => ?_
  obtain ⟨y₀, ⟨Φ₀⟩⟩ := exists_divisorFlattening p
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [← naPotentialAnAt_anDivVal p Φ₀ Γ ω t ht', ← naPotentialAnAt_anDivVal p Φ₀ Γ' ω t ht']
  exact h _

/-- **`lma:anaorder` for `Γ^An` on `X^An`**: `Γ ≤ Γ'` iff `Γ^An ≤ Γ'^An` on `X^An`. -/
theorem sourceNAPOrder_iff_naPotentialAnAt_le {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt (m + 1) E Γ ω v ≤ naPotentialAnAt (m + 1) E Γ' ω v :=
  ⟨fun h v => DivDict2.naPotentialAnAt_mono h ω v, sourceNAPOrder_of_naPotentialAnAt_le ω⟩

/-- **Injectivity of `Γ ↦ Γ^An`** as functions on `X^An` (`lma:anaorder`, `thm:DXZ`), with no
dictionary hypothesis. -/
theorem naPotentialAnAt_injective (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    Function.Injective fun Γ : SourceNAPotential θ => naPotentialAnAt (m + 1) E Γ ω := by
  intro Γ Γ' h
  have h' : ∀ v : BerkovichPoint f,
      naPotentialAnAt (m + 1) E Γ ω v = naPotentialAnAt (m + 1) E Γ' ω v :=
    fun v => congrFun h v
  exact SourceNAPOrder.antisymm
    (sourceNAPOrder_of_naPotentialAnAt_le ω fun v => (h' v).le)
    (sourceNAPOrder_of_naPotentialAnAt_le ω fun v => (h' v).ge)

end NA

end SGPT.NAPotential.TowerAlg

end
