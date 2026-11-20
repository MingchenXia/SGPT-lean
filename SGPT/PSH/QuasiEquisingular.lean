import SGPT.PSH.SingularityOrder
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformComparison
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAuxiliaryDomination

set_option autoImplicit false

/-!
The original SGPT four-clause approximation definition has an existential
auxiliary Kähler background and one multiplier inclusion term per separated
pair of exponents. Original antitonicity produces the entire tail inclusion.
Existing main background domination and uniform comparison are reused.
Natural index k represents the original positive index k+1.
-/

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open scoped Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- SGPT `def:quasiequsing`: all four original conditions, with actual
analytic germs, pointwise decreasing limit, an existential genuine auxiliary
Kähler form/error, and the literal original one-term ideal inclusion. -/
def SourceQuasiEquisingularApproximation (θ : ClosedRealOneOneForm n M)
    (u : M → EReal) (U : ℕ → M → EReal) : Prop :=
  IsThetaPshPotential θ.val u ∧
    (∀ j, HasManifoldAnalyticSingularityType (n := n) (U j)) ∧
    DecreasesPointwiseTo U u ∧
    (∃ (ω : KahlerBackground n M) (ε : ℕ → ℝ),
      NonnegativeDecreasesToZero ε ∧
      ∀ j, IsThetaPshPotential (θ + ε j • ω.form).val (U j)) ∧
    ∀ c d : ℝ, 0 < c → c < d →
      ∃ j, MultiplierIdealIncluded (n := n) (U j) d u c

/-- Existing main approximation fields imply every original source condition. -/
theorem sourceQuasiEquisingularApproximation_of_native
    {ω : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation ω θ u ε U) :
    SourceQuasiEquisingularApproximation θ u U := by
  refine ⟨h.target, h.term_hasAnalyticSingularityType, h.decreasesPointwise,
    ⟨ω, ε, h.error, h.term⟩, ?_⟩
  intro c d hc hcd
  exact (h.eventually_multiplierIdealIncluded hc hcd).exists

/-- The original one-term ideal inclusion propagates to the whole late tail
by genuine pointwise antitonicity and existing multiplier-ideal order. -/
theorem native_of_sourceQuasiEquisingularApproximation
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {U : ℕ → M → EReal}
    (h : SourceQuasiEquisingularApproximation θ u U) :
    ∃ (ω : KahlerBackground n M) (ε : ℕ → ℝ),
      IsQuasiEquisingularApproximation ω θ u ε U := by
  obtain ⟨hu, ha, hd, ⟨ω, ε, hε, ht⟩, hI⟩ := h
  refine ⟨ω, ε, hu, hε, ht, ha, hd, ?_⟩
  intro c d hc hcd
  obtain ⟨j, hj⟩ := hI c d hc hcd
  filter_upwards [eventually_ge_atTop j] with k hk
  have horder := iOrderOnManifold_of_le (ht j).1.quasiPlurisubharmonic
    (fun x ↦ hd.1 x hk)
  intro e z hz f hf hmem
  exact hj e z hz f hf (horder d (hc.trans hcd) e z hz f hf hmem)

/-- Exact equivalence with genuine existing full approximation records.
The actual functions and all original values, including poles, are preserved. -/
theorem sourceQuasiEquisingularApproximation_iff_exists_native
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) (U : ℕ → M → EReal) :
    SourceQuasiEquisingularApproximation θ u U ↔
      ∃ (ω : KahlerBackground n M) (ε : ℕ → ℝ),
        IsQuasiEquisingularApproximation ω θ u ε U := by
  constructor
  · exact native_of_sourceQuasiEquisingularApproximation
  · rintro ⟨ω, ε, h⟩
    exact sourceQuasiEquisingularApproximation_of_native h

/-- Original arbitrary source approximations may use different auxiliary
forms. Existing main domination internally produces one genuine common form;
main's full comparison then produces one finite constant for the entire tail. -/
theorem sourceQuasiEquisingular_uniform_tail_comparison [CompactSpace M]
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {U V : ℕ → M → EReal}
    (hU : SourceQuasiEquisingularApproximation θ u U)
    (hV : SourceQuasiEquisingularApproximation θ u V)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∃ C : ℝ, ∀ k ≥ k₀, ∀ x : M,
      V k x ≤ ((1 - a : ℝ) : EReal) * U j x + (C : EReal) := by
  obtain ⟨ω₀, ε, hU'⟩ := native_of_sourceQuasiEquisingularApproximation hU
  obtain ⟨ω₁, δ, hV'⟩ := native_of_sourceQuasiEquisingularApproximation hV
  obtain ⟨κ, hκ₀, hκ₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background ω₀ ω₁
  have hUκ :=
    QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
      hU' hκ₀
  have hVκ :=
    QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
      hV' hκ₁
  obtain ⟨k₀, C, hC⟩ :=
    QuasiEquisingularUniformComparison.exists_uniform_tail_comparison hUκ hVκ ha0 ha1 j
  exact ⟨max k₀ 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), C,
    fun k hk x ↦ hC k ((le_max_left _ _).trans hk) x⟩

/-- SGPT `prop:compqequi`: the literal original singularity preorder in
every dimension, for arbitrary genuine source approximation choices. -/
theorem sourceQuasiEquisingular_eventually_singularityLE [CompactSpace M]
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {U V : ℕ → M → EReal}
    (hU : SourceQuasiEquisingularApproximation θ u U)
    (hV : SourceQuasiEquisingularApproximation θ u V)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k ≥ k₀,
      SingularityLE (V k) (fun x ↦ ((1 - a : ℝ) : EReal) * U j x) := by
  obtain ⟨k₀, hk₀, C, hC⟩ := sourceQuasiEquisingular_uniform_tail_comparison hU hV ha0 ha1 j
  refine ⟨k₀, hk₀, fun k hk ↦ ?_⟩
  exact (singularityLE_iff_exists_real _ _).mpr ⟨C, hC k hk⟩

end

end SGPT.PSH
