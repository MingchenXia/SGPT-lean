import SGPT.PSH.RIsoACommonModel
import SGPT.PSH.CompactPrimeMultiplierLimit

/-!
# Prime divisors over compact, possibly disconnected, complex manifolds

`SGPT.PSH.CompactPrimeOver` formalizes prime divisors over a complex manifold `X` (`def:primdiv`,
smooth base): presentations `PrimePresentation n X` (a modification `X' → X` and a connected
smooth hypersurface `E ⊆ X'`), the relation "there is a common resolution on which the strict
transforms coincide" (`commonResolutionRelation`), and, for compact **connected** `X`, its
transitivity, the quotient `DirectPrimeOver n X`, the generic Lelong number `ν(φ, E)`
(`def:pshfunctions:L1112`) and the multiplier-ideal formula `prop:Lelongnumfrommis`.

All presentation-level statements there hold for arbitrary `X`; only transitivity used
connectedness (through the connected common model).  With
`SGPT.PSH.RIsoACommonModel.exists_compact_common_model` the same relation is transitive on every
compact `X` (`commonResolutionRelation_trans_of_compact`), so the book's quotient, its centre,
the generic Lelong number of `def:pshfunctions:L1112` and the formula of `prop:Lelongnumfrommis`
exist for all compact complex manifolds, connected or not.  For connected `X` the quotient is
literally the earlier `DirectPrimeOver n X` (`primeOverCompact_eq_directPrimeOver`).

Blueprint: `claude-r-iso-a.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.RIsoAPrimeOver

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy CompactPrimeOver
  CompactPrimeMultiplierOrder CompactPrimeMultiplierLimit VariableComplexAtlas
  SquaredLogLelongSourceNormalization

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section Compact

variable [CompactSpace X]

/-- **Transitivity over compact bases** (`def:primdiv`): the common-resolution relation is
transitive on every compact complex manifold, connected or not.  A single new witness is built
from a common model of the two middle models (`exists_compact_common_model`) and composition of
strict transforms. -/
theorem commonResolutionRelation_trans_of_compact {p q r : PrimePresentation n X}
    (hpq : commonResolutionRelation p q) (hqr : commonResolutionRelation q r) :
    commonResolutionRelation p r := by
  obtain ⟨h₀⟩ := hpq
  obtain ⟨h₁⟩ := hqr
  let : CompactSpace q.model :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification q.modification
  obtain ⟨Z, instTop, instChart, instMfd, _instCompact, a, b, ha, hb, hab⟩ :=
    RIsoACommonModel.exists_compact_common_model h₀.right_modification h₁.left_modification
  refine ⟨⟨BlowupTowers.CMfd.of (n := n) Z, h₀.left ∘ a, h₁.right ∘ b,
    AnalyticModificationComposition.isAnalyticModification_comp h₀.left_modification ha,
    AnalyticModificationComposition.isAnalyticModification_comp h₁.right_modification hb,
    ?_, ?_⟩⟩
  · funext z
    change p.projection (h₀.left (a z)) = r.projection (h₁.right (b z))
    calc
      p.projection (h₀.left (a z)) = q.projection (h₀.right (a z)) :=
        congrFun h₀.over_base (a z)
      _ = q.projection (h₁.left (b z)) := congrArg q.projection (congrFun hab z)
      _ = r.projection (h₁.right (b z)) := congrFun h₁.over_base (b z)
  · rw [StrictTransformComposition.strictTransform_comp h₀.left_modification.1 ha.1,
      StrictTransformComposition.strictTransform_comp h₁.right_modification.1 hb.1]
    calc
      strictTransform n a (strictTransform n h₀.left p.divisor) =
          strictTransform n a (strictTransform n h₀.right q.divisor) :=
        congrArg (strictTransform n a) h₀.strict_equal
      _ = strictTransform n (h₀.right ∘ a) q.divisor :=
        (StrictTransformComposition.strictTransform_comp h₀.right_modification.1 ha.1
          q.divisor).symm
      _ = strictTransform n (h₁.left ∘ b) q.divisor :=
        congrArg (fun f => strictTransform n f q.divisor) hab
      _ = strictTransform n b (strictTransform n h₁.left q.divisor) :=
        StrictTransformComposition.strictTransform_comp h₁.left_modification.1 hb.1 q.divisor
      _ = strictTransform n b (strictTransform n h₁.right r.divisor) :=
        congrArg (strictTransform n b) h₁.strict_equal

/-- The book's equivalence of prime divisors over a compact complex manifold, as a setoid: the
SINGLE common-resolution relation with its three proved laws. -/
def compactSetoid : Setoid (PrimePresentation n X) where
  r := commonResolutionRelation
  iseqv := ⟨commonResolutionRelation_refl, commonResolutionRelation_symm,
    commonResolutionRelation_trans_of_compact⟩

variable (n X) in
/-- **Source `def:primdiv`** (smooth compact base, connected or not): prime divisors over `X`. -/
def PrimeOverCompact : Type (u + 1) :=
  Quotient (compactSetoid (n := n) (X := X))

variable (n X) in
/-- The set `X^Div` of pairs `c ord_E`, `c ∈ ℚ_{>0}`. -/
def WeightedPrimeOverCompact : Type (u + 1) :=
  {c : ℚ // 0 < c} × PrimeOverCompact n X

/-- Class equality is exactly the single common-resolution relation. -/
theorem compact_mk_eq_iff (p q : PrimePresentation n X) :
    (Quot.mk commonResolutionRelation p : PrimeOverCompact n X) =
      Quot.mk commonResolutionRelation q ↔ commonResolutionRelation p q := by
  constructor
  · exact Quotient.exact (s := compactSetoid (n := n) (X := X)) (a := p) (b := q)
  · exact Quotient.sound (s := compactSetoid (n := n) (X := X)) (a := p) (b := q)

/-- The centre of a prime divisor over `X`. -/
def compactCenter : PrimeOverCompact n X → Set X :=
  Quot.lift presentationCenter (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationCenter_eq_of_commonResolution h)

theorem compactCenter_mk (p : PrimePresentation n X) :
    compactCenter (Quot.mk commonResolutionRelation p) = presentationCenter p := rfl

/-- **Source `def:pshfunctions:L1112`** (compact base): the generic Lelong number
`ν(φ, E) = ν(π^*φ, E)`, independent of the representative. -/
def compactReader (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    PrimeOverCompact n X → ℝ≥0∞ :=
  Quot.lift (presentationReader φ) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationReader_eq_of_commonResolution h hφ)

theorem compactReader_mk (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (p : PrimePresentation n X) :
    compactReader φ hφ (Quot.mk commonResolutionRelation p) = presentationReader φ p := rfl

omit [CompactSpace X] in
private theorem qpsh_of_sourcePSH {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    ManifoldQuasiPlurisubharmonic (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  intro e z hz
  exact (hnative.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt

omit [CompactSpace X] in
private theorem globalQPSH_of_sourcePSH {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    IsGlobalQuasiPshPotential (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  exact ⟨qpsh_of_sourcePSH hφ, hnative.locallyNondegenerate⟩

/-- The generic Lelong number for `φ ∈ PSH(X)` (`def:pshmfd` input). -/
def compactSourcePSHReader (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ) :
    PrimeOverCompact n X → ℝ≥0∞ :=
  compactReader φ (qpsh_of_sourcePSH hφ)

/-- At every representative `E ⊆ Y`, `π : Y → X`, the reader is the generic Lelong number of the
pull-back `ν(π^*φ, E)`. -/
theorem compactSourcePSHReader_mk (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ)
    (p : PrimePresentation n X) :
    compactSourcePSHReader φ hφ (Quot.mk commonResolutionRelation p) =
      (ofFixedModel n p.model).sourceGenericLelong (φ ∘ p.projection) p.divisor := rfl

/-- `ord_E 𝓘(cφ)`: the coefficient along `E` of the pulled-back multiplier ideal, on the quotient. -/
def compactMultiplierOrder {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ) {c : ℝ}
    (hc : 0 < c) : PrimeOverCompact n X → ℕ :=
  Quot.lift (presentationMultiplierOrder hφ hc) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationMultiplierOrder_eq_of_commonResolution hφ hc h)

theorem compactMultiplierOrder_mk {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    {c : ℝ} (hc : 0 < c) (p : PrimePresentation n X) :
    compactMultiplierOrder hφ hc (Quot.mk commonResolutionRelation p) =
      presentationMultiplierOrder hφ hc p := rfl

/-- **Source `prop:Lelongnumfrommis`** on compact (possibly disconnected) complex manifolds:
`ν(φ, E) = lim_k (1/k) ord_E 𝓘(kφ)` for `φ ∈ PSH(X)` and every prime divisor `E` over `X`
(along `k = 1, 2, …`). -/
theorem tendsto_compactMultiplierOrder_ratio (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ)
    (E : PrimeOverCompact n X) :
    Tendsto (fun k : ℕ =>
      (compactMultiplierOrder (globalQPSH_of_sourcePSH hφ)
        (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) / (k + 1 : ℕ))
      atTop (𝓝 (compactSourcePSHReader φ hφ E)) := by
  refine Quot.inductionOn E ?_
  intro p
  exact tendsto_presentationMultiplierOrder_ratio (globalQPSH_of_sourcePSH hφ) p

/-- The same formula for quasi-psh input with local nondegeneracy. -/
theorem tendsto_compactMultiplierOrder_ratio_of_qpsh {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (E : PrimeOverCompact n X) :
    Tendsto (fun k : ℕ =>
      (compactMultiplierOrder hφ (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) /
        (k + 1 : ℕ)) atTop (𝓝 (compactReader φ hφ.1 E)) := by
  refine Quot.inductionOn E ?_
  intro p
  exact tendsto_presentationMultiplierOrder_ratio hφ p

end Compact

/-- For compact connected `X` the quotient is literally the earlier `DirectPrimeOver n X`, and the
readers agree. -/
theorem primeOverCompact_eq_directPrimeOver [CompactSpace X] [ConnectedSpace X] :
    PrimeOverCompact n X = DirectPrimeOver n X := rfl

theorem compactReader_eq_directReader [CompactSpace X] [ConnectedSpace X] (φ : X → EReal)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    (compactReader φ hφ : PrimeOverCompact n X → ℝ≥0∞) = directReader φ hφ := rfl

end SGPT.PSH.RIsoAPrimeOver
