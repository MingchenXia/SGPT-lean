import SGPT.PSH.OriginalValuativeStalkCriterion
import SGPT.PSH.CompactPrimeLogDiscrepancy
import SGPT.PSH.RIsoAPrimeOver
import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder

/-!
# `thm:valuativemulti` in the book's terms: `ord_E(f)`, `ν(φ, E)` and `A_X(E)`

The positive-dimensional valuative criterion `SGPT.PSH.ActualGermValuative` is stated with three
independently named readers: the full-fibre/flattening order `LocalFibreReader.fibreOrder`, the
squared-log generic Lelong number `⨅ z ∈ E, squaredLogLelongNumber (φ ∘ π) z`, and the represented
log discrepancy `IntrinsicJacobianCoefficient.representedLogDiscrepancy`.  This file identifies them
with the book's quantities and restates the theorem with them.

* `vanishingOrderAlong E y g` : the order of vanishing of `g` along the smooth hypersurface `E` at
  `y`, the largest `k` with `g ∈ 𝓘_E^k` near `y` (ideal powers of the ideal sheaf of `E`, no
  coordinates); `germOrdE π E x F` : the book's `ord_E(f)` of a germ `f` at `x` for a prime divisor
  `E ⊆ Y` over `X`, `π : Y → X`: the order of vanishing of `π^* f` along `E`, read at the points of
  `E` over `x` (where the germ `π^* f` lives), i.e. the minimum of `vanishingOrderAlong E y (f ∘ π)`
  over `y ∈ E ∩ π⁻¹(x)`.  `germOrdE_eq_fibreOrder` : it equals the full-fibre/flattening order.
* `presentationReader_eq_iInf_squaredLog` : the squared-log reader is the book's generic Lelong
  number `ν(φ, E) = ν(π^*φ, E)` of `def:pshfunctions:L1112` (`squaredLogLelongNumber` is the book's
  normalisation, `def:pshfunctions:L1002`).
* `compactLogDiscrepancy` : the log discrepancy `A_X(E) = 1 + ord_E(K_{Y/X})` (Jacobian order), a
  class function on prime divisors over compact `X`.
* `mem_multiplierIdeal_iff_bookPrimeBound` : `thm:valuativemulti` (1) ⟺ (2) with `ord_E(f)`,
  `ν(φ, E)`, `A_X(E)` and all prime divisors `E` over `X` with `x` in the centre.

Blueprint: `claude-r-iso-a.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.RIsoAGermOrder

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci AnalyticModificationLocalDiscrepancy SquaredLogLelongSourceNormalization
  CompactPrimeOver CompactPrimeLogDiscrepancy VariableComplexAtlas ActualGermValuative

universe u

/-! ### The order of vanishing along a smooth hypersurface -/

section Order

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- The order of vanishing of `g` along `E` at `y`: the supremum of the `k` with `g ∈ 𝓘_E^k` at
`y` (`⊤` when `g` vanishes to infinite order, e.g. `g = 0` near `y`). -/
def vanishingOrderAlong (n : ℕ) {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (E : Set Z) (y : Z) (g : Z → ℂ) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : (IdealWeightPowers.idealPow (vanishingIdeal (n := n) E) k).mem y g),
    (k : ℕ∞)

/-- In any flattening of the smooth hypersurface `E` at `y` the order of vanishing is the
multiplicity of the defining equation. -/
theorem vanishingOrderAlong_eq_functionNormalOrder {E : Set Y} {y : Y}
    (Φ : DivisorFlattening (m := m) E y) (g : Y → ℂ) (hg : HolomorphicAt (m + 1) g y) :
    vanishingOrderAlong (m + 1) E y g = functionNormalOrder Φ g hg := by
  have hmem : ∀ k : ℕ, (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) E) k).mem y g ↔
      (k : ℕ∞) ≤ functionNormalOrder Φ g hg := by
    intro k
    rw [IdealPowerNormalOrder.mem_idealPow_iff_equation_pow_dvd Φ k g hg]
    exact pow_dvd_iff_le_emultiplicity
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  constructor
  · intro hk
    refine hk.trans (iSup₂_le fun j hj => ?_)
    exact (hmem j).mp hj
  · intro hk
    exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (IdealWeightPowers.idealPow
      (vanishingIdeal (n := m + 1) E) j).mem y g) => (j : ℕ∞)) k ((hmem k).mpr hk) le_rfl

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **The book's `ord_E(f)` for a germ.** For a prime divisor `E ⊆ Y` over `X` (`π : Y → X`) and
a germ `f` at `x`, the order of vanishing of `π^* f` along `E` at the points of `E` over `x`. -/
def germOrdE (n : ℕ) {Z W : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (π : Z → W) (E : Set Z) (x : W) (F : W → ℂ) : ℕ∞ :=
  ⨅ y : {y : Z // y ∈ E ∧ π y = x}, vanishingOrderAlong n E y.val (F ∘ π)

/-- `ord_E(f)` is the full-fibre/flattening order of `ActualGermValuative`. -/
theorem germOrdE_eq_fibreOrder {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {E : Set Y} (hE : IsClosedConnectedSubmanifold (m + 1) E m) (x : X) (F : X → ℂ)
    (hF : HolomorphicAt (m + 1) F x) :
    germOrdE (m + 1) π E x F = LocalFibreReader.fibreOrder hπ E x F hF := by
  unfold germOrdE LocalFibreReader.fibreOrder
  refine iInf_congr fun y => ?_
  have : Nonempty (DivisorFlattening (m := m) E y.val) :=
    DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y.val y.property.1)
  symm
  calc (⨅ Φ : DivisorFlattening (m := m) E y.val,
        pullbackNormalOrder hπ Φ F (by rw [y.property.2]; exact hF)) =
      ⨅ _ : DivisorFlattening (m := m) E y.val, vanishingOrderAlong (m + 1) E y.val (F ∘ π) :=
        iInf_congr fun Φ => (vanishingOrderAlong_eq_functionNormalOrder Φ _ _).symm
    _ = vanishingOrderAlong (m + 1) E y.val (F ∘ π) := iInf_const

/-- `ord_E(f)` only depends on the germ of `f` at `x`. -/
theorem germOrdE_congr {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {E : Set Y} (hE : IsClosedConnectedSubmanifold (m + 1) E m) (x : X) {F G : X → ℂ}
    (hF : HolomorphicAt (m + 1) F x) (hG : HolomorphicAt (m + 1) G x) (hFG : F =ᶠ[𝓝 x] G) :
    germOrdE (m + 1) π E x F = germOrdE (m + 1) π E x G := by
  rw [germOrdE_eq_fibreOrder hπ hE x F hF, germOrdE_eq_fibreOrder hπ hE x G hG]
  exact LocalFibreReader.fibreOrder_congr hπ E x hF hG hFG

end Order

/-! ### The book's form of `thm:valuativemulti` -/

section Book

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- `ord_E(g)` for an element `g` of the actual stalk `𝒪_{X,x}`, read on a representative. -/
def stalkOrdE (p : PrimePresentation (m + 1) X) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) : ℕ∞ :=
  germOrdE (m + 1) p.projection p.divisor x (Classical.choose (exists_original_representative x g))

private theorem smooth_hypersurface (p : PrimePresentation (m + 1) X) :
    IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
  have hdim : p.divisorDimension = m := by
    have h := p.codimension_one
    omega
  simpa only [hdim] using p.smooth

/-- `ord_E(g)` is the order of EVERY representative of `g`, and the actual germ fibre order. -/
theorem stalkOrdE_eq (p : PrimePresentation (m + 1) X) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hFg : actualOriginalFunctionGerm x F hF = g) :
    stalkOrdE p x g = germOrdE (m + 1) p.projection p.divisor x F ∧
      stalkOrdE p x g = actualGermFibreOrder p.modification p.divisor x g := by
  obtain ⟨hF₀, hFg₀⟩ := Classical.choose_spec (exists_original_representative x g)
  have hE := smooth_hypersurface p
  have h₀ : stalkOrdE p x g = actualGermFibreOrder p.modification p.divisor x g := by
    rw [stalkOrdE, germOrdE_eq_fibreOrder p.modification hE x _ hF₀,
      actualGermFibreOrder_eq_original p.modification p.divisor x g _ hF₀ hFg₀]
  refine ⟨?_, h₀⟩
  rw [h₀, actualGermFibreOrder_eq_original p.modification p.divisor x g F hF hFg,
    germOrdE_eq_fibreOrder p.modification hE x F hF]

/-- The squared-log generic reader is the book's `ν(φ, E) = ν(π^*φ, E)`
(`def:pshfunctions:L1112`). -/
theorem presentationReader_eq_iInf_squaredLog {n : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] (φ : Z → EReal)
    (p : PrimePresentation n Z) :
    presentationReader φ p =
      ⨅ z ∈ p.divisor, squaredLogLelongNumber (n := n) (φ ∘ p.projection) z := by
  simp only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq]

/-- **Source `thm:valuativemulti` (2)**, in the book's terms: one `ε` for all prime divisors `E`
over `X` with `x` in the centre of `E`, `ord_E(g) ≥ (1 + ε) ν(φ, E) - A_X(E)`, i.e.
`(1 + ε) ν(φ, E) ≤ ord_E(g) + A_X(E)` (`A_X(E) = 1 + ord_E(K_{Y/X})`). -/
def BookPrimeBound (φ : X → EReal) (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    (ε : ℝ) : Prop :=
  ∀ p : PrimePresentation (m + 1) X, x ∈ presentationCenter p →
    ENNReal.ofReal (1 + ε) * presentationReader φ p ≤
      extendedOrderValue (stalkOrdE p x g) + (presentationLogDiscrepancy p : ℝ≥0∞)

/-- The book's condition is the condition of `ActualGermValuative`. -/
theorem bookPrimeBound_iff (φ : X → EReal) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) (ε : ℝ) :
    BookPrimeBound φ x g ε ↔ ActualGermUniformPrimeBound (m := m) φ x g ε := by
  constructor
  · intro h Y _ _ _ π hπ E hE hx
    let p : PrimePresentation (m + 1) X :=
      ⟨BlowupTowers.CMfd.of (n := m + 1) Y, π, hπ, E, m, hE, rfl⟩
    have hp := h p hx
    rw [presentationReader_eq_iInf_squaredLog, (stalkOrdE_eq p x g _
      (Classical.choose_spec (exists_original_representative x g)).1
      (Classical.choose_spec (exists_original_representative x g)).2).2] at hp
    exact hp
  · intro h p hx
    have hp := h p.model p.projection p.modification p.divisor (smooth_hypersurface p) hx
    rw [presentationReader_eq_iInf_squaredLog, (stalkOrdE_eq p x g _
      (Classical.choose_spec (exists_original_representative x g)).1
      (Classical.choose_spec (exists_original_representative x g)).2).2]
    exact hp

/-- **Source `thm:valuativemulti`, (1) ⟺ (2)**, positive dimension, in the book's terms: for `φ`
quasi-psh on `X`, `x ∈ X` and `g ∈ 𝒪_{X,x}`, `g ∈ 𝓘(φ)_x` iff there is `ε > 0` with
`ord_E(g) ≥ (1 + ε) ν(φ, E) - A_X(E)` for every prime divisor `E` over `X` whose centre contains
`x`. -/
theorem mem_multiplierIdeal_iff_bookPrimeBound {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x ↔
      ∃ ε : ℝ, 0 < ε ∧ BookPrimeBound φ x g ε := by
  simp only [bookPrimeBound_iff]
  constructor
  · exact exists_uniform_all_prime_bound_of_original_stalk_membership hφ x g
  · rintro ⟨ε, hε, h⟩
    exact (original_stalk_multiplier_membership hφ x g hε h).1

end Book

/-! ### `A_X(E)` on prime divisors over compact manifolds -/

section Compact

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- The log discrepancy `A_X(E) = 1 + ord_E(K_{Y/X})` as a function of the prime divisor `E` over
a compact (possibly disconnected) complex manifold. -/
def compactLogDiscrepancy : RIsoAPrimeOver.PrimeOverCompact n X → ℕ :=
  Quot.lift presentationLogDiscrepancy (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationLogDiscrepancy_eq_of_commonResolution h)

theorem compactLogDiscrepancy_mk (p : PrimePresentation n X) :
    compactLogDiscrepancy (Quot.mk commonResolutionRelation p) = presentationLogDiscrepancy p :=
  rfl

end Compact

end SGPT.PSH.RIsoAGermOrder
