import SGPT.PSH.CompactPrimeMultiplierLimit
import SGPT.Okounkov.AlgebraicValuationBodies

/-!
# The order of vanishing of a section along a prime divisor over `X`

Source: chapter *The theory of Okounkov bodies*, subsection *Recover Lelong numbers from partial
Okounkov bodies* (`thm:nuOk`, `cor:numin`): for a prime divisor `E` over `X` (source
`def:primdiv`: a connected smooth hypersurface `E ⊆ Y` of a resolution `π : Y → X`) and a section
`s` of a line bundle on `X`, `ord_E(s)` is the order of vanishing of `π^* s` along `E`, and
`ord_E H⁰(X, L^k ⊗ 𝓘(kφ)) = min_s ord_E(s)`.

Setting: `X` an integral smooth projective complex scheme of dimension `m + 1`, `X(ℂ)` its
analytic manifold; a prime divisor over `X` is a `SGPT.PSH.CompactPrimeOver.PrimePresentation`
of `X(ℂ)` (model `π : Y → X(ℂ)`, an analytic modification, and `E ⊆ Y` a closed connected
submanifold of dimension `m`).

## Main definitions and results

* `sectionDivisorOrder f E p s`: `ord_E(s) ∈ ℕ∞` for a global section `s` of an arbitrary line
  bundle `M` on `X`, the infimum over the points `y ∈ E` and the local frames of `M` near
  `π(y)` of the order of vanishing along `E` at `y` of the pulled-back frame coefficient
  (`SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder.pullbackNormalOrder`).
* `originalStalkNormalOrder_le_functionNormalOrder`, `le_pullbackNormalOrder_of_isInSpanAt`: the
  order of a member of an ideal is at least the order of the ideal; the order of a holomorphic
  combination of functions is at least the minimum of their orders.
* `presentationMultiplierOrder_eq_originalStalkNormalOrder`: the order `ord_E 𝓘(cφ)` of
  `prop:Lelongnumfrommis` is read at every point of `E`.
* **`presentationMultiplierOrder_le_sectionDivisorOrder`**: every nonzero
  `s ∈ H⁰(X, M ⊗ 𝓘(cφ))` has `ord_E(s) ≥ ord_E 𝓘(cφ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF3

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder

universe u

/-! ### Normal orders of members and of holomorphic combinations -/

section Local

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] {E : Set Y} {y : Y}

/-- The order along `E` of a member of an ideal is at least the order of the ideal. -/
theorem originalStalkNormalOrder_le_functionNormalOrder (Φ : DivisorFlattening (m := m) E y)
    {A : GermIdeal (m + 1) Y} {g : Y → ℂ} (hA : A.mem y g) (hg : HolomorphicAt (m + 1) g y) :
    originalStalkNormalOrder Φ A ≤ functionNormalOrder Φ g hg := by
  unfold originalStalkNormalOrder functionNormalOrder idealNormalOrder
  exact iInf_le_of_le ⟨chartTranslatedGerm y y (mem_chart_source _ y) g hg,
    Ideal.subset_span ⟨g, hg, hA, rfl⟩⟩ le_rfl

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **The order of a holomorphic combination.** If the germ of `F` at `π(y)` is a holomorphic
combination of functions `h ∈ S`, each holomorphic at `π(y)` with pulled-back order along `E` at
least `N`, then the pulled-back order of `F` along `E` at `y` is at least `N`. -/
theorem le_pullbackNormalOrder_of_isInSpanAt {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (Φ : DivisorFlattening (m := m) E y)
    {S : (X → ℂ) → Prop} {F : X → ℂ} (hF : IsInSpanAt (n := m + 1) S (π y) F)
    (hFh : HolomorphicAt (m + 1) F (π y)) {N : ℕ∞}
    (hS : ∀ h, S h → ∃ hh : HolomorphicAt (m + 1) h (π y), N ≤ pullbackNormalOrder hπ Φ h hh) :
    N ≤ pullbackNormalOrder hπ Φ F hFh := by
  obtain ⟨-, K, s, c, hs, hc, heq⟩ := hF
  have hsh : ∀ i, HolomorphicAt (m + 1) (s i) (π y) := fun i => (hS _ (hs i)).1
  let G : Fin K → Y → ℂ := fun i => s i ∘ π
  have hG : ∀ i, HolomorphicAt (m + 1) (G i) y := fun i =>
    (hsh i).comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  let A : GermIdeal (m + 1) Y := ⟨fun z g => IsInSpanAt (n := m + 1) (· ∈ range G) z g⟩
  have hA := originalStalkNormalOrder_eq_generators Φ A G hG (fun _ => Iff.rfl)
  have hFπ : HolomorphicAt (m + 1) (F ∘ π) y :=
    hFh.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hmem : A.mem y (F ∘ π) := by
    refine ⟨hFπ, K, G, fun i => c i ∘ π, fun i => mem_range_self i,
      fun i => (hc i).comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt), ?_⟩
    exact hπ.1.continuous.continuousAt.tendsto.eventually heq
  have hle := originalStalkNormalOrder_le_functionNormalOrder Φ hmem hFπ
  rw [hA] at hle
  refine le_trans (le_iInf fun i => ?_) hle
  obtain ⟨hh, hN⟩ := hS _ (hs i)
  exact hN

end Local

/-! ### Orders of multiplier ideals along a prime divisor over `X` -/

section Presentation

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- The divisor of a prime divisor over `X` is a closed connected submanifold of dimension
`m` of the model. -/
theorem isClosedConnectedSubmanifold_divisor (p : PrimePresentation (m + 1) X) :
    IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
  have hdim : p.divisorDimension = m := by
    have h := p.codimension_one
    omega
  simpa only [hdim] using p.smooth

/-- **`ord_E 𝓘(cφ)` is read at every point of `E`** (`prop:Lelongnumfrommis`): the order of the
pulled-back multiplier ideal along `E`, in any flattening of `E` at any point `y ∈ E`. -/
theorem presentationMultiplierOrder_eq_originalStalkNormalOrder {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) {c : ℝ} (hc : 0 < c)
    (p : PrimePresentation (m + 1) X) {y : p.model} (hy : y ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor y) :
    (presentationMultiplierOrder hφ hc p : ℕ∞) =
      originalStalkNormalOrder Φ
        (GermIdeal.pullback (m := m + 1) p.projection (multiplierIdeal (n := m + 1) c φ)) :=
  (MultiplierIdealLowerBound.originalStalkNormalOrder_eq_actualMultiplierCoefficient
    p.modification (isClosedConnectedSubmanifold_divisor p) hφ hc y hy Φ).symm

/-- A member of an ideal pulls back into the pulled-back ideal. -/
theorem mem_pullback_comp {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X} {y : Y} {𝔞 : GermIdeal (m + 1) X} {g : X → ℂ}
    (hπ : IsAnalyticModification (n := m + 1) π) (hg : 𝔞.mem (π y) g)
    (hgh : HolomorphicAt (m + 1) g (π y)) :
    (GermIdeal.pullback (m := m + 1) π 𝔞).mem y (g ∘ π) := by
  refine ⟨hgh.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt), 1,
    fun _ => g ∘ π, fun _ _ => 1, fun _ => ⟨g, hg, rfl⟩, fun _ => holomorphicAt_const 1, ?_⟩
  exact Eventually.of_forall fun z => by simp

end Presentation

/-! ### The scheme setting -/

section Scheme

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of3OrderTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of3OrderCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of3OrderManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **`ord_E(s)`**, the order of vanishing along a prime divisor `E ⊆ Y` over `X` (presented by
`π : Y → X(ℂ)`) of a global section `s` of a line bundle `M` on `X`: the infimum, over the points
`y ∈ E`, the local frames `β` of `M` on Zariski opens `U ∋ π(y)` and the flattenings of `E` at
`y`, of the order along `E` at `y` of `π^*` of the coefficient of `s` in `β`. (Frame changes are
units and the order of a section is constant along the connected `E`, so this is the order of
`π^* s` along `E` at any of its points; it is `⊤` exactly for the zero section.) -/
def sectionDivisorOrder (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {M : X.Modules}
    (s : bundleSections M ⊤) : ℕ∞ :=
  ⨅ (y : p.model) (_ : y ∈ p.divisor) (U : X.Opens) (β : LocalBundleFrame M U)
    (hU : schemeComplexPointImage f (p.projection y) ∈ U)
    (Φ : DivisorFlattening (m := m) p.divisor y),
    pullbackNormalOrder p.modification Φ
      (schemeOpenRegularFunction f (m + 1) E U
        (β.coefficients (𝟙 U) (M.val.map (homOfLE le_top).op s)))
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ _ hU)

/-- `ord_E(s)` is at most the order read at one point, frame and flattening. -/
theorem sectionDivisorOrder_le (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    {M : X.Modules} (s : bundleSections M ⊤) {y : p.model} (hy : y ∈ p.divisor) {U : X.Opens}
    (β : LocalBundleFrame M U) (hU : schemeComplexPointImage f (p.projection y) ∈ U)
    (Φ : DivisorFlattening (m := m) p.divisor y) :
    sectionDivisorOrder f E p s ≤ pullbackNormalOrder p.modification Φ
      (schemeOpenRegularFunction f (m + 1) E U
        (β.coefficients (𝟙 U) (M.val.map (homOfLE le_top).op s)))
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ _ hU) :=
  iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le U (iInf_le_of_le β
    (iInf_le_of_le hU (iInf_le_of_le Φ le_rfl)))))

/-- **Sections of `M ⊗ 𝓘(cφ)` vanish to order at least `ord_E 𝓘(cφ)` along `E`**: for every
section `s` of a line bundle `M` whose coefficients lie in `𝓘(cφ)` in every local frame,
`ord_E 𝓘(cφ) ≤ ord_E(s)`. -/
theorem presentationMultiplierOrder_le_sectionDivisorOrder {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) {c : ℝ} (hc : 0 < c)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {M : X.Modules}
    {s : bundleSections M ⊤}
    (hs : AlgebraicValuation.IsPlainIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) c φ) s) :
    (presentationMultiplierOrder hφ hc p : ℕ∞) ≤ sectionDivisorOrder f E p s := by
  refine le_iInf fun y => le_iInf fun hy => le_iInf fun U => le_iInf fun β => le_iInf fun hU =>
    le_iInf fun Φ => ?_
  have hhol := schemeOpenRegularFunction_holomorphicAt f (m + 1) E U
    (β.coefficients (𝟙 U) (M.val.map (homOfLE le_top).op s)) _ hU
  have hmem := hs U β (p.projection y) hU
  rw [presentationMultiplierOrder_eq_originalStalkNormalOrder hφ hc p hy Φ]
  exact originalStalkNormalOrder_le_functionNormalOrder Φ
    (mem_pullback_comp p.modification hmem hhol) _

end Scheme

end SGPT.Okounkov.OF3
