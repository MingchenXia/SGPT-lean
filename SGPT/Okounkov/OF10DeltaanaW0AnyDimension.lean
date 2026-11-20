import SGPT.Okounkov.OF8DeltaanaW0General
import SGPT.Okounkov.EffectiveDivisorDimensionZero
import SGPT.Projective.OriginalModificationZeroPullback
import SGPT.PSH.NativeLogAnyDimension
import SGPT.PSH.AtlasLogComponentCartier

/-!
# `rmk:DeltaanaW0`: the log-resolution formula `eq:DeltaanaW0` in every dimension

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*
(`sec:PoB`), remark `rmk:DeltaanaW0`, second sentence:

> *If we take a modification `π : Y → X` such that `π^*φ` has log singularities along an
> effective `ℚ`-divisor `D` on `Y`, then* `Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`.  (`eq:DeltaanaW0`)

Lane OF8 proved the formula for `X` of dimension `n = m + 1 ≥ 1`
(`SGPT.Okounkov.OF8.partialBody_eq_logResolution`,
`SGPT.Okounkov.OF8.partialBody_eq_logResolutionBody`). The section `sec:PoB` works on a smooth
projective variety of arbitrary dimension `n`, the case `n = 0` included. This file states and
proves the formula **for every `n ≥ 0` in one statement**, with the same objects and hypotheses:

* `X` an integral smooth projective complex scheme of relative dimension `n` (closed projective
  embedding `E`), `L` a line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`;
* `φ ∈ PSH(X, θ)` with positive volume (the standing assumption of `sec:PoB`);
* `ν` an arbitrary surjective rank-`n` valuation of `ℂ(X)`, section values at its centre;
* `π : Y → X(ℂ)` a modification: a finite sequence of blow-ups with smooth centres
  (`IsBlowupSequence`, the book's convention, as in `prop:birinvO`);
* `D` an effective geometric `ℚ`-divisor on `Y` such that `π^*φ` has log singularities along
  `D` (book Definition 1.6.2 in every dimension: `NativeHasLogSingularitiesAlongAnyDimension`,
  which is *literally* OF8's `NativeHasLogSingularitiesAlong` in positive dimension,
  `SGPT.PSH.nativeHasLogSingularitiesAlongAnyDimension_succ_iff`).

## The any-dimensional objects

OF8's right-hand side is defined with the dimension `m + 1` built in. The definitions below are
the same definitions with the dimension a parameter `n`, and they *are* OF8's in positive
dimension:

* `IsPullbackIdealSectionAny` (`π^*s ∈ H⁰(Y, π^*M^k ⊗ 𝔞)`); `= OF8.IsPullbackIdealSection` for
  `n = m + 1` (`isPullbackIdealSectionAny_succ`, `Iff.rfl`);
* `pullbackDivisorValuesAny` (`Γ_ν(W)`, `W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))` read on `X`);
  `= OF8.pullbackDivisorValues` (`pullbackDivisorValuesAny_succ`, `rfl`);
* `IsCartierPresentationAny D F d`: `D = (1/d) F` coefficientwise along every prime divisor
  (`ord_P D = d⁻¹ ord_P F`), `↔ D = cartierGeometricQDivisor F (1/d)` in positive dimension
  (`isCartierPresentationAny_succ_iff`);
* `logResolutionBodyAny`, the right-hand side `Δ_ν(π^*L - D) + ν(D) = d⁻¹ Δ(Γ_ν(W))` for a
  presentation `D = (1/d) F`; `= OF8.logResolutionBody` in positive dimension
  (`logResolutionBodyAny_succ`).

## Main results

* `isPullbackMultiplierSection_iff_isPullbackIdealSectionAny`: at the levels `dk`,
  `π^*s ∈ 𝓘(dk π^*φ)` iff `π^*s ∈ 𝒪_Y(-kF)`, every dimension (positive dimension: OF8's `L²`
  Riemann-extension argument; dimension `0`: both ideals are `𝒪_Y`);
* **`partialBody_eq_logResolutionAny`** (`eq:DeltaanaW0`, every `n`, every presentation);
* `exists_cartier_presentationAny`, **`partialBody_eq_logResolutionBodyAny`** (presentation-free,
  every `n`).

The proof is OF8's, with the dimension a parameter: `prop:birinvO` in all dimensions
(`SGPT.Okounkov.OriginalBook.modification_partialBody_invariant_allDimensions`), the Veronese
invariance of the body of an almost semigroup (`SGPT.Okounkov.ValGen2.setBody_veroneseSet`) and
the identification of the multiplier ideals at the levels `dk`.
The dimension-`0` case is spelled out in `SGPT.Okounkov.OF10DeltaanaW0DimZero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF10

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class
open scoped Topology Manifold ContDiff Pointwise ENNReal

/-! ### `D = (1/d) F` in every dimension -/

section Presentation

variable {n : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **`D = (1/d) F`** for an effective geometric `ℚ`-divisor `D` and an effective (Cartier)
divisor `F` on `Z`, in every dimension: along every prime divisor `P` of `Z`,
`ord_P D = d⁻¹ ord_P F` (`nativeCartierCoefficientAny`, the order of `F` along `P`). In
positive dimension this is `D = cartierGeometricQDivisor F (1/d)`
(`isCartierPresentationAny_succ_iff`); in dimension `0` there are no prime divisors. -/
def IsCartierPresentationAny (D : EffectiveGeometricQDivisor n Z) (F : EffectiveDivisor n Z)
    (d : ℕ) : Prop :=
  ∀ Q : GeometricPrimeCarrier n Z,
    D.coefficient Q = (1 / (d : ℚ)) * (nativeCartierCoefficientAny F Q : ℚ)

/-- In positive dimension, `IsCartierPresentationAny` is OF8's presentation
`D = cartierGeometricQDivisor F (1/d)`. -/
theorem isCartierPresentationAny_succ_iff {m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (D : EffectiveGeometricQDivisor (m + 1) Y) (F : EffectiveDivisor (m + 1) Y) (d : ℕ) :
    IsCartierPresentationAny D F d ↔
      D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) := by
  constructor
  · intro h
    have hc : ∀ Q, D.coefficient Q =
        (cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)).coefficient Q := by
      intro Q
      rw [h Q, cartierGeometricQDivisor_coefficient]
      rfl
    have hext : ∀ {A B : EffectiveGeometricQDivisor (m + 1) Y},
        (∀ Q, A.coefficient Q = B.coefficient Q) → A = B := by
      intro A B h
      cases A
      cases B
      have h' := funext h
      cases h'
      rfl
    exact hext hc
  · rintro rfl Q
    rw [cartierGeometricQDivisor_coefficient]
    rfl

/-- In dimension `0` every `D` is `(1/d) F` (there are no prime divisors). -/
theorem isCartierPresentationAny_of_dim_zero {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    (D : EffectiveGeometricQDivisor 0 Y) (F : EffectiveDivisor 0 Y) (d : ℕ) :
    IsCartierPresentationAny D F d :=
  fun Q => isEmptyElim Q

/-- **Every effective `ℚ`-divisor on a compact complex manifold of any dimension is `(1/d) F`**
for an effective divisor `F` and `d > 0` (positive dimension:
`SGPT.Okounkov.OF8.exists_cartier_presentation`; dimension `0`: `d = 1`, `F = 0`). -/
theorem exists_cartier_presentationAny [CompactSpace Z] (D : EffectiveGeometricQDivisor n Z) :
    ∃ (d : ℕ) (F : EffectiveDivisor n Z), 0 < d ∧ IsCartierPresentationAny D F d := by
  cases n with
  | zero => exact ⟨1, 0, one_pos, isCartierPresentationAny_of_dim_zero D 0 1⟩
  | succ m =>
    obtain ⟨d, F, hd, h⟩ := OF8.exists_cartier_presentation D
    exact ⟨d, F, hd, (isCartierPresentationAny_succ_iff D F d).mpr h⟩

end Presentation

/-! ### The graded linear series `W` of `π^*L - D` in every dimension -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance of10Topology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of10Charts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of10Manifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

section Pullback

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- `π^*s ∈ H⁰(Z, π^*M^k ⊗ 𝔞)` in every dimension: in every local frame `α` of `M`, the pullback
along `π` of the coefficient of `s ∈ H⁰(X, M^k)` lies in the ideal sheaf `𝔞` of `Z` at every point
of the preimage of the frame domain. This is OF8's `IsPullbackIdealSection` with the dimension a
parameter (`isPullbackIdealSectionAny_succ`). -/
def IsPullbackIdealSectionAny (π : Z → SchemeComplexPoint f) (𝔞 : GermIdeal n Z)
    {M : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections M k) : Prop :=
  ∀ (U : X.Opens) (α : LocalBundleFrame M U) (z : Z),
    schemeComplexPointImage f (π z) ∈ U →
      𝔞.mem z (fun w => sectionFrameCoefficient f n E α k s (π w))

variable [IsIntegral X]

/-- **The values `Γ_ν(W)` of the graded linear series `W_k = H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))`**, read
on `X`, in every dimension:
`Γ_ν(W) = {(ν(s), k) : s ∈ H⁰(X, L^{dk}) \ {0}, π^*s ∈ H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))}`.
This is OF8's `pullbackDivisorValues` with the dimension a parameter
(`pullbackDivisorValuesAny_succ`). -/
def pullbackDivisorValuesAny (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (c : X) {L : X.Modules} (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f) (d : ℕ)
    (F : EffectiveDivisor n Z) : Set ((Fin n → ℤ) × ℤ) :=
  {z | ∃ (k : ℕ) (s : bundlePowerGlobalSections L (d * k)) (hs : s ≠ 0),
    IsPullbackIdealSectionAny f n E π (k • F).ideal (d * k) s ∧
      z = (sectionVector v c a (d * k) s hs, (k : ℤ))}

open Classical in
/-- **The right-hand side of `eq:DeltaanaW0`, `Δ_ν(π^*L - D) + ν(D)`**, in every dimension, in an
ambient admissible cone `C` (the book's is `C(Δ_ν(L))`): for a chosen presentation `D = (1/d) F`
(`IsCartierPresentationAny`), `d⁻¹ Δ(Γ_ν(W))` with `W_k = H⁰(Z, π^*L^{dk} ⊗ 𝒪_Z(-kF))`
(`pullbackDivisorValuesAny`), `Δ` taken in the Veronese cone `C^{(d)}`. This is OF8's
`logResolutionBody` with the dimension a parameter (`logResolutionBodyAny_succ`). -/
def logResolutionBodyAny (C : AdmissibleCone n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (c : X) {L : X.Modules} (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f)
    (D : EffectiveGeometricQDivisor n Z) : Set (EuclideanSpace ℝ (Fin n)) :=
  if h : ∃ (d : ℕ) (F : EffectiveDivisor n Z), 0 < d ∧ IsCartierPresentationAny D F d then
    ((h.choose : ℝ)⁻¹) • ValGen.setBody (ValGen2.veroneseCone C h.choose_spec.choose_spec.1)
      (pullbackDivisorValuesAny f n E v c a π h.choose h.choose_spec.choose)
  else ∅

end Pullback

/-! ### Agreement with OF8 in positive dimension -/

section Succ

variable {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

omit [IsComplexManifold (m + 1) Z] in
/-- In positive dimension `IsPullbackIdealSectionAny` is OF8's `IsPullbackIdealSection`. -/
theorem isPullbackIdealSectionAny_succ
    (π : Z → SchemeComplexPoint f) (𝔞 : GermIdeal (m + 1) Z) {M : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections M k) :
    IsPullbackIdealSectionAny f (m + 1) E π 𝔞 k s ↔ OF8.IsPullbackIdealSection f E π 𝔞 k s :=
  Iff.rfl

variable [IsIntegral X]

/-- In positive dimension `pullbackDivisorValuesAny` is OF8's `pullbackDivisorValues`. -/
theorem pullbackDivisorValuesAny_succ
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) (c : X) {L : X.Modules}
    (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f) (d : ℕ)
    (F : EffectiveDivisor (m + 1) Z) :
    pullbackDivisorValuesAny f (m + 1) E v c a π d F = OF8.pullbackDivisorValues f E v c a π d F :=
  rfl

private theorem choose_congr {α : Sort*} {P Q : α → Prop} (h : P = Q) (hp : ∃ x, P x)
    (hq : ∃ x, Q x) : hp.choose = hq.choose := by
  subst h
  rfl

/-- In positive dimension `logResolutionBodyAny` is OF8's `logResolutionBody`. -/
theorem logResolutionBodyAny_succ (C : AdmissibleCone (m + 1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) (c : X) {L : X.Modules}
    (a : LineBundleAtlas L) (π : Z → SchemeComplexPoint f)
    (D : EffectiveGeometricQDivisor (m + 1) Z) :
    logResolutionBodyAny f (m + 1) E C v c a π D = OF8.logResolutionBody f E C v c a π D := by
  have hP : (fun d : ℕ => ∃ F : EffectiveDivisor (m + 1) Z,
      0 < d ∧ IsCartierPresentationAny D F d) =
      (fun d : ℕ => ∃ F : EffectiveDivisor (m + 1) Z,
        0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)) := by
    funext d
    simp only [isCartierPresentationAny_succ_iff]
  unfold logResolutionBodyAny OF8.logResolutionBody
  by_cases h : ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z), 0 < d ∧ IsCartierPresentationAny D F d
  · have h' : ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z),
        0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) := by
      rw [← hP]
      exact h
    rw [dif_pos h, dif_pos h']
    have hd : h.choose = h'.choose := choose_congr hP h h'
    have hF : h.choose_spec.choose = h'.choose_spec.choose := by
      apply choose_congr _ h.choose_spec h'.choose_spec
      funext F
      rw [hd, isCartierPresentationAny_succ_iff]
    have key : ∀ (d₁ d₂ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (F₁ F₂ : EffectiveDivisor (m + 1) Z),
        d₁ = d₂ → F₁ = F₂ →
        ((d₁ : ℝ)⁻¹) • ValGen.setBody (ValGen2.veroneseCone C h₁)
            (pullbackDivisorValuesAny f (m + 1) E v c a π d₁ F₁) =
          ((d₂ : ℝ)⁻¹) • ValGen.setBody (ValGen2.veroneseCone C h₂)
            (OF8.pullbackDivisorValues f E v c a π d₂ F₂) := by
      rintro d₁ d₂ h₁ h₂ F₁ F₂ rfl rfl
      rfl
    exact key _ _ _ _ _ _ hd hF
  · have h' : ¬ ∃ (d : ℕ) (F : EffectiveDivisor (m + 1) Z),
        0 < d ∧ D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity) := by
      rw [← hP]
      exact h
    rw [dif_neg h, dif_neg h']

end Succ

/-! ### The formula in every dimension -/

section Formula

variable [IsIntegral X] {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

private theorem holomorphicAt_of_dim_zero' {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] (g : Y → ℂ) (z : Y) :
    HolomorphicAt 0 g z := by
  refine Eventually.of_forall fun y => ?_
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (fun _ : Y => g y) y :=
    mdifferentiableAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [(RooftopDimZero.isOpen_singleton_of_dim_zero rfl y).mem_nhds rfl] with w hw
  exact congrArg g (mem_singleton_iff.mp hw)

variable {f n E}

omit [IsIntegral X] in
/-- **At the levels `dk`, `π^*s ∈ 𝓘(dk π^*φ)` iff `π^*s ∈ 𝒪_Z(-kF)`**, in every dimension, for
`π^*φ` log singular along `D = (1/d) F`. Positive dimension: OF8
(`SGPT.Okounkov.OF8.isPullbackMultiplierSection_iff_isPullbackIdealSection`, `L²` Riemann
extension). Dimension `0`: `θ`-psh weights are finite, so `𝓘(dk π^*φ) = 𝒪_Z`
(`SGPT.Okounkov.OriginalModification.Zero.isPullbackMultiplierSection_all`), and every effective
divisor of a `0`-dimensional manifold is `0`, so `𝒪_Z(-kF) = 𝒪_Z`
(`SGPT.Okounkov.effectiveDivisor_ideal_eq_unit_of_dimension_zero`). -/
theorem isPullbackMultiplierSection_iff_isPullbackIdealSectionAny
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := n) π)
    {D : EffectiveGeometricQDivisor n Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z)))
    (F : EffectiveDivisor n Z) {d : ℕ} (hd : 0 < d) (hDF : IsCartierPresentationAny D F d)
    (k : ℕ) (s : bundlePowerGlobalSections L (d * k)) :
    OriginalModification.AllDimensions.IsPullbackMultiplierSection f n E π φ (d * k) s ↔
      IsPullbackIdealSectionAny f n E π (k • F).ideal (d * k) s := by
  let := E.isSeparated
  let := E.quasiCompact
  cases n with
  | zero =>
    refine iff_of_true
      (OriginalModification.Zero.isPullbackMultiplierSection_all f E a H hφ π (d * k) s) ?_
    intro U α z _
    rw [effectiveDivisor_ideal_eq_unit_of_dimension_zero (k • F)]
    exact holomorphicAt_of_dim_zero' _ z
  | succ m =>
    exact OF8.isPullbackMultiplierSection_iff_isPullbackIdealSection hπ hlog F hd
      ((isCartierPresentationAny_succ_iff D F d).mp hDF) k s

/-- **The Veronese subset of order `d` of `Γ_ν(π^*θ, π^*φ)` is `Γ_ν(W)`**, every dimension. -/
theorem veroneseSet_pullbackValues_eqAny
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := n) π)
    {D : EffectiveGeometricQDivisor n Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z)))
    (F : EffectiveDivisor n Z) {d : ℕ} (hd : 0 < d) (hDF : IsCartierPresentationAny D F d) :
    ValGen2.veroneseSet d (OriginalModification.AllDimensions.pullbackValues f n E a v c π φ) =
      pullbackDivisorValuesAny f n E v c a π d F := by
  ext ⟨x, j⟩
  rw [ValGen2.mem_veroneseSet]
  constructor
  · rintro ⟨k', s, hs, hP, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hx, hj⟩ := hz
    have hj0 : 0 ≤ j := by
      have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
      have : (0 : ℤ) ≤ (d : ℤ) * j := by rw [hj]; exact Nat.cast_nonneg _
      exact nonneg_of_mul_nonneg_right (by linarith) hdpos
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    have hk' : k' = d * k := by exact_mod_cast hj.symm
    subst hk'
    exact ⟨k, s, hs, (isPullbackMultiplierSection_iff_isPullbackIdealSectionAny a H hφ hπ hlog F
      hd hDF k s).mp hP, by rw [hx]⟩
  · rintro ⟨k, s, hs, hP, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hx, hj⟩ := hz
    subst hx hj
    exact ⟨d * k, s, hs,
      (isPullbackMultiplierSection_iff_isPullbackIdealSectionAny a H hφ hπ hlog F hd hDF k s).mpr
        hP, by simp⟩

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, in every dimension `n ≥ 0`.** Let `X` be an integral
smooth projective complex scheme of dimension `n`, `L` a line bundle with atlas and smooth metric
`H`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)` with positive volume (`sec:PoB`), `ν` a surjective rank-`n`
valuation (values at its centre), `π : Y → X` a modification (a finite sequence of blow-ups with
smooth centres) such that `π^*φ` has log singularities along the effective `ℚ`-divisor `D`, and
`D = (1/d) F` with `F` an effective divisor. Then `Δ_ν(θ, φ) = d⁻¹ Δ(Γ_ν(W))`,
`W_k = H⁰(Y, π^*L^{dk} ⊗ 𝒪_Y(-kF))`, i.e. `Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)`. The bodies are
taken in the book's cones: `C(Δ_ν(L))` on the left, its Veronese cone `C(Δ_ν(L^d))` on the right.
For `n = m + 1` this is `SGPT.Okounkov.OF8.partialBody_eq_logResolution`. -/
theorem partialBody_eq_logResolutionAny
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence n (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor n Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z)))
    (F : EffectiveDivisor n Z) {d : ℕ} (hd : 0 < d) (hDF : IsCartierPresentationAny D F d) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f n E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        ((d : ℝ)⁻¹) • ValGen.setBody
          (ValGen2.veroneseCone (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) hd)
          (pullbackDivisorValuesAny f n E v (valuationCenter f v) a π d F) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E
  have hπ := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  set c := valuationCenter f v with hcdef
  obtain ⟨hKc, hKv, hB⟩ :=
    OriginalBook.modification_partialBody_invariant_allDimensions f n E a H v hv hseq hφ hpos
  refine ⟨hKc, hKv, ?_⟩
  set C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv with hCdef
  set P := OriginalModification.AllDimensions.pullbackValues f n E a v c π φ with hPdef
  -- the partial body has positive volume, hence `P` is an almost semigroup in `C`
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f n E a H hφ hpos
  obtain ⟨hKc', hKv', hsub', hΓ', -, -, hvol⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f n E a H hbig v hv hφ hpos
  have hvol' : volume (ValGen.partialBody f n E v c a C φ) ≠ 0 := by
    have hv2 := hvol
    change volume (ValGen.partialBody f n E v c a C φ) = _ at hv2
    rw [hv2]
    exact (ENNReal.div_pos_iff.mpr ⟨hpos.ne', ENNReal.natCast_ne_top _⟩).ne'
  have hne : (ValGen.setBody C P).Nonempty := by
    rw [← hB] at hvol'
    exact nonempty_of_measure_ne_zero hvol'
  have hcond : ∃ hsub : P ⊆ (latticePoints C.cone : Set _),
      (⟨P, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C := by
    by_contra hno
    unfold ValGen.setBody at hne
    rw [dif_neg hno] at hne
    exact Set.not_nonempty_empty hne
  obtain ⟨hsub, hP⟩ := hcond
  have hver := ValGen2.setBody_veroneseSet hd hsub hP
  rw [veroneseSet_pullbackValues_eqAny a H v c hφ hπ hlog F hd hDF] at hver
  rw [hver, inv_smul_smul₀ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  exact hB.symm

/-- **Source `rmk:DeltaanaW0`, `eq:DeltaanaW0`, presentation-free form, every dimension `n ≥ 0`**:
for `φ ∈ PSH(X, θ)` with positive volume, a modification `π : Y → X` with `π^*φ` log singular
along the effective `ℚ`-divisor `D`, and every surjective rank-`n` valuation `ν` (values at its
centre), `Δ_ν(θ, φ) = Δ_ν(π^*L - D) + ν(D)` (`logResolutionBodyAny`, in the cone `C(Δ_ν(L))`).
For `n = m + 1` this is `SGPT.Okounkov.OF8.partialBody_eq_logResolutionBody`
(`logResolutionBodyAny_succ`). -/
theorem partialBody_eq_logResolutionBodyAny
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : Function.Surjective v) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : Nonempty (SchemeComplexPoint f) := OF8.nonempty_schemeComplexPoint f E;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    {π : Z → SchemeComplexPoint f}
    (hseq : letI := E.isSeparated; letI := E.quasiCompact;
      IsBlowupSequence n (SchemeComplexPoint f) Z π)
    {D : EffectiveGeometricQDivisor n Z}
    (hlog : NativeHasLogSingularitiesAlongAnyDimension D (fun z => φ (π z))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := E.isProper
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) a))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) a)),
      ValGen.partialBody f n E v (valuationCenter f v) a
          (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        logResolutionBodyAny f n E (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) v
          (valuationCenter f v) a π D := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  have hπ := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : CompactSpace Z := by
    refine ⟨?_⟩
    have h := hπ.2.1.isCompact_preimage (isCompact_univ (X := SchemeComplexPoint f))
    rwa [Set.preimage_univ] at h
  have hex : ∃ (d : ℕ) (F : EffectiveDivisor n Z), 0 < d ∧ IsCartierPresentationAny D F d :=
    exists_cartier_presentationAny D
  obtain ⟨hKc, hKv, hbody⟩ := partialBody_eq_logResolutionAny a H v hv hφ hpos hseq hlog
    hex.choose_spec.choose hex.choose_spec.choose_spec.1 hex.choose_spec.choose_spec.2
  refine ⟨hKc, hKv, ?_⟩
  rw [hbody, logResolutionBodyAny, dif_pos hex]

end Formula

end SGPT.Okounkov.OF10
