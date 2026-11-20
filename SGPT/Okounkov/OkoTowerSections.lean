import SGPT.Okounkov.OkoTowerDescent
import SGPT.Okounkov.AlgPOBComparison

/-!
# Multiplier sections of a pulled-back line bundle on a modification

Lane OKO-TOWER, blueprint `claude-oko-tower.tex`, nodes `claude-oko-tower:sections`,
`claude-oko-tower:body`.  Source: chapter *The theory of Okounkov bodies*, `prop:birinvO`:
*let `π : Y → X` be a modification; then `Δ_ν(π^*L, π^*h) = Δ_ν(L, h)`.*

Setting of lanes OKO-A / H0-GAGA3 / OKO-CLOSE: `X` an integral smooth projective complex scheme of
dimension `m + 1`, `X(ℂ)` its complex manifold, `Y•` a smooth flag of `X(ℂ)` (`ν = ν_{Y•}`), `L` a
line bundle with atlas `a`, `θ = c₁(L, h₀)`, `h = h₀ e^{-φ}`.  A modification is a holomorphic map
`π : Z → X(ℂ)` from a complex manifold of the same dimension (an analytic modification; the
book's modifications, finite sequences of blow-ups with smooth centres, are such maps).

The section spaces of `Δ_ν(π^*L, π^*h)` are `H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`; since `π_* 𝒪_Z = 𝒪_X`
every section of `π^*L^k` is the pullback `π^*s` of a unique `s ∈ H⁰(X, L^k)`
(`SGPT.Okounkov.OkoTower.exists_pullback_eq` in `OkoTowerDX`), and the valuation `ν` of
`ℂ(Z) = ℂ(X)` takes the value `ν(s)` on `π^*s`.  In a local frame `α` of `L` on `U`, `π^*α` is a
frame of `π^*L` on `π⁻¹(U)` and the coefficient of `π^*s` in `(π^*α)^k` is `s_α ∘ π`, where
`s_α` is the coefficient of `s` in `α^k`.  Hence:

* `IsPullbackMultiplierSection π φ k s`: `π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`, i.e. in every local
  frame `α` of `L`, `s_α ∘ π ∈ 𝓘(k (φ ∘ π))` at every point of `π⁻¹(U)` (`k = 0`: no condition).
* `pullbackMultiplierSubmodule`: these sections form a subspace of `H⁰(X, L^k)`.
* `pullbackMultiplierSectionSet`: `Γ(π^*θ, π^*φ) = {(ν(π^*s), k)}`;
  `pullbackPartialOkounkovBody`: `Δ_ν(π^*L, π^*h) = Δ(Γ(π^*θ, π^*φ))` (as `partialOkounkovBody`,
  relative to an admissible cone, junk value `∅` off the almost-semigroup locus).
* **`isMultiplierSection_of_isPullbackMultiplierSection`** (descent, `π_* 𝓘(k π^*φ) ⊆ 𝓘(kφ)`):
  `π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ)) ⇒ s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`; hence
  `Γ(π^*θ, π^*φ) ⊆ Γ(θ, φ)` (`pullbackMultiplierSectionSet_subset`).
* `card_slice_pullbackMultiplierSectionSet`: `#Γ_k(π^*θ, π^*φ) = h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.OkoTower

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov SGPT.LineBundle SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f]

local instance okoTowerSecTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTowerSecCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoTowerSecManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-! ### Multiplier sections of the pulled-back bundle -/

variable (m) in
/-- **`π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`**: in every local frame `α` of `L` on `U`, the
coefficient `s_α ∘ π` of `π^*s` in the pulled-back frame `(π^*α)^k` lies in `𝓘(k (φ ∘ π))` at
every point of `π⁻¹(U)` (source convention `𝓘(0 · π^*φ) = 𝒪_Z`). -/
def IsPullbackMultiplierSection (π : Z → SchemeComplexPoint f) (φ : SchemeComplexPoint f → EReal)
    {L : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections L k) : Prop :=
  k = 0 ∨ ∀ (U : X.Opens) (α : LocalBundleFrame L U) (z : Z),
    schemeComplexPointImage f (π z) ∈ U →
      (multiplierIdeal (n := m + 1) (k : ℝ) (fun w => φ (π w))).mem z
        (fun w => sectionFrameCoefficient f (m + 1) E α k s (π w))

/-- The preimage under a continuous map of the frame domain is a neighbourhood. -/
theorem preimage_frameDomain_mem_nhds {π : Z → SchemeComplexPoint f} (hπc : Continuous π)
    (U : X.Opens) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ U) :
    π ⁻¹' (schemeComplexPointImage f ⁻¹' U) ∈ 𝓝 z :=
  ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).preimage hπc).mem_nhds hz

/-- **Descent** (`π_* 𝓘(k π^*φ) ⊆ 𝓘(kφ)`): if `π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))` then
`s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem isMultiplierSection_of_isPullbackMultiplierSection {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    {L : X.Modules} {k : ℕ} {s : bundlePowerGlobalSections L k}
    (hs : IsPullbackMultiplierSection f E m π φ k s) :
    IsMultiplierSection f (m + 1) E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases hs with h0 | hs
  · exact Or.inl h0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α p hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine multiplierIdeal_mem_of_forall_comp_mem hπ hφ hkR
    (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ p hp) fun z hz => ?_
  exact hs U α z (by rw [hz]; exact hp)

/-- `𝓘(c (φ ∘ π))` contains `0`. -/
theorem multiplierIdeal_mem_zero {u : Z → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u) {c : ℝ} (hc : 0 < c) (z : Z) :
    (multiplierIdeal (n := m + 1) c u).mem z (fun _ => (0 : ℂ)) := by
  have h := MultiplierIdealProductComparison.mem_multiplierIdeal_sum hu hc (x := z)
    (∅ : Finset Bool) (F := fun _ _ => (0 : ℂ)) (by simp)
  simpa using h

/-- `𝓘(c u)` is closed under addition. -/
theorem multiplierIdeal_mem_add {u : Z → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u) {c : ℝ} (hc : 0 < c) {z : Z}
    {g h : Z → ℂ} (hg : (multiplierIdeal (n := m + 1) c u).mem z g)
    (hh : (multiplierIdeal (n := m + 1) c u).mem z h) :
    (multiplierIdeal (n := m + 1) c u).mem z (fun w => g w + h w) := by
  have hs := MultiplierIdealProductComparison.mem_multiplierIdeal_sum hu hc (x := z)
    (Finset.univ : Finset Bool) (F := fun b => if b then g else h)
    (by intro b _; cases b <;> simpa)
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr hs
    (Eventually.of_forall fun w => ?_)
  simp

variable {f E}

theorem isPullbackMultiplierSection_zero {π : Z → SchemeComplexPoint f}
    (hπc : Continuous π) {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w)))
    {L : X.Modules} (k : ℕ) :
    IsPullbackMultiplierSection f E m π φ k (0 : bundlePowerGlobalSections L k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α z hz
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr
    (multiplierIdeal_mem_zero hφ hkR z) ?_
  filter_upwards [preimage_frameDomain_mem_nhds f hπc U hz] with w hw
  exact (SGPT.IGood.sectionFrameCoefficient_zero (f := f) (n := m + 1) (E := E) α k hw).symm

theorem isPullbackMultiplierSection_add {π : Z → SchemeComplexPoint f}
    (hπc : Continuous π) {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w)))
    {L : X.Modules} {k : ℕ} {s t : bundlePowerGlobalSections L k}
    (hs : IsPullbackMultiplierSection f E m π φ k s)
    (ht : IsPullbackMultiplierSection f E m π φ k t) :
    IsPullbackMultiplierSection f E m π φ k (s + t) := by
  rcases hs with h0 | hs
  · exact Or.inl h0
  rcases ht with h0 | ht
  · exact Or.inl h0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α z hz
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr
    (multiplierIdeal_mem_add hφ hkR (hs U α z hz) (ht U α z hz)) ?_
  filter_upwards [preimage_frameDomain_mem_nhds f hπc U hz] with w hw
  exact (SGPT.IGood.DXMain.sectionFrameCoefficient_add f (m + 1) E α k s t hw).symm

theorem isPullbackMultiplierSection_smul {π : Z → SchemeComplexPoint f}
    (hπc : Continuous π) {φ : SchemeComplexPoint f → EReal}
    {L : X.Modules} {k : ℕ} (c : ℂ) {s : SectionSpace f L k}
    (hs : IsPullbackMultiplierSection f E m π φ k s) :
    IsPullbackMultiplierSection f E m π φ k (c • s : SectionSpace f L k) := by
  rcases hs with h0 | hs
  · exact Or.inl h0
  right
  intro U α z hz
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr
    (MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul
      (a := fun _ => c) (holomorphicAt_const (n := m + 1) c) (hs U α z hz)) ?_
  filter_upwards [preimage_frameDomain_mem_nhds f hπc U hz] with w hw
  exact (SGPT.IGood.DXMain.sectionFrameCoefficient_smul f (m + 1) E α k c s hw).symm

variable (f E)

/-- **`H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`**, as the subspace of `H⁰(X, L^k)` of the sections `s` with
`π^*s` in it. -/
def pullbackMultiplierSubmodule {π : Z → SchemeComplexPoint f} (hπc : Continuous π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w)))
    (L : X.Modules) (k : ℕ) : Submodule ℂ (SectionSpace f L k) where
  carrier := {s | IsPullbackMultiplierSection f E m π φ k s}
  zero_mem' := isPullbackMultiplierSection_zero hπc hφ k
  add_mem' := fun hs ht => isPullbackMultiplierSection_add hπc hφ hs ht
  smul_mem' := fun c _ hs => isPullbackMultiplierSection_smul hπc c hs

theorem mem_pullbackMultiplierSubmodule {π : Z → SchemeComplexPoint f} (hπc : Continuous π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w)))
    (L : X.Modules) (k : ℕ) (s : SectionSpace f L k) :
    s ∈ pullbackMultiplierSubmodule f E hπc hφ L k ↔ IsPullbackMultiplierSection f E m π φ k s :=
  Iff.rfl

/-! ### The section set and the partial Okounkov body on the modification -/

variable [IsIntegral X] (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L)

/-- **`Γ(π^*θ, π^*φ) = {(ν(π^*s), k) : k ∈ ℕ, π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ)) \ {0}}`**
(`def:Okounkov:L484` on the modification, for the valuation `ν = ν_{Y•}` of `ℂ(Z) = ℂ(X)`). -/
def pullbackMultiplierSectionSet (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal) : Set ((Fin (m + 1) → ℤ) × ℤ) :=
  sectionValueSet f (m + 1) E Y hY a fun k s => IsPullbackMultiplierSection f E m π φ k s

/-- **`Γ(π^*θ, π^*φ) ⊆ Γ(θ, φ)`** (descent of multiplier sections). -/
theorem pullbackMultiplierSectionSet_subset {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ) :
    pullbackMultiplierSectionSet f E Y hY a π φ ⊆ multiplierSectionSet f (m + 1) E Y hY a φ :=
  sectionValueSet_mono a fun _ _ hs =>
    isMultiplierSection_of_isPullbackMultiplierSection f E hπ hφ hs

/-- The degree-`k` slice of `Γ(π^*θ, π^*φ)`. -/
theorem mem_slice_pullbackMultiplierSectionSet (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) (x : Fin (m + 1) → ℤ) :
    x ∈ slice (pullbackMultiplierSectionSet f E Y hY a π φ) (k : ℤ) ↔
      ∃ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0), IsPullbackMultiplierSection f E m π φ k s ∧
        x = fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℤ) := by
  constructor
  · rintro ⟨k', s, hs, hP, hz⟩
    have hk : k' = k := by
      have h2 := congrArg Prod.snd hz
      simp only at h2
      exact_mod_cast h2.symm
    subst hk
    exact ⟨s, hs, hP, congrArg Prod.fst hz⟩
  · rintro ⟨s, hs, hP, rfl⟩
    exact ⟨k, s, hs, hP, rfl⟩

/-- **`#Γ_k(π^*θ, π^*φ) = h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`** (one-dimensional leaves). -/
theorem card_slice_pullbackMultiplierSectionSet {π : Z → SchemeComplexPoint f}
    (hπc : Continuous π) {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w))) (k : ℕ) :
    Nat.card (slice (pullbackMultiplierSectionSet f E Y hY a π φ) (k : ℤ)) =
      Module.finrank ℂ (pullbackMultiplierSubmodule f E hπc hφ L k) := by
  rw [← SGPT.IGood.DXMain.card_sectionValues_eq_finrank f (m + 1) E Y hY a k
    (pullbackMultiplierSubmodule f E hπc hφ L k)]
  have hset : slice (pullbackMultiplierSectionSet f E Y hY a π φ) (k : ℤ) =
      (fun v : Fin (m + 1) → ℕ => fun i => (v i : ℤ)) ''
        SGPT.IGood.DXMain.sectionValues f (m + 1) E Y hY a k
          (pullbackMultiplierSubmodule f E hπc hφ L k) := by
    ext x
    rw [mem_slice_pullbackMultiplierSectionSet]
    constructor
    · rintro ⟨s, hs, hP, rfl⟩
      exact ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
      exact ⟨s, hs, hP, rfl⟩
  rw [hset]
  refine Nat.card_image_of_injective (fun v w hvw => ?_) _
  funext i
  exact_mod_cast congrFun hvw i

open Classical in
/-- **Source `prop:birinvO`, left-hand side**: the partial Okounkov body
`Δ_ν(π^*L, π^*h) = Δ(Γ(π^*θ, π^*φ))` of the pulled-back Hermitian line bundle on the
modification `π : Z → X(ℂ)`, for the valuation `ν = ν_{Y•}` (relative to an admissible ambient
cone `C`, as `SGPT.Okounkov.partialOkounkovBody`; junk value `∅` off the almost-semigroup
locus). -/
def pullbackPartialOkounkovBody (C : AdmissibleCone (m + 1)) (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  if h : ∃ hsub : pullbackMultiplierSectionSet f E Y hY a π φ ⊆ (latticePoints C.cone : Set _),
      (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C then
    (bodyExtension (⟨⟨_, h.1⟩, h.2⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin (m + 1))))
  else ∅

/-- The value of `Δ_ν(π^*L, π^*h)` on an almost semigroup. -/
theorem pullbackPartialOkounkovBody_eq {C : AdmissibleCone (m + 1)} (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal)
    (hsub : pullbackMultiplierSectionSet f E Y hY a π φ ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    pullbackPartialOkounkovBody f E Y hY a C π φ =
      (bodyExtension (⟨⟨_, hsub⟩, hΓ⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin (m + 1)))) := by
  unfold pullbackPartialOkounkovBody
  rw [dif_pos ⟨hsub, hΓ⟩]

end SGPT.Okounkov.OkoTower

end
