import SGPT.Okounkov.SchemeSectionWeight
import SGPT.Okounkov.SchemeProjectiveSectionPolytopes
import SGPT.Okounkov.SchemeProjectiveSectionRawBody
import SGPT.PSH.CanonicalGrowthManifold
import SGPT.AlmostSemigroup.OkounkovComparison
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.FirstPass.IEnvelope

/-!
# Section sets and Okounkov bodies of Hermitian line bundles (algebraic setting)

Source Section *Algebraic partial Okounkov bodies* of the chapter *The theory of Okounkov
bodies*: `def:Okounkov:L484` (the sets `Γ(θ,φ)` and the polytopes `Δ_k(θ,φ)`),
`def:Okounkov:L500` (the set `Γ^∞(θ,φ)` built from `𝓘_∞`), `def:DeltakT` (twisted polytopes)
and `def:Okobd` (the Okounkov body `Δ_ν(L) = Δ(Γ(L))`).

## Formal setting

`X` is an integral smooth projective complex scheme of relative dimension `n` (structure
morphism `f`, closed projective embedding `E`), viewed through its analytic point manifold
`SchemeComplexPoint f`; `L : X.Modules` is a line bundle with a rank-one atlas `a`. The rank `n`
valuation `ν` is the flag valuation of a smooth flag `Y` of the analytic manifold
(`schemeFubiniStudySectionVector`, a genuine valuation of the function field,
`schemeFubiniStudyFunctionFieldValuation`): this is the case `Δ_{Y•}` of the source, which
writes `Δ_ν` for a general rank `n` valuation.

A section `s ∈ H⁰(X, L^k)` lies in `H⁰(X, L^k ⊗ 𝔞)` for an ideal sheaf `𝔞` when, in every local
frame of `L` (hence of `L^k`), its holomorphic coefficient lies in `𝔞` at every point of the
frame domain (`IsIdealSection`). The metric `h = h₀ e^{-φ}` on `L` is recorded by its weight
`φ` relative to a smooth reference metric `h₀` (curvature `θ = c₁(L, h₀)`); the condition
`s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` only involves `φ` (the smooth positive factor `|e|²_{h₀}` of a frame
does not change local integrability). The multiplier ideal `𝓘(kφ)` is the germ ideal
`multiplierIdeal k φ` (germs `g` with `|g|² e^{-kφ}` locally integrable, source convention), with
`𝓘(0·φ) = 𝒪_X`, and `𝓘_∞(kφ)` is `SGPT.PSH.inftyIdeal (k φ)` (source `def:Iinfty`).

## Further contents

* `multiplierIdeal_eq_of_sameSingularityType`: multiplier ideals only depend on the singularity
  type; hence `Γ(θ, φ)` is unchanged by a change of smooth reference metric (source
  `prop:Okocurrent`, Step 1).
* `partialOkounkovBody`: source `def:Okounkov:L687` relative to an admissible cone, with the
  conditional comparison `partialOkounkovBody_mono` (source `prop:IcompimplyDeltacomp`).
* Conditional forms of source `cor:Okounvol` and of the untwisted case of
  `prop:Deltaconvtwisted`, under the conclusion `Γ(L) ∈ 𝒮'(C)` of source `prop:Okounbiglbdl`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology

section SingularityType

open Set Filter MeasureTheory

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Same singularity type on the whole manifold gives equal multiplier ideals `𝓘(cu) = 𝓘(cv)`. -/
theorem multiplierIdeal_eq_of_sameSingularityType {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v)
    (hsame : SameSingularityTypeOn u v univ) (c : ℝ) :
    multiplierIdeal (n := n) c u = multiplierIdeal (n := n) c v := by
  ext p g
  let e := complexChartAt (n := n) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hp
  have hchart : SameSingularityTypeOn (chartFunction u e) (chartFunction v e) univ := by
    exact ⟨⟨hsame.1.choose, fun z _ => hsame.1.choose_spec _ (mem_univ _)⟩,
      ⟨hsame.2.choose, fun z _ => hsame.2.choose_spec _ (mem_univ _)⟩⟩
  exact and_congr_right fun _ => multiplierIntegrableAt_iff_of_sameSingularityTypeOn
    (hu e _ hz) (hv e _ hz) (U := univ) univ_mem hchart

/-- A bounded smooth perturbation `u + f` of a quasi-psh function has the same multiplier
ideals: `𝓘(c(u + f)) = 𝓘(cu)`. -/
theorem multiplierIdeal_add_bounded_smooth {u : M → EReal} {f : M → ℝ}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (hf : ChartSmooth (n := n) f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (c : ℝ) :
    multiplierIdeal (n := n) c (fun x => u x + (f x : EReal)) =
      multiplierIdeal (n := n) c u := by
  apply multiplierIdeal_eq_of_sameSingularityType (hu.add_smooth hf) hu
  refine ⟨⟨C, fun x _ => ?_⟩, ⟨C, fun x _ => ?_⟩⟩
  · have h1 : (f x : EReal) ≤ (C : EReal) := EReal.coe_le_coe_iff.mpr (le_of_abs_le (hC x))
    exact add_le_add le_rfl h1
  · have h1 : (-C : ℝ) ≤ f x := neg_le_of_abs_le (hC x)
    calc u x = u x + ((f x : EReal) + ((-f x : ℝ) : EReal)) := by
          rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
      _ = (u x + (f x : EReal)) + ((-f x : ℝ) : EReal) := by rw [add_assoc]
      _ ≤ (u x + (f x : EReal)) + (C : EReal) := by
          exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))

/-- The multiplier-ideal order `φ ⪯_𝓘 ψ` (`IOrderOnManifold`: `𝓘(cφ) ⊆ 𝓘(cψ)` for all `c > 0`,
formulated in charts on analytic germs) gives the inclusion of the multiplier ideal sheaves
`𝓘(cφ) ⊆ 𝓘(cψ)` of holomorphic germs. -/
theorem multiplierIdeal_le_of_iOrderOnManifold {φ ψ : M → EReal}
    (h : SGPT.Foundations.Analysis.FirstPass.IEnvelope.IOrderOnManifold (n := n) φ ψ)
    {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := n) c φ).Le (multiplierIdeal (n := n) c ψ) := by
  rintro x g ⟨hg, hint⟩
  refine ⟨hg, ?_⟩
  have hhol := SGPT.Foundations.Analysis.Pending.CartanLocalReduction.holAt_comp_chart_symm
    (mem_chart_source (ComplexModel n) x) hg
  obtain ⟨t, htd, ht, hxt⟩ := eventually_nhds_iff.mp hhol
  have han : AnalyticAt ℂ (fun z => g ((chartAt (ComplexModel n) x).symm z))
      ((chartAt (ComplexModel n) x) x) :=
    SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic.analyticAt_of_differentiableOn ht
      (fun z hz => (htd z hz).differentiableWithinAt) hxt
  exact (SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr
    (h c hc (complexChartAt (n := n) x) _
      ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)) _ han
      ((SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
        _ _ _ _).mp hint))

end SingularityType

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionBodiesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionBodiesCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The holomorphic coefficient of a section `s ∈ H⁰(X, L^k)` in the frame `α^{⊗k}` induced by
a local frame `α` of `L` on `U`. -/
def sectionFrameCoefficient {L : X.Modules} {U : X.Opens} (α : LocalBundleFrame L U) (k : ℕ)
    (s : bundlePowerGlobalSections L k) : SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E U
    ((α.tensorPower k).coefficients (𝟙 U) ((bundleTensorPower L k).val.map (homOfLE le_top).op s))

/-- `s ∈ H⁰(X, L^k ⊗ 𝔞)`: in every local frame of `L`, the coefficient of `s` lies in the ideal
sheaf `𝔞` at every point of the frame domain. -/
def IsIdealSection (𝔞 : GermIdeal n (SchemeComplexPoint f)) {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) : Prop :=
  ∀ (U : X.Opens) (α : LocalBundleFrame L U) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ U → 𝔞.mem p (sectionFrameCoefficient f n E α k s)

/-- `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`, with the source convention `𝓘(0·φ) = 𝒪_X`. -/
def IsMultiplierSection (φ : SchemeComplexPoint f → EReal) {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) : Prop :=
  k = 0 ∨ IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) φ) k s

local instance sectionBodiesComplex [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ))` (source `def:Iinfty`; `𝓘_∞(0) = 𝒪_X`). -/
def IsInftySection (φ : SchemeComplexPoint f → EReal) {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  IsIdealSection f n E (SGPT.PSH.inftyIdeal (n := n) fun x => (k : EReal) * φ x) k s

variable [IsIntegral X] (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The lattice points `(ν(s), k)` of the nonzero sections `s ∈ H⁰(X, L^k)` satisfying a
degreewise condition `P k s`. -/
def sectionValueSet {L : X.Modules} (a : LineBundleAtlas L)
    (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) : Set ((Fin n → ℤ) × ℤ) :=
  {z | ∃ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0), P k s ∧
    z = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ))}

/-- Source `def:Okounkov:L484`, first set:
`Γ(θ, φ) = {(ν(s), k) : k ∈ ℕ, s ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def multiplierSectionSet {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : Set ((Fin n → ℤ) × ℤ) :=
  sectionValueSet f n E Y hY a fun k s => IsMultiplierSection f n E φ k s

/-- Source `def:Okounkov:L500`:
`Γ^∞(θ, φ) = {(ν(s), k) : k ∈ ℕ, s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ)) \ {0}}`. -/
def inftySectionSet {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : Set ((Fin n → ℤ) × ℤ) :=
  sectionValueSet f n E Y hY a fun k s => IsInftySection f n E φ k s

/-- The degree-`k` polytope `Δ_k(S) = Conv {k⁻¹ x : x ∈ S_k}` of a lattice set (source
Section *Almost semigroups*); it is empty when `S_k = ∅`. -/
def degreePolytope (S : Set ((Fin n → ℤ) × ℤ)) (k : ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun x => (k : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x) ''
    SGPT.AlmostSemigroup.slice S (k : ℤ))

/-- Source `def:Okounkov:L484`, second set:
`Δ_k(θ, φ) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) : Set (Fin n → ℝ) :=
  degreePolytope n (multiplierSectionSet f n E Y hY a φ) k

/-- Source `def:Okobd`: the Okounkov body `Δ_{Y•}(L) = Δ(Γ(L))` of `L`, the height-one slice of
the closed convex cone generated by the section semigroup `Γ(L)`
(`SGPT.AlmostSemigroup.Okounkov.body`, source `def:Okokk`). -/
def lineBundleOkounkovBody {L : X.Modules} (a : LineBundleAtlas L) : Set (Fin n → ℝ) :=
  SGPT.AlmostSemigroup.Okounkov.body (schemeProjectiveSectionSemigroup f n E Y hY a)

/-- The lattice values `ν(s)` of the nonzero sections `s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`, for a
twisting line bundle `T`. The bundle `T ⊗ L^k` carries an arbitrary rank-one atlas `b` (the flag
valuation of sections does not depend on the atlas), and its sections are taken in its first
tensor power (the degree-one sections of `bundleTensorPower (T ⊗ L^k) 1 = 𝒪_X ⊗ (T ⊗ L^k)`),
where the flag valuation of sections is defined. -/
def twistedMultiplierValues {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) : Set (Fin n → ℤ) :=
  {x | ∃ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
    (k = 0 ∨ IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) φ) 1 s) ∧
      x = fun i =>
        (schemeFubiniStudySectionVector f n E Y hY b 1 s hs i : ℤ)}

/-- Source `def:DeltakT`, first polytope:
`Δ_{k,T}(θ, φ) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def twistedMultiplierDegreePolytope {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun x => (k : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x) ''
    twistedMultiplierValues f n E Y hY k b φ)

/-- Source `def:DeltakT`, second polytope:
`Δ_{k,T}(L) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k) \ {0}}`. -/
def twistedDegreePolytope {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun x => (k : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x) ''
    {x | ∃ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1)
      (hs : s ≠ 0), x = fun i =>
        (schemeFubiniStudySectionVector f n E Y hY b 1 s hs i : ℤ)})

variable {f n E Y hY}

theorem mem_sectionValueSet {L : X.Modules} {a : LineBundleAtlas L}
    {P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop} {z : (Fin n → ℤ) × ℤ} :
    z ∈ sectionValueSet f n E Y hY a P ↔
      ∃ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0), P k s ∧
        z = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)) :=
  Iff.rfl

/-- The section set of the trivial condition is the section semigroup `Γ(L)`. -/
theorem sectionValueSet_true {L : X.Modules} (a : LineBundleAtlas L) :
    sectionValueSet f n E Y hY a (fun _ _ => True) =
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) := by
  ext z
  constructor
  · rintro ⟨k, s, hs, -, rfl⟩
    exact ⟨k, s, hs, rfl⟩
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, trivial, rfl⟩

/-- Every section set is contained in the section semigroup `Γ(L)`. -/
theorem sectionValueSet_subset {L : X.Modules} (a : LineBundleAtlas L)
    (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) :
    sectionValueSet f n E Y hY a P ⊆
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) := by
  rintro z ⟨k, s, hs, -, rfl⟩
  exact ⟨k, s, hs, rfl⟩

/-- `Γ(θ, φ) ⊆ Γ(L)`. -/
theorem multiplierSectionSet_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    multiplierSectionSet f n E Y hY a φ ⊆
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) :=
  sectionValueSet_subset a _

/-- `Γ^∞(θ, φ) ⊆ Γ(L)`. -/
theorem inftySectionSet_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    inftySectionSet f n E Y hY a φ ⊆
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) :=
  sectionValueSet_subset a _

/-- Monotonicity of section sets in the degreewise condition. -/
theorem sectionValueSet_mono {L : X.Modules} (a : LineBundleAtlas L)
    {P Q : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop} (hPQ : ∀ k s, P k s → Q k s) :
    sectionValueSet f n E Y hY a P ⊆ sectionValueSet f n E Y hY a Q := by
  rintro z ⟨k, s, hs, hP, rfl⟩
  exact ⟨k, s, hs, hPQ k s hP, rfl⟩

/-- Source `prop:Okocurrent`, Step 1: changing the smooth reference metric `h₀` to
`h₀' = h₀ e^{f}` replaces the weight `φ` of `h` by `φ' = φ + f` (with `θ' = θ - dd^c f`), and
`Γ(θ, φ) = Γ(θ', φ')`. Here `f` is any bounded chart-smooth function and `φ` is quasi-psh. -/
theorem multiplierSectionSet_add_bounded_smooth {L : X.Modules} (a : LineBundleAtlas L)
    {φ : SchemeComplexPoint f → EReal} {g : SchemeComplexPoint f → ℝ}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hg : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := n) g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    multiplierSectionSet f n E Y hY a (fun x => φ x + (g x : EReal)) =
      multiplierSectionSet f n E Y hY a φ := by
  let := E.isSeparated
  let := E.quasiCompact
  have hI : ∀ k : ℕ, multiplierIdeal (n := n) (k : ℝ) (fun x => φ x + (g x : EReal)) =
      multiplierIdeal (n := n) (k : ℝ) φ := fun k =>
    multiplierIdeal_add_bounded_smooth hφ hg hC _
  unfold multiplierSectionSet IsMultiplierSection
  simp only [hI]

/-- The degree-`k` slice of `Γ(θ, φ)` is finite. -/
theorem multiplierSectionSet_slice_finite {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    (SGPT.AlmostSemigroup.slice (multiplierSectionSet f n E Y hY a φ) (k : ℤ)).Finite :=
  (schemeProjectiveSectionSemigroup_slice_finite f n E Y hY a k).subset
    fun _ hx => multiplierSectionSet_subset a φ hx

/-- The polytopes `Δ_k(θ, φ)` are compact. -/
theorem isCompact_multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    IsCompact (multiplierDegreePolytope f n E Y hY a φ k) :=
  by
    apply Set.Finite.isCompact_convexHull ℝ
    exact (multiplierSectionSet_slice_finite a φ k).image _

/-- The polytopes `Δ_k(θ, φ)` are convex. -/
theorem convex_multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    Convex ℝ (multiplierDegreePolytope f n E Y hY a φ k) :=
  convex_convexHull ℝ _

/-- `Δ_k(θ, φ) ⊆ Δ_k(L)`. -/
theorem multiplierDegreePolytope_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    multiplierDegreePolytope f n E Y hY a φ k ⊆
      degreePolytope n (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) k :=
  convexHull_mono (Set.image_mono fun _ hx => multiplierSectionSet_subset a φ hx)

/-- A nonzero section of `L^k ⊗ 𝓘(kφ)` gives a vertex `k⁻¹ ν(s)` of `Δ_k(θ, φ)`. -/
theorem normalized_mem_multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) {k : ℕ} (s : bundlePowerGlobalSections L k) (hs : s ≠ 0)
    (hmult : IsMultiplierSection f n E φ k s) :
    (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)) ∈
      multiplierDegreePolytope f n E Y hY a φ k := by
  refine subset_convexHull ℝ _ ⟨fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ),
    ⟨k, s, hs, hmult, rfl⟩, ?_⟩
  ext i
  simp [SGPT.AlmostSemigroup.Counting.integerCast]

/-- The degree-zero section `1` gives `(0, 0) ∈ Γ(θ, φ)`. -/
theorem zero_mem_multiplierSectionSet {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    (0 : (Fin n → ℤ) × ℤ) ∈ multiplierSectionSet f n E Y hY a φ := by
  obtain ⟨k, s, hs, hz⟩ := schemeProjectiveSectionSemigroup_zero_mem f n E Y hY a
  have hk : (k : ℤ) = 0 := (congrArg Prod.snd hz).symm
  have hk' : k = 0 := by exact_mod_cast hk
  exact ⟨k, s, hs, Or.inl hk', hz⟩

/-- `Δ_{Y•}(L)` is the convex body `Δ(Γ(L))` in the Euclidean coordinates of the existing raw
section body. -/
theorem lineBundleOkounkovBody_eq_rawBody {L : X.Modules} (a : LineBundleAtlas L) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm '' lineBundleOkounkovBody f n E Y hY a =
      schemeProjectiveSectionRawBody f n E Y hY a :=
  rfl

/-- `Δ_{Y•}(L)` is closed and convex. -/
theorem lineBundleOkounkovBody_isClosed_convex {L : X.Modules} (a : LineBundleAtlas L) :
    IsClosed (lineBundleOkounkovBody f n E Y hY a) ∧
      Convex ℝ (lineBundleOkounkovBody f n E Y hY a) :=
  ⟨(SGPT.AlmostSemigroup.Okounkov.isClosed_closedCone _).preimage
      (continuous_id.prodMk continuous_const),
    SGPT.AlmostSemigroup.Okounkov.convex_body _⟩

/-- `Δ_{k,T}(θ, φ) ⊆ Δ_{k,T}(L)`. -/
theorem twistedMultiplierDegreePolytope_subset {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) :
    twistedMultiplierDegreePolytope f n E Y hY k b φ ⊆ twistedDegreePolytope f n E Y hY k b := by
  apply convexHull_mono
  apply Set.image_mono
  rintro x ⟨s, hs, -, rfl⟩
  exact ⟨s, hs, rfl⟩

/-- `Δ_{Y•}(L)` does not depend on the atlas of `L`. -/
theorem lineBundleOkounkovBody_atlas_independent {L : X.Modules} (a b : LineBundleAtlas L) :
    lineBundleOkounkovBody f n E Y hY a = lineBundleOkounkovBody f n E Y hY b := by
  unfold lineBundleOkounkovBody
  rw [schemeProjectiveSectionSemigroup_atlas_independent f n E Y hY a b]

section PartialBody

open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension

variable (f n E Y hY)

open Classical in
/-- Source `def:Okounkov:L687`, relative to an admissible ambient cone `C` (the source takes the
cone over `Δ_ν(L)`): when `Γ(θ, φ)` lies in `C` and is an almost semigroup there (source
`thm:Gammaasg`), the partial Okounkov body `Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` is the value of the
continuous extension of the Okounkov body map (source `thm:Okocont`, `bodyExtension`); otherwise
the definition takes the junk value `∅`. -/
def partialOkounkovBody (C : AdmissibleCone n) {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  if h : ∃ hsub : multiplierSectionSet f n E Y hY a φ ⊆ (latticePoints C.cone : Set _),
      (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C then
    (bodyExtension (⟨⟨_, h.1⟩, h.2⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin n)))
  else ∅

variable {f n E Y hY}

/-- The value of the partial Okounkov body on an almost semigroup. -/
theorem partialOkounkovBody_eq {C : AdmissibleCone n} {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal)
    (hsub : multiplierSectionSet f n E Y hY a φ ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    partialOkounkovBody f n E Y hY C a φ =
      (bodyExtension (⟨⟨_, hsub⟩, hΓ⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin n))) := by
  unfold partialOkounkovBody
  rw [dif_pos ⟨hsub, hΓ⟩]

/-- Multiplier-ideal comparison `𝓘(kφ) ⊆ 𝓘(kψ)` for all `k ≥ 1` (implied by `φ ⪯_𝓘 ψ`) gives
`Γ(θ, φ) ⊆ Γ(θ, ψ)`. -/
theorem multiplierSectionSet_mono {L : X.Modules} (a : LineBundleAtlas L)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hI : ∀ k : ℕ, 0 < k → (multiplierIdeal (n := n) (k : ℝ) φ).Le
      (multiplierIdeal (n := n) (k : ℝ) ψ)) :
    multiplierSectionSet f n E Y hY a φ ⊆ multiplierSectionSet f n E Y hY a ψ := by
  apply sectionValueSet_mono
  rintro k s (hk | hs)
  · exact Or.inl hk
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · exact Or.inr fun U α p hp => hI k hk p _ (hs U α p hp)

/-- `φ ⪯_𝓘 ψ` gives `Γ(θ, φ) ⊆ Γ(θ, ψ)`. -/
theorem multiplierSectionSet_mono_of_iOrder {L : X.Modules} (a : LineBundleAtlas L)
    {φ ψ : SchemeComplexPoint f → EReal}
    (h : letI := E.isSeparated; letI := E.quasiCompact;
      SGPT.Foundations.Analysis.FirstPass.IEnvelope.IOrderOnManifold (n := n) φ ψ) :
    multiplierSectionSet f n E Y hY a φ ⊆ multiplierSectionSet f n E Y hY a ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  exact multiplierSectionSet_mono a fun k hk =>
    multiplierIdeal_le_of_iOrderOnManifold h (by exact_mod_cast hk)

/-- Source `prop:IcompimplyDeltacomp`, conditional form: if `𝓘(kφ) ⊆ 𝓘(kψ)` for all `k ≥ 1`
and both `Γ(θ, φ)` and `Γ(θ, ψ)` are almost semigroups in the admissible cone `C`, then
`Δ_{Y•}(θ, φ) ⊆ Δ_{Y•}(θ, ψ)` (via source `cor:Okocomp`). -/
theorem partialOkounkovBody_mono {C : AdmissibleCone n} {L : X.Modules} (a : LineBundleAtlas L)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hI : ∀ k : ℕ, 0 < k → (multiplierIdeal (n := n) (k : ℝ) φ).Le
      (multiplierIdeal (n := n) (k : ℝ) ψ))
    (hφ : ∃ hsub : multiplierSectionSet f n E Y hY a φ ⊆ (latticePoints C.cone : Set _),
      (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C)
    (hψ : ∃ hsub : multiplierSectionSet f n E Y hY a ψ ⊆ (latticePoints C.cone : Set _),
      (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    partialOkounkovBody f n E Y hY C a φ ⊆ partialOkounkovBody f n E Y hY C a ψ := by
  obtain ⟨hsφ, hφ⟩ := hφ
  obtain ⟨hsψ, hψ⟩ := hψ
  rw [partialOkounkovBody_eq a φ hsφ hφ, partialOkounkovBody_eq a ψ hsψ hψ]
  exact SGPT.AlmostSemigroup.OkounkovComparison.bodyExtension_mono _ _
    (multiplierSectionSet_mono a hI)

end PartialBody

section Volume

open SGPT.AlmostSemigroup Filter MeasureTheory

/-- Source `cor:Okounvol`, conditional form: if the section semigroup `Γ(L)` lies in an
admissible cone `C` and generates `ℤⁿ⁺¹` (i.e. `Γ(L) ∈ 𝒮'(C)`, the conclusion of source
`prop:Okounbiglbdl`), then `k⁻ⁿ h⁰(X, L^k) → vol Δ_{Y•}(L)`; equivalently
`vol Δ_{Y•}(L) = vol(L) / n!` with `vol(L) = lim n! h⁰(X, L^k) / kⁿ`. -/
theorem tendsto_finrank_div_pow_lineBundleOkounkovBody {L : X.Modules} (a : LineBundleAtlas L)
    (C : AdmissibleCone n)
    (hS : schemeProjectiveSectionSemigroup f n E Y hY a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f n E Y hY a) = ⊤) :
    Tendsto (fun k : ℕ =>
        letI := schemeGlobalSectionModule f (bundleTensorPower L k)
        (k : ℝ)⁻¹ ^ n * (Module.finrank ℂ (bundlePowerGlobalSections L k) : ℝ))
      atTop (nhds (volume.real (lineBundleOkounkovBody f n E Y hY a))) := by
  have h := Okounkov.tendsto_source_of_generatedGroup_eq_top C _ hS hG
  refine h.congr fun k => ?_
  change (k : ℝ)⁻¹ ^ n * ((Okounkov.sourceSubset C _ hS).slices k).card = _
  rw [Okounkov.card_sourceSubset_slices C _ hS k,
    schemeProjectiveSectionSemigroup_slice_card_eq_finrank f n E Y hY a k]

/-- Source `prop:Deltaconvtwisted` for the trivial twist `T = 𝒪_X`, conditional form: if
`Γ(L) ∈ 𝒮'(C)` (source `prop:Okounbiglbdl`), the polytopes `Δ_k(L)` converge to `Δ_{Y•}(L)` in
the Hausdorff metric. -/
theorem tendsto_hausdorffDist_lineBundleDegreeBody {L : X.Modules} (a : LineBundleAtlas L)
    (C : AdmissibleCone n)
    (hS : schemeProjectiveSectionSemigroup f n E Y hY a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f n E Y hY a) = ⊤) :
    Tendsto (fun k => Metric.hausdorffDist (schemeProjectiveSectionDegreeBody f n E Y hY a k)
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' lineBundleOkounkovBody f n E Y hY a))
      atTop (nhds 0) :=
  BodyGeometry.tendsto_hausdorffDist_degreeBody C _ hS hG

end Volume

end SGPT.Okounkov
