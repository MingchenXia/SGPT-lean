import SGPT.Okounkov.AlgebraicValuationSections
import SGPT.Okounkov.AlgebraicBodyBound
import SGPT.IGood.SectionMinimalMultiplier

/-!
# Section sets, polytopes and Okounkov bodies of a Hermitian line bundle for a valuation `ν`

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*,
for an arbitrary valuation `ν : ℂ(X)^× → ℤⁿ` (`SGPT.Okounkov.AlgebraicValuationSections`):

* `def:Okounkov:L484`: `Γ(θ, φ) = {(ν(s), k) : k ∈ ℕ, s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))^×}`,
  `Δ_k(θ, φ) = Conv{k⁻¹ ν(s) : s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))^×}`, and for `φ = V_θ`, `Γ(L)`, `Δ_k(L)`;
* `def:Okounkov:L500`: `Γ^∞(θ, φ) = {(ν(s), k) : s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ))^×}`;
* `def:DeltakT`: `Δ_{k,T}(θ, φ) = Conv{k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))^×}` and
  `Δ_{k,T}(L) = Conv{k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k)^×}`, with the global sections of the line
  bundle `T ⊗ L^k = bundleTensor T (bundleTensorPower L k)` itself;
* `def:Okobd`: `Δ_ν(L) = Δ(Γ(L))` (`SGPT.Okounkov.AlgebraicValuation.centreOkounkovBody`).

The multiplier conditions are those of `SGPT.Okounkov.AlgebraicSectionBodies` (in every local
frame the coefficient lies in the multiplier ideal `𝓘(kφ)`, resp. `𝓘_∞(kφ)`). The canonical
objects take section values at the centre of `ν` (`valuationCenter`, `X` is proper over `ℂ`);
all objects are also defined at any point `c` where `ν ≥ 0`.

## Main results

* `centreMultiplierSectionSet_thetaPshSupremum`: `Γ(θ, V_θ) = Γ(L)` (the convention of
  `def:Okounkov:L484`), from `eq:H0eqH0IVtheta` (`SGPT.IGood.isMultiplierSection_thetaPshSupremum_all`).
* Inclusions `Γ(θ, φ), Γ^∞(θ, φ) ⊆ Γ(L)`, `Δ_k(θ, φ) ⊆ Δ_k(L)`, `Δ_{k,T}(θ, φ) ⊆ Δ_{k,T}(L)`,
  convexity of the polytopes, closedness and convexity of `Δ_ν(L)`.
* Flag valuations: `isNonnegAt_flag` (the flag valuation is nonnegative on the local ring of the
  flag point), and at the flag point the general objects are the existing flag objects
  (`sectionSemigroup_flag`, `multiplierSectionSet_flag`, `inftySectionSet_flag`,
  `okounkovBody_flag`); hence, for flag valuations, `Δ_ν(L)` is a compact convex set, nonempty
  for big `L` (`SGPT.Okounkov.isCompact_lineBundleOkounkovBody`,
  `SGPT.Okounkov.nonempty_lineBundleOkounkovBody`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.AlgebraicValuation

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Opposite TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Pointwise

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance algebraicValuationBodiesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algebraicValuationBodiesCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance algebraicValuationBodiesManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `s ∈ H⁰(X, M ⊗ 𝔞)` for a section `s` of a line bundle `M`: in every local frame of `M`, the
coefficient of `s` lies in the ideal sheaf `𝔞` at every point of the frame domain. -/
def IsPlainIdealSection (𝔞 : GermIdeal n (SchemeComplexPoint f)) {M : X.Modules}
    (s : bundleSections M ⊤) : Prop :=
  ∀ (U : X.Opens) (β : LocalBundleFrame M U) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ U →
      𝔞.mem p (schemeOpenRegularFunction f n E U (β.coefficients (𝟙 U)
        (M.val.map (homOfLE le_top).op s)))

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)

/-- Source `def:Okounkov:L484`, first set, at the point `c`:
`Γ(θ, φ) = {(ν(s), k) : k ∈ ℕ, s ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def multiplierSectionSet {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : Set ((Fin n → ℤ) × ℤ) :=
  sectionValueSet v c a fun k s => IsMultiplierSection f n E φ k s

/-- Source `def:Okounkov:L500`, at the point `c`:
`Γ^∞(θ, φ) = {(ν(s), k) : k ∈ ℕ, s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ)) \ {0}}`. -/
def inftySectionSet {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : Set ((Fin n → ℤ) × ℤ) :=
  sectionValueSet v c a fun k s => IsInftySection f n E φ k s

/-- Source `def:Okounkov:L484`, second set, at the point `c`:
`Δ_k(θ, φ) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) \ {0}}` (empty if there is no such `s`). -/
def multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) : Set (Fin n → ℝ) :=
  SGPT.Okounkov.degreePolytope n (multiplierSectionSet f n E v c a φ) k

/-- The polytopes `Δ_k(L) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, L^k) \ {0}}` at the point `c`. -/
def lineBundleDegreePolytope {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (c : X) {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ) : Set (Fin n → ℝ) :=
  SGPT.Okounkov.degreePolytope n (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) k

/-- The values `ν(s)` of the nonzero sections `s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` (the global sections
of the line bundle `T ⊗ L^k`, with an arbitrary rank-one atlas `b`), at the point `c`. -/
def twistedMultiplierValues {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) : Set (Fin n → ℤ) :=
  {x | ∃ (s : bundleSections (bundleTensor T (bundleTensorPower L k)) ⊤) (hs : s ≠ 0),
    (k = 0 ∨ IsPlainIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) φ) s) ∧
      x = plainSectionVector v c b s hs}

/-- The values `ν(s)` of the nonzero sections `s ∈ H⁰(X, T ⊗ L^k)`, at the point `c`. -/
def twistedValues {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (c : X) {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) : Set (Fin n → ℤ) :=
  {x | ∃ (s : bundleSections (bundleTensor T (bundleTensorPower L k)) ⊤) (hs : s ≠ 0),
    x = plainSectionVector v c b s hs}

/-- Source `def:DeltakT`, first polytope, at the point `c`:
`Δ_{k,T}(θ, φ) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def twistedMultiplierDegreePolytope {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun x => (k : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x) ''
    twistedMultiplierValues f n E v c k b φ)

/-- Source `def:DeltakT`, second polytope, at the point `c`:
`Δ_{k,T}(L) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k) \ {0}}`. -/
def twistedDegreePolytope {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (c : X) {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) : Set (Fin n → ℝ) :=
  convexHull ℝ ((fun x => (k : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x) ''
    twistedValues v c k b)

/-! ### Canonical objects at the centre of `ν` -/

section Centre

/-- Source `def:Okounkov:L484`: `Γ(θ, φ)` for the valuation `ν = w` (values at the centre). -/
def centreMultiplierSectionSet (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    {L : X.Modules} (a : LineBundleAtlas L) (φ : SchemeComplexPoint f → EReal) :
    Set ((Fin n → ℤ) × ℤ) :=
  haveI := E.isProper
  multiplierSectionSet f n E w (valuationCenter f w) a φ

/-- Source `def:Okounkov:L484`: `Δ_k(θ, φ)` for the valuation `ν = w`. -/
def centreMultiplierDegreePolytope
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {L : X.Modules}
    (a : LineBundleAtlas L) (φ : SchemeComplexPoint f → EReal) (k : ℕ) : Set (Fin n → ℝ) :=
  haveI := E.isProper
  multiplierDegreePolytope f n E w (valuationCenter f w) a φ k

/-- Source `def:Okounkov:L484`: `Γ(L)` for the valuation `ν = w`. -/
def centreSectionSemigroup (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    {L : X.Modules} (a : LineBundleAtlas L) : AddSubsemigroup ((Fin n → ℤ) × ℤ) :=
  haveI := E.isProper
  sectionSemigroup w (valuationCenter f w) a

/-- Source `def:Okounkov:L484`: `Δ_k(L)` for the valuation `ν = w`. -/
def centreLineBundleDegreePolytope
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {L : X.Modules}
    (a : LineBundleAtlas L) (k : ℕ) : Set (Fin n → ℝ) :=
  haveI := E.isProper
  lineBundleDegreePolytope w (valuationCenter f w) a k

/-- Source `def:Okounkov:L500`: `Γ^∞(θ, φ)` for the valuation `ν = w`. -/
def centreInftySectionSet (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    {L : X.Modules} (a : LineBundleAtlas L) (φ : SchemeComplexPoint f → EReal) :
    Set ((Fin n → ℤ) × ℤ) :=
  haveI := E.isProper
  inftySectionSet f n E w (valuationCenter f w) a φ

/-- Source `def:DeltakT`: `Δ_{k,T}(θ, φ)` for the valuation `ν = w`. -/
def centreTwistedMultiplierDegreePolytope
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) : Set (Fin n → ℝ) :=
  haveI := E.isProper
  twistedMultiplierDegreePolytope f n E w (valuationCenter f w) k b φ

/-- Source `def:DeltakT`: `Δ_{k,T}(L)` for the valuation `ν = w`. -/
def centreTwistedDegreePolytope
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) : Set (Fin n → ℝ) :=
  haveI := E.isProper
  twistedDegreePolytope w (valuationCenter f w) k b

omit [SmoothOfRelativeDimension n f] in
/-- The centre of `w` is a point where `w ≥ 0`. -/
theorem isNonnegAt_centre (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) :
    haveI := E.isProper
    IsNonnegAt w (valuationCenter f w) :=
  haveI := E.isProper
  isNonnegAt_valuationCenter f w

end Centre

variable {f n E v c}

/-! ### Basic properties -/

/-- `Γ(θ, φ) ⊆ Γ(L)`. -/
theorem multiplierSectionSet_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    multiplierSectionSet f n E v c a φ ⊆ (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) :=
  sectionValueSet_subset c a _

/-- `Γ^∞(θ, φ) ⊆ Γ(L)`. -/
theorem inftySectionSet_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    inftySectionSet f n E v c a φ ⊆ (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) :=
  sectionValueSet_subset c a _

/-- `Δ_k(θ, φ) ⊆ Δ_k(L)`. -/
theorem multiplierDegreePolytope_subset {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    multiplierDegreePolytope f n E v c a φ k ⊆ lineBundleDegreePolytope v c a k :=
  convexHull_mono (Set.image_mono fun _ hx => multiplierSectionSet_subset a φ hx)

theorem convex_multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    Convex ℝ (multiplierDegreePolytope f n E v c a φ k) :=
  convex_convexHull ℝ _

/-- A nonzero section of `L^k ⊗ 𝓘(kφ)` gives the point `k⁻¹ ν(s)` of `Δ_k(θ, φ)`. -/
theorem normalized_mem_multiplierDegreePolytope {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) {k : ℕ} (s : bundlePowerGlobalSections L k) (hs : s ≠ 0)
    (hmult : IsMultiplierSection f n E φ k s) :
    (k : ℝ)⁻¹ • (fun i => (sectionVector v c a k s hs i : ℝ)) ∈
      multiplierDegreePolytope f n E v c a φ k := by
  refine subset_convexHull ℝ _ ⟨sectionVector v c a k s hs, ⟨k, s, hs, hmult, rfl⟩, ?_⟩
  ext i
  simp [SGPT.AlmostSemigroup.Counting.integerCast]

/-- `Δ_{k,T}(θ, φ) ⊆ Δ_{k,T}(L)`. -/
theorem twistedMultiplierDegreePolytope_subset {T L : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) :
    twistedMultiplierDegreePolytope f n E v c k b φ ⊆ twistedDegreePolytope v c k b := by
  apply convexHull_mono
  apply Set.image_mono
  rintro x ⟨s, hs, -, rfl⟩
  exact ⟨s, hs, rfl⟩

/-- The twisted polytopes do not depend on the atlas of `T ⊗ L^k`. -/
theorem twistedMultiplierDegreePolytope_atlas_independent (hc : IsNonnegAt v c) {T L : X.Modules}
    (k : ℕ) (b b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) :
    twistedMultiplierDegreePolytope f n E v c k b φ = twistedMultiplierDegreePolytope f n E v c k b' φ := by
  have hset : twistedMultiplierValues f n E v c k b φ = twistedMultiplierValues f n E v c k b' φ := by
    ext x
    constructor
    · rintro ⟨s, hs, hI, rfl⟩
      exact ⟨s, hs, hI, plainSectionVector_eq_of_value_eq c c b b' s s hs hs
        (plainSectionValue_atlas_independent hc b b' s)⟩
    · rintro ⟨s, hs, hI, rfl⟩
      exact ⟨s, hs, hI, plainSectionVector_eq_of_value_eq c c b' b s s hs hs
        (plainSectionValue_atlas_independent hc b' b s)⟩
  unfold twistedMultiplierDegreePolytope
  rw [hset]

theorem twistedDegreePolytope_atlas_independent (hc : IsNonnegAt v c) {T L : X.Modules}
    (k : ℕ) (b b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    twistedDegreePolytope v c k b = twistedDegreePolytope v c k b' := by
  have hset : twistedValues v c k b = twistedValues v c k b' := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, plainSectionVector_eq_of_value_eq c c b b' s s hs hs
        (plainSectionValue_atlas_independent hc b b' s)⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, plainSectionVector_eq_of_value_eq c c b' b s s hs hs
        (plainSectionValue_atlas_independent hc b' b s)⟩
  unfold twistedDegreePolytope
  rw [hset]

/-- `Δ_ν(L)` is closed and convex. -/
theorem okounkovBody_isClosed_convex {L : X.Modules} (a : LineBundleAtlas L) :
    IsClosed (okounkovBody v c a) ∧ Convex ℝ (okounkovBody v c a) :=
  ⟨(SGPT.AlmostSemigroup.Okounkov.isClosed_closedCone _).preimage
      (continuous_id.prodMk continuous_const),
    SGPT.AlmostSemigroup.Okounkov.convex_body _⟩

/-- Source `def:Okounkov:L484`, convention `Γ(θ, V_θ) = Γ(L)`: for `θ = c₁(L, H)` (`H` a smooth
Hermitian metric) and the potential `V_θ` with minimal singularities, every section of `L^k` is a
section of `L^k ⊗ 𝓘(k V_θ)` (`eq:H0eqH0IVtheta`), so `Γ(θ, V_θ) = Γ(L)`. -/
theorem multiplierSectionSet_thetaPshSupremum {L : X.Modules} (H : SchemeLineBundleMetric f n E L)
    (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    multiplierSectionSet f n E v c a (thetaPshSupremum (H.curvature b).val) =
      (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [← sectionValueSet_true c a]
  unfold multiplierSectionSet
  ext z
  constructor
  · rintro ⟨k, s, hs, -, rfl⟩
    exact ⟨k, s, hs, trivial, rfl⟩
  · rintro ⟨k, s, hs, -, rfl⟩
    exact ⟨k, s, hs, SGPT.IGood.isMultiplierSection_thetaPshSupremum_all H b k s, rfl⟩

/-- Consequently `Δ_k(θ, V_θ) = Δ_k(L)`. -/
theorem multiplierDegreePolytope_thetaPshSupremum {L : X.Modules}
    (H : SchemeLineBundleMetric f n E L) (a b : LineBundleAtlas L) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    multiplierDegreePolytope f n E v c a (thetaPshSupremum (H.curvature b).val) k =
      lineBundleDegreePolytope v c a k := by
  unfold multiplierDegreePolytope lineBundleDegreePolytope
  rw [multiplierSectionSet_thetaPshSupremum H a b]

/-- At the centre: `Γ(θ, V_θ) = Γ(L)`. -/
theorem centreMultiplierSectionSet_thetaPshSupremum {L : X.Modules}
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (H : SchemeLineBundleMetric f n E L) (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    centreMultiplierSectionSet f n E w a (thetaPshSupremum (H.curvature b).val) =
      (centreSectionSemigroup f n E w a : Set ((Fin n → ℤ) × ℤ)) :=
  multiplierSectionSet_thetaPshSupremum H a b

/-! ### Flag valuations -/

section Flag

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The point of `X` under the flag point. -/
abbrev flagCentre : X :=
  letI := E.isSeparated
  letI := E.quasiCompact
  schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E
    (schemeProjectiveTNKahlerBackground f n E) Y hY).val

variable (f n E) in
/-- The flag valuation is nonnegative on the local ring of the flag point. -/
theorem isNonnegAt_flag :
    IsNonnegAt (schemeFubiniStudyFunctionFieldValuation f n E Y hY) (flagCentre (f := f) (n := n)
      (E := E) Y hY) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro g
  change 0 ≤ schemeOriginalFlagFunctionFieldValuation f n E
    (schemeProjectiveTNKahlerBackground f n E) Y hY (algebraMap _ X.functionField g)
  rw [schemeOriginalFlagFunctionFieldValuation_stalk]
  set h := schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n E
    (schemeProjectiveTNKahlerBackground f n E) Y hY).val g
  by_cases h0 : h = 0
  · rw [h0, (originalFlagGermValuation _ _).map_zero]
    exact le_top
  · rw [originalFlagGermValuation_apply_of_ne_zero _ _ h h0]
    apply WithTop.coe_le_coe.mpr
    unfold originalFlagGermLexVector
    rw [← toLex_zero]
    exact Pi.toLex_monotone (fun i => Int.natCast_nonneg _)

/-- At the flag point, the section values of the flag valuation are the existing ones. -/
theorem sectionValue_flag {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    sectionValue (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a k s =
      schemeOriginalFlagSectionValue f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [schemeOriginalFlagSectionValue_eq_frame f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a
    (a.frame (a.centerIndex (flagCentre (f := f) (n := n) (E := E) Y hY)))
    (a.centerIndex_mem _) k s]
  rfl

theorem sectionVector_flag {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    sectionVector (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a k s hs =
      fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have h := sectionValue_flag (E := E) Y hY a k s
  rw [sectionValue_eq_vector _ a k s hs, schemeFubiniStudySectionValue_vector f n E Y hY a k s hs]
    at h
  exact toLex.injective (WithTop.coe_injective h)

/-- At the flag point, `Γ(L)` of the flag valuation is the existing section semigroup. -/
theorem sectionSemigroup_flag {L : X.Modules} (a : LineBundleAtlas L) :
    sectionSemigroup (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a =
      schemeProjectiveSectionSemigroup f n E Y hY a := by
  ext z
  constructor
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, by rw [sectionVector_flag]⟩
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, by rw [sectionVector_flag]⟩

theorem sectionValueSet_flag {L : X.Modules} (a : LineBundleAtlas L)
    (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) :
    sectionValueSet (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a P =
      SGPT.Okounkov.sectionValueSet f n E Y hY a P := by
  ext z
  constructor
  · rintro ⟨k, s, hs, hP, rfl⟩
    exact ⟨k, s, hs, hP, by rw [sectionVector_flag]⟩
  · rintro ⟨k, s, hs, hP, rfl⟩
    exact ⟨k, s, hs, hP, by rw [sectionVector_flag]⟩

/-- At the flag point, `Γ(θ, φ)` of the flag valuation is the existing set. -/
theorem multiplierSectionSet_flag {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    multiplierSectionSet f n E (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a φ =
      SGPT.Okounkov.multiplierSectionSet f n E Y hY a φ :=
  sectionValueSet_flag Y hY a _

/-- At the flag point, `Γ^∞(θ, φ)` of the flag valuation is the existing set. -/
theorem inftySectionSet_flag {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    inftySectionSet f n E (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a φ =
      SGPT.Okounkov.inftySectionSet f n E Y hY a φ :=
  sectionValueSet_flag Y hY a _

/-- At the flag point, `Δ_ν(L)` of the flag valuation is the existing body `Δ_{Y•}(L)`. -/
theorem okounkovBody_flag {L : X.Modules} (a : LineBundleAtlas L) :
    okounkovBody (schemeFubiniStudyFunctionFieldValuation f n E Y hY)
        (flagCentre (f := f) (n := n) (E := E) Y hY) a =
      SGPT.Okounkov.lineBundleOkounkovBody f n E Y hY a := by
  unfold okounkovBody SGPT.Okounkov.lineBundleOkounkovBody
  rw [sectionSemigroup_flag]

end Flag

end SGPT.Okounkov.AlgebraicValuation
