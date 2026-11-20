import SGPT.GAGA.OkoCloseDXMain
import SGPT.GAGA.H0LOkounkov

/-!
# The Hausdorff convergence property `thm:HCP` for an arbitrary twist `T`


Setting of lane OKO-A / DXMAIN: `X` an integral smooth projective complex scheme of dimension
`n = m + 1` carrying a smooth flag `Y•` (flag valuation `ν = ν_{Y•}`), `L` a line bundle with
atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`, and `T` a
line bundle with an atlas (`T` holomorphic is algebraic by GAGA). The twisted polytopes of
`def:DeltakT` are `Δ_{k,T}(θ, φ) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}}`
(`SGPT.Okounkov.twistedMultiplierDegreePolytope`, for any atlas `b_k` of `T ⊗ L^k`; it does not
depend on the atlas, `twistedMultiplierValues_atlas_independent`).

* `eventually_twisted_normalized_mem_thickening` (upper half): for every `η > 0` and `k ≫ 0`,
  `k⁻¹ ν(s) ∈ Δ_{Y•}(θ_φ)^η` for every nonzero `s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` (the twisted
  containment `SGPT.IGood.DXMain.eventually_twisted_mem_smul_partialOkounkovBody`);
* lower half: `#{ν(s)} = h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` (one-dimensional leaves) and the twisted lower
  bound `SGPT.GAGA.OkoClose.dxMainTwistedLowerBound`;
* **`tendsto_hausdorffDist_twistedMultiplierDegreePolytope`** (`thm:HCP`, `lma:twistedHcp` for
  every `T`): `Δ_{k,T}(θ, φ) → Δ_{Y•}(θ, φ)` in the Hausdorff metric, by the filling criterion
  `SGPT.Okounkov.AlgPOB.tendsto_hausdorffDist_of_fills`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.OkoClose

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoHcpTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoHcpCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoHcpManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  {T : X.Modules} (aT : LineBundleAtlas T)


/-- The valuative points `ν(s)` of the twisted multiplier sections do not depend on the atlas of
`T ⊗ L^k`. -/
theorem twistedMultiplierValues_atlas_independent (k : ℕ)
    (b b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) :
    twistedMultiplierValues f (m + 1) E Y hY k b φ =
      twistedMultiplierValues f (m + 1) E Y hY k b' φ := by
  let := E.isSeparated
  let := E.quasiCompact
  have hv (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0) :
      schemeFubiniStudySectionVector f (m + 1) E Y hY b 1 s hs =
        schemeFubiniStudySectionVector f (m + 1) E Y hY b' 1 s hs :=
    schemeOriginalFlagSectionVector_atlas_independent f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY b b' 1 s hs
  ext x
  constructor
  · rintro ⟨s, hs, hP, rfl⟩
    exact ⟨s, hs, hP, by rw [hv]⟩
  · rintro ⟨s, hs, hP, rfl⟩
    exact ⟨s, hs, hP, by rw [hv]⟩


/-- `Δ_{k,T}(θ, φ)` does not depend on the atlas of `T ⊗ L^k`. -/
theorem twistedMultiplierDegreePolytope_atlas_independent (k : ℕ)
    (b b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (φ : SchemeComplexPoint f → EReal) :
    twistedMultiplierDegreePolytope f (m + 1) E Y hY k b φ =
      twistedMultiplierDegreePolytope f (m + 1) E Y hY k b' φ := by
  unfold twistedMultiplierDegreePolytope
  rw [twistedMultiplierValues_atlas_independent f E Y hY k b b' φ]

/-! ### The upper half -/

/-- **Twisted valuative points approach the partial body**: for every `η > 0` and all `k ≫ 0`,
`k⁻¹ ν(s) ∈ Δ_{Y•}(θ, φ)^η` for every nonzero `s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`. -/
theorem eventually_twisted_normalized_mem_thickening {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {η : ℝ} (hη : 0 < η) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
      (k = 0 ∨ IsIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) (k : ℝ) φ) 1 s) →
        (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY
            (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ)) ∈
          thickening η (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨ε, ψ, hε, hψ, -, hle, hsub⟩ :=
    AlgebraicDX.exists_approximant_subset_thickening (F := 𝔽) hφ hη2
  obtain ⟨C, hC, hCsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(θ + (ε / 2) • ω.form))
  obtain ⟨R, hR⟩ := (TranscendentalPartial.isCompact_partialOkounkovBody (F := 𝔽)
    (θ + ε • ω.form) ψ).isBounded.exists_norm_le
  set R' : ℝ := |R| + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hpos : (0 : ℝ) < min (1 / 2) (min (ε / (4 * C)) (η / (2 * R'))) :=
    lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨q, hq0, hqlt⟩ := exists_pos_rat_lt hpos
  have hq1 : q ≤ 1 / 2 := by
    have h : (q : ℝ) ≤ 1 / 2 := hqlt.le.trans (min_le_left _ _)
    exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact h)
  have hqC : 2 * (q : ℝ) * C ≤ ε / 2 := by
    have h : (q : ℝ) ≤ ε / (4 * C) := hqlt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hqR : (q : ℝ) * R' < η / 2 := by
    have h : (q : ℝ) < η / (2 * R') := hqlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨k₀, hk₀, hcont⟩ := SGPT.IGood.DXMain.eventually_twisted_mem_smul_partialOkounkovBody
    f E Y hY aT a H hε hψ hle hC.le hCsemi hq0 hq1 hqC
  refine ⟨k₀, hk₀, fun k hk s hs hm => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hcont k hk s hs hm
  obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.mp (hsub hy)
  rw [mem_thickening_iff]
  refine ⟨z, hz, ?_⟩
  rw [← hyx]
  have hdist : dist ((1 - (q : ℝ)) • y) y ≤ (q : ℝ) * R' := by
    rw [dist_eq_norm]
    have : (1 - (q : ℝ)) • y - y = (-(q : ℝ)) • y := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by exact_mod_cast hq0)]
    have hyR : ‖y‖ ≤ R' := (hR y hy).trans (by rw [hR']; linarith [le_abs_self R])
    exact mul_le_mul_of_nonneg_left hyR (by exact_mod_cast hq0.le)
  calc dist ((1 - (q : ℝ)) • y) z ≤ dist ((1 - (q : ℝ)) • y) y + dist y z := dist_triangle _ _ _
    _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (hdist.trans hqR.le) hdz
    _ = η := add_halves η

/-! ### The twisted value set as a lattice subset of a cube cone -/

/-- The lattice set `{(ν(s), k) : k ≥ k₀, s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}}`. -/
def twistedValueSet (k₀ : ℕ) (φ : SchemeComplexPoint f → EReal) : Set ((Fin (m + 1) → ℤ) × ℤ) :=
  {z | ∃ k : ℕ, k₀ ≤ k ∧ z.2 = (k : ℤ) ∧
    z.1 ∈ twistedMultiplierValues f (m + 1) E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) φ}


theorem slice_twistedValueSet {k₀ k : ℕ} (hk : k₀ ≤ k) (φ : SchemeComplexPoint f → EReal) :
    slice (twistedValueSet f E Y hY a aT k₀ φ) (k : ℤ) =
      twistedMultiplierValues f (m + 1) E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) φ := by
  ext x
  constructor
  · rintro ⟨k', -, hk', hx⟩
    have : k' = k := by
      have h' : (k' : ℤ) = (k : ℤ) := hk'.symm
      exact_mod_cast h'
    subst this
    exact hx
  · intro hx
    exact ⟨k, hk, rfl, hx⟩


theorem slice_twistedValueSet_of_lt {k₀ k : ℕ} (hk : k < k₀) (φ : SchemeComplexPoint f → EReal) :
    slice (twistedValueSet f E Y hY a aT k₀ φ) (k : ℤ) = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨k', hk', hk'', -⟩
  have : k' = k := by
    have h' : (k' : ℤ) = (k : ℤ) := hk''.symm
    exact_mod_cast h'
  omega

/-- **`#{ν(s) : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}} = h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`** (one-dimensional
leaves). -/
theorem card_twistedMultiplierValues {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (k : ℕ) :
    Nat.card (twistedMultiplierValues f (m + 1) E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) φ) =
      SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k := by
  rw [SGPT.IGood.DXMain.twistedMultiplierH0, ← SGPT.IGood.DXMain.card_sectionValues_eq_finrank f
    (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k) 1
    (SGPT.IGood.DXMain.twistedMultiplierSubmodule f (m + 1) E hφq T L k)]
  have hset : twistedMultiplierValues f (m + 1) E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) φ =
      (fun v : Fin (m + 1) → ℕ => fun i => (v i : ℤ)) ''
        SGPT.IGood.DXMain.sectionValues f (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k) 1
          (SGPT.IGood.DXMain.twistedMultiplierSubmodule f (m + 1) E hφq T L k) := by
    ext x
    constructor
    · rintro ⟨s, hs, hP, rfl⟩
      exact ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
      exact ⟨s, hs, hP, rfl⟩
  rw [hset]
  refine Nat.card_image_of_injective (fun v w hvw => ?_) _
  funext i
  exact_mod_cast congrFun hvw i

/-- For `k ≫ 0` the twisted values lie in the cube cone `C([0, C + 1]ⁿ)` as soon as
`Δ_{Y•}(θ_φ) ⊆ [0, C]ⁿ`. -/
theorem exists_twistedValueSet_subset {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {C : ℝ}
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ twistedValueSet f E Y hY a aT k₀ φ ⊆
      (latticePoints (cubeCone (n := m + 1) (C + 1)).cone : Set _) ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ twistedMultiplierValues f (m + 1) E Y hY k
        (SGPT.IGood.DXMain.twistAtlas aT a k) φ,
        ((k : ℝ))⁻¹ • Counting.integerCast x ∈ thickening 1 (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨k₀, hk₀, h⟩ := eventually_twisted_normalized_mem_thickening f E Y hY a H aT hφ one_pos
  have hmem : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ twistedMultiplierValues f (m + 1) E Y hY k
      (SGPT.IGood.DXMain.twistAtlas aT a k) φ,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ thickening 1 (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
    rintro k hk x ⟨s, hs, hP, rfl⟩
    have hcast : Counting.integerCast (fun i =>
        (schemeFubiniStudySectionVector f (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k)
          1 s hs i : ℤ)) =
        fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY
          (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ) := by
      funext i
      simp [Counting.integerCast]
    rw [hcast]
    exact h k hk s hs hP
  refine ⟨k₀, hk₀, ?_, hmem⟩
  rintro ⟨x, z⟩ ⟨k, hk, hz, hx⟩
  simp only at hz hx
  subst hz
  have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le hk₀ hk
  obtain ⟨y, hyK, hdy⟩ := mem_thickening_iff.mp (hmem k hk x hx)
  have hyC := hKC hyK
  change (y, (1 : ℝ)) ∈ (cubeCone (n := m + 1) C).cone at hyC
  obtain ⟨-, hy⟩ := hyC
  obtain ⟨s, hs, -, rfl⟩ := hx
  refine ⟨by simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; positivity,
    fun i => ⟨?_, ?_⟩⟩
  · simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    positivity
  · simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_natCast]
    have hdi : |((k : ℝ))⁻¹ * (schemeFubiniStudySectionVector f (m + 1) E Y hY
        (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ) - y i| < 1 := by
      have h1 := (dist_le_pi_dist (((k : ℝ))⁻¹ • Counting.integerCast (fun i =>
        (schemeFubiniStudySectionVector f (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k)
          1 s hs i : ℤ))) y i).trans_lt hdy
      rw [Real.dist_eq] at h1
      simpa [Counting.integerCast] using h1
    have hyi := (hy i).2
    rw [mul_one] at hyi
    have h2 : ((k : ℝ))⁻¹ * (schemeFubiniStudySectionVector f (m + 1) E Y hY
        (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ) < C + 1 := by
      linarith [(abs_lt.mp hdi).2]
    rw [inv_mul_lt_iff₀ hkpos] at h2
    linarith

/-- `{(ν(s), k) : k ≥ k₀, s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) \ {0}}` as a lattice subset of a cube cone
containing it. -/
def twistedConeSubset {k₀ : ℕ} {φ : SchemeComplexPoint f → EReal} {C : ℝ}
    (hsub : twistedValueSet f E Y hY a aT k₀ φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _)) :
    ConeSubset (cubeCone (n := m + 1) C) :=
  ⟨_, hsub⟩

/-- For `k ≥ k₀` the normalized cardinalities of the twisted value set are
`k⁻ⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`. -/
theorem normalizedCardinality_twistedConeSubset {k₀ : ℕ} {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ) {C : ℝ}
    (hsub : twistedValueSet f E Y hY a aT k₀ φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _)) {k : ℕ} (hk : k₀ ≤ k) :
    (twistedConeSubset f E Y hY a aT hsub).normalizedCardinality k =
      (k : ℝ)⁻¹ ^ (m + 1) * SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k := by
  have h := Nat.card_eq_card_finite_toFinset ((twistedConeSubset f E Y hY a aT hsub).finite_slice k)
  rw [ConeSubset.normalizedCardinality, ← card_twistedMultiplierValues f E Y hY a aT hφq k,
    ← slice_twistedValueSet f E Y hY a aT hk φ]
  rw [show ((twistedConeSubset f E Y hY a aT hsub).slices k).card =
    Nat.card (slice (twistedValueSet f E Y hY a aT k₀ φ) (k : ℤ)) from h.symm]

/-- **The lower hypothesis from the twisted lower bound of `thm:DXmain1`**: for every `ε > 0`
and `k ≫ 0`, `vol Δ_{Y•}(θ_φ) - ε ≤ k⁻ⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`. -/
theorem twistedConeSubset_lower [Nonempty (SchemeComplexPoint f)] {k₀ : ℕ}
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {C : ℝ}
    (hsub : twistedValueSet f E Y hY a aT k₀ φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, volume.real
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) - ε ≤
      (twistedConeSubset f E Y hY a aT hsub).normalizedCardinality k := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hlow := dxMainTwistedLowerBound a H aT hφ
  unfold SGPT.IGood.DXMain.DXMainTwistedLowerBound at hlow
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hφq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
  set V := iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ with hVdef
  have hVtop : V ≠ ⊤ := by
    have hfin := ((PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hφ).2.measure_lt_top
      (μ := (volume : Measure (Fin (m + 1) → ℝ)))).ne
    rw [PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ] at hfin
    intro htop
    apply hfin
    rw [← hVdef, htop]
    exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)
  set N : ℝ := ((m + 1).factorial : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Nat.factorial_pos (m + 1)
  have hvolK : volume.real (PartialBody.generalPartialBody 𝔽 θ φ) = V.toReal / N := by
    rw [measureReal_def, PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [hvolK]
  by_cases hcase : V.toReal / N - ε ≤ 0
  · refine Eventually.of_forall fun k => hcase.trans ?_
    rw [ConeSubset.normalizedCardinality]
    positivity
  push Not at hcase
  have hpos : 0 < V.toReal - N * ε := by
    have := mul_lt_mul_of_pos_left hcase hN
    rw [mul_sub, mul_div_cancel₀ _ hN.ne', mul_zero] at this
    exact this
  have hVpos : 0 < V.toReal := by linarith [mul_pos hN hε]
  have hb : ENNReal.ofReal (V.toReal - N * ε) < V :=
    calc ENNReal.ofReal (V.toReal - N * ε) < ENNReal.ofReal V.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hVpos).mpr (by linarith [mul_pos hN hε])
      _ = V := ENNReal.ofReal_toReal hVtop
  have hev := Filter.eventually_lt_of_lt_liminf (hb.trans_le hlow)
  filter_upwards [hev, eventually_gt_atTop 0, eventually_ge_atTop k₀] with k hk hk0 hkk₀
  rw [normalizedCardinality_twistedConeSubset f E Y hY a aT hφq hsub hkk₀]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hu : SGPT.IGood.DXMain.normalizedTwistedH0 f E a H T hφ k =
      ENNReal.ofReal (N * (SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k : ℝ) /
        (k : ℝ) ^ (m + 1)) := by
    rw [SGPT.IGood.DXMain.normalizedTwistedH0, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_mul hN.le, hNdef, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hkR.le, ENNReal.ofReal_natCast]
  rw [hu] at hk
  have hk' := (ENNReal.ofReal_lt_ofReal_iff'.mp hk).1
  have hinv : (k : ℝ)⁻¹ ^ (m + 1) *
      (SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k : ℝ) =
      (SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k : ℝ) / (k : ℝ) ^ (m + 1) := by
    rw [inv_pow, inv_mul_eq_div]
  rw [hinv]
  have h1 : V.toReal - N * ε < N * ((SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hφq T L k :
      ℝ) / (k : ℝ) ^ (m + 1)) := by
    rw [mul_div_assoc] at hk'
    exact hk'
  rw [div_sub' hN.ne', div_le_iff₀ hN]
  linarith

/-! ### `thm:HCP` -/

include aT in
/-- **Source `thm:HCP` and `lma:twistedHcp` for every twisting line bundle `T`** (flag
valuations): if `vol θ_φ > 0`, the twisted polytopes `Δ_{k,T}(θ, φ)` (`def:DeltakT`, for any atlases
`b_k` of `T ⊗ L^k`) converge in the Hausdorff metric to the partial Okounkov body
`Δ_{Y•}(θ_φ)` (in Euclidean coordinates). -/
theorem tendsto_hausdorffDist_twistedMultiplierDegreePolytope [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          twistedMultiplierDegreePolytope f (m + 1) E Y hY k (b k) φ)
        (TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)))
      atTop (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨-, hKC⟩ := hC C₀ le_rfl φ hφ
  obtain ⟨-, hKC'⟩ := hC (C₀ + 1) (by linarith) φ hφ
  obtain ⟨k₀, -, hsub, -⟩ := exists_twistedValueSet_subset f E Y hY a H aT hφ hKC
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hφ
  set S := twistedConeSubset f E Y hY a aT hsub with hS
  have hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η
        (PartialBody.generalPartialBody 𝔽 (H.curvature a) φ) := by
    intro η hη
    obtain ⟨k₁, -, h⟩ := eventually_twisted_normalized_mem_thickening f E Y hY a H aT hφ hη
    filter_upwards [eventually_ge_atTop k₁] with k hk x hx
    obtain ⟨k', -, hk', hx'⟩ := (ConeSubset.mem_slices S k x).mp hx
    have hkk : k' = k := by
      have h' : (k' : ℤ) = (k : ℤ) := hk'.symm
      exact_mod_cast h'
    subst hkk
    obtain ⟨s, hs, hP, hxs⟩ := hx'
    simp only at hxs
    subst hxs
    have hcast : Counting.integerCast (fun i =>
        (schemeFubiniStudySectionVector f (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k')
          1 s hs i : ℤ)) =
        fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY
          (SGPT.IGood.DXMain.twistAtlas aT a k') 1 s hs i : ℝ) := by
      funext i
      simp [Counting.integerCast]
    rw [hcast]
    exact thickening_subset_cthickening _ _ (h k' hk s hs hP)
  have hfill := tendsto_hausdorffDist_of_fills (cubeCone (n := m + 1) (C₀ + 1)) hKc hKv hKC' S hpos
    hup (fun ε hε => twistedConeSubset_lower f E Y hY a H aT hφ hsub hε)
  refine hfill.congr' ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  congr 1
  unfold euclideanDegreePolytope
  rw [hS]
  change (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' convexHull ℝ
      ((fun x => ((k : ℝ))⁻¹ • Counting.integerCast x) ''
        slice (twistedValueSet f E Y hY a aT k₀ φ) (k : ℤ)) = _
  rw [slice_twistedValueSet f E Y hY a aT hk φ,
    twistedMultiplierDegreePolytope_atlas_independent f E Y hY k (b k)
      (SGPT.IGood.DXMain.twistAtlas aT a k) φ]
  rfl

include aT in
/-- **Source `thm:HCP` and `lma:twistedHcp` for every twisting line bundle `T`, algebraic form**:
there is `C₀` such that for every cube cone `C([0, C]ⁿ)`, `C ≥ C₀`, and every `φ ∈ PSH(X, θ)` with
`vol θ_φ > 0`, `Δ_{k,T}(θ, φ) → Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` (the algebraic partial Okounkov body of
`def:Okounkov:L687`) in the Hausdorff metric. -/
theorem tendsto_hausdorffDist_twistedMultiplierDegreePolytope_partialOkounkovBody
    [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      ∀ b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)),
      Tendsto (fun k => hausdorffDist
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
            twistedMultiplierDegreePolytope f (m + 1) E Y hY k (b k) φ)
          (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ)) atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' φ hφ hpos b => ?_⟩
  rw [hC C hC' φ hφ hpos]
  exact tendsto_hausdorffDist_twistedMultiplierDegreePolytope f E Y hY a H aT hφ hpos b

end SGPT.GAGA.OkoClose
