import SGPT.IGood.DXMainComparison
import SGPT.Okounkov.TranscendentalMainTheorem
import SGPT.Okounkov.PartialBodyContinuity
import SGPT.AlmostSemigroup.Counting

/-!
# The asymptotic Riemann–Roch formula `thm:DXmain1`: the upper bound

Source: `thm:DXmain1` (chapter *`𝓘`-good singularities*, Section *The volumes of Hermitian
pseudo-effective line bundles*); blueprint chapter `claude-dxmain`.

## Setting

`X` is an integral smooth projective complex scheme of dimension `n = m + 1` (structure morphism
`f`, closed projective embedding `E`) carrying a smooth flag `Y•` of its analytic point manifold;
`𝔽 = schemeFubiniStudyOriginalFlagGeometry f n E Y hY` is the flag geometry with the
Fubini–Study Kähler background `ω`. `L` is a line bundle with atlas `a` and smooth Hermitian
metric `H`, `θ = c₁(L, H) = H.curvature a`, `φ ∈ PSH(X, θ)`, and
`h⁰(X, L^k ⊗ 𝓘(kφ)) = multiplierH0` (`SGPT.IGood.DXMainSections`).

## Main results

* `exists_approximant` (purely transcendental, any flag geometry): for `η > 0` there are
  `ε > 0` and a Kähler current `θ + ε ω + dd^c ψ` with analytic singularities of a global type,
  `φ ≤ ψ + C`, whose DRWNXZ partial body has volume `≤ vol Δ_{Y•}(θ, φ) + η`.
* `eventually_normalized_mem_smul_partialOkounkovBody`: for such `ψ` and rational
  `a ∈ (0, 1/2]` small, `k⁻¹ ν(s) ∈ (1 - a) Δ(θ + ε ω; ψ)` for all `k ≫ 0` and all nonzero
  `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`.
* **`limsup_multiplierH0_le`** (`thm:DXmain1`, inequality `≤`, `T = 𝒪_X`):
  `limsup_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ ≤ vol θ_φ = ∫_X θ_{P_θ[φ]_𝓘}ⁿ`.
* `tendsto_multiplierH0_of_iVolume_eq_zero` (`thm:DXmain1` when `vol θ_φ = 0`).

The lower bound is not proved here (see the blueprint: it needs a section construction).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open scoped Topology ENNReal NNReal Pointwise

/-! ### Approximation of the volume of a partial body (any flag geometry) -/

section Approximant

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **Approximation of `vol Δ_{Y•}(θ, φ)` by DRWNXZ bodies of analytic Kähler currents**: for
`η > 0` there are `ε > 0` and `ψ ∈ 𝒜ᵍ(θ + ε ω)` with `θ + ε ω + dd^c ψ` a Kähler current,
`φ ⪯ ψ`, and `vol Δ(θ + ε ω; ψ) ≤ vol Δ_{Y•}(θ, φ) + η`. -/
theorem exists_approximant {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ (ε : ℝ) (ψ : F.carrier → EReal), 0 < ε ∧
      ψ ∈ globalAnalyticCurrents (θ + ε • F.omega.form) ∧
      IsKahlerCurrentPotential (θ + ε • F.omega.form) ψ ∧ SingularityLE φ ψ ∧
      volume (partialOkounkovBody F (θ + ε • F.omega.form) ψ) ≤
        volume (PartialBody.generalPartialBody F θ φ) + η := by
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  -- Step 1: the Kähler bodies `Δ(θ + (j + 1)⁻¹ ω, φ)` decrease to `Δ(θ, φ)`.
  set K : ℕ → Set (Fin (m + 1) → ℝ) := fun j =>
    PartialBody.kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ with hK
  have hKanti : Antitone K := by
    intro i j hij
    refine PartialBody.kahlerPartialBody_add_smul_mono hφ F.omega (by positivity) ?_
    have : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact inv_anti₀ (by positivity) this
  have hKmeas : ∀ j, NullMeasurableSet (K j) volume := fun j =>
    (PartialBody.isClosed_kahlerPartialBody _ φ).measurableSet.nullMeasurableSet
  have hKfin : ∃ j, volume (K j) ≠ ⊤ := ⟨0,
    ((PartialBody.kahlerPartialBody_convexBody
      (PartialBody.isKahlerCurrentPotential_add_smul hφ F.omega (by positivity))).2.1.measure_lt_top).ne⟩
  have hlim1 := tendsto_measure_iInter_atTop hKmeas hKanti hKfin
  have hgen : (⋂ j, K j) = PartialBody.generalPartialBody F θ φ := rfl
  rw [hgen] at hlim1
  have hgenfin : volume (PartialBody.generalPartialBody F θ φ) ≠ ⊤ :=
    (PartialBody.convex_isCompact_generalPartialBody hφ).2.measure_lt_top.ne
  obtain ⟨j, hj⟩ := (hlim1.eventually (gt_mem_nhds
    (ENNReal.lt_add_right hgenfin hη2.ne'))).exists
  -- Step 2: the Kähler body is the decreasing intersection along a Kähler approximation.
  set ε : ℝ := ((j : ℝ) + 1)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hφK : IsKahlerCurrentPotential (θ + ε • F.omega.form) φ :=
    PartialBody.isKahlerCurrentPotential_add_smul hφ F.omega hε0
  obtain ⟨U, hU⟩ := PartialBody.exists_isKahlerQEA hφK
  set P : ℕ → Set (Fin (m + 1) → ℝ) := fun i =>
    partialOkounkovBody F (θ + ε • F.omega.form) (U i) with hP
  have hPanti : Antitone P := fun i i' hii' =>
    partialOkounkovBody_mono _
      (PartialBody.singularityLE_succ_of_sourceQuasiEquisingularApproximation hU.1 hii')
  have hPmeas : ∀ i, NullMeasurableSet (P i) volume := fun i =>
    (isClosed_partialOkounkovBody _ _).measurableSet.nullMeasurableSet
  have hPfin : ∃ i, volume (P i) ≠ ⊤ :=
    ⟨0, (isCompact_partialOkounkovBody _ _).measure_lt_top.ne⟩
  have hlim2 := tendsto_measure_iInter_atTop hPmeas hPanti hPfin
  have hKj : (⋂ i, P i) = K j := (PartialBody.kahlerPartialBody_eq_iInter hU).symm
  rw [hKj] at hlim2
  have hKjfin : volume (K j) ≠ ⊤ :=
    ((PartialBody.kahlerPartialBody_convexBody hφK).2.1.measure_lt_top).ne
  obtain ⟨i, hi⟩ := (hlim2.eventually (gt_mem_nhds
    (ENNReal.lt_add_right hKjfin hη2.ne'))).exists
  refine ⟨ε, U i, hε0, (hU.2 i).1, (hU.2 i).2,
    PartialBody.le_of_sourceQuasiEquisingularApproximation hU.1 i, ?_⟩
  calc volume (P i) ≤ volume (K j) + η / 2 := hi.le
    _ ≤ (volume (PartialBody.generalPartialBody F θ φ) + η / 2) + η / 2 := by
        gcongr
        exact hj.le
    _ = volume (PartialBody.generalPartialBody F θ φ) + η := by
        rw [add_assoc, ENNReal.add_halves]

end Approximant

/-! ### The containment of the normalized valuative points -/

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance dxUpperTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxUpperCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance dxUpperManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **The valuative points lie in a scaled partial body** (blueprint
`claude-dxmain:containment`): let `θ' = θ + ε ω`, `ψ ∈ 𝒜ᵍ(θ')` with `θ' + dd^c ψ` Kähler and
`φ ⪯ ψ`, and let `q ∈ ℚ ∩ (0, 1/2]` with `2 q C ≤ ε / 2`, where `C ω - θ - (ε/2) ω ≥ 0`. Then for
all `k ≫ 0` and all nonzero `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`, `k⁻¹ ν(s) ∈ (1 - q) Δ(θ'; ψ)`. -/
theorem eventually_normalized_mem_smul_partialOkounkovBody {φ ψ : SchemeComplexPoint f → EReal}
    {ε : ℝ} (hε : 0 < ε)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ψ ∈ globalAnalyticCurrents (H.curvature a +
        ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form))
    (hle : SingularityLE φ ψ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : letI := E.isSeparated; letI := E.quasiCompact;
      (-(H.curvature a + (ε / 2) • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) +
        C • (schemeProjectiveTNKahlerBackground f (m + 1) E).form).val.IsSemipositive)
    {q : ℚ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hqC : 2 * (q : ℝ) * C ≤ ε / 2) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      IsMultiplierSection f (m + 1) E φ k s →
        (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)) ∈
          (1 - (q : ℝ)) • partialOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (q : ℝ) < 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hq1
    push_cast at h
    linarith
  have hψq : ManifoldQuasiPlurisubharmonic (n := m + 1) ψ := hψ.1.1.quasiPlurisubharmonic
  have hψan := (globalAnalyticCurrents_subset_analyticCurrents _ hψ).2
  obtain ⟨k₀, hk₀, hcomp⟩ :=
    exists_singularityLE_normalizedPotential f (m + 1) E a H hψan hq0R hq1R
  refine ⟨k₀, hk₀, fun k hk s hs hmult => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
  have hI := isIdealSection_multiplierIdeal_of_singularityLE f (m + 1) E hψq hle hkpos hmult
  have hSL := hcomp k hk s hI
  have hε2 : 0 < ε / 2 := by positivity
  have hA : normalizedPotential f (m + 1) E a H k s ∈ analyticCurrents (θ + (ε / 2) • ω.form) := by
    refine normalizedPotential_mem_analyticCurrents f (m + 1) E a H hkpos hs _ ?_
    have heq : θ + (ε / 2) • ω.form - θ = (ε / 2) • ω.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive hε2.le
  have hK := isKahlerCurrentPotential_normalizedPotential f (m + 1) E a H hkpos hs ω hε2
  have hmem := flagValuation_self_mem_partialOkounkovBody_of_analytic (F := 𝔽) hK hA
  have hmem2 := partialOkounkovBody_mono (F := 𝔽) (θ + (ε / 2) • ω.form) hSL hmem
  have hmem3 := PartialBody.inv_smul_mem_partialOkounkovBody_add (F := 𝔽) hC0 hC hq0 hq1 hqC hmem2
  have hθeq : θ + (ε / 2) • ω.form + (ε / 2) • ω.form = θ + ε • ω.form := by
    rw [add_assoc, ← add_smul, add_halves]
  change _ ∈ partialOkounkovBody 𝔽 (θ + (ε / 2) • ω.form + (ε / 2) • ω.form) ψ at hmem3
  rw [hθeq, flagValuation_normalizedPotential f E Y hY a H s hs] at hmem3
  have hne : (1 - (q : ℝ)) ≠ 0 := by linarith
  refine ⟨_, hmem3, ?_⟩
  change (1 - (q : ℝ)) • ((1 - (q : ℝ))⁻¹ • ((k : ℝ)⁻¹ •
    (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)))) = _
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- The lattice count: for `k ≥ k₀` (from the containment), `h⁰(X, L^k ⊗ 𝓘(kφ))` is at most the
number of integer points of `k K`, for any `K` containing all normalized valuative points. -/
theorem multiplierH0_le_integerLatticeCount {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    {K : Set (Fin (m + 1) → ℝ)} (hK : IsCompact K) {k : ℕ} (hk : 0 < k)
    (hmem : ∀ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      IsMultiplierSection f (m + 1) E φ k s →
        (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)) ∈ K) :
    multiplierH0 f (m + 1) E hφq L k ≤ SGPT.AlmostSemigroup.Counting.integerLatticeCount K k := by
  have hcard := card_sectionValues_eq_finrank f (m + 1) E Y hY a k (multiplierSubmodule f (m + 1) E hφq L k)
  rw [multiplierH0, ← hcard, SGPT.AlmostSemigroup.Counting.integerLatticeCount]
  have hfin := SGPT.AlmostSemigroup.Counting.finite_integerPoints_dilate hK k
  have : Finite (SGPT.AlmostSemigroup.Counting.integerPoints ((k : ℝ) • K)) := hfin.to_subtype
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine Nat.card_le_card_of_injective
    (fun v => ⟨fun i => ((v.1 i : ℕ) : ℤ), ?_⟩) ?_
  · obtain ⟨s, hs, hsV, hv⟩ := v.2
    have h := hmem s hs hsV
    change SGPT.AlmostSemigroup.Counting.integerCast (fun i => ((v.1 i : ℕ) : ℤ)) ∈ (k : ℝ) • K
    have heq : SGPT.AlmostSemigroup.Counting.integerCast (fun i => ((v.1 i : ℕ) : ℤ)) =
        (k : ℝ) • ((k : ℝ)⁻¹ •
          (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ))) := by
      rw [smul_smul, mul_inv_cancel₀ hkR, one_smul, hv]
      funext i
      simp [SGPT.AlmostSemigroup.Counting.integerCast]
    rw [heq]
    exact Set.smul_mem_smul_set h
  · intro v w hvw
    apply Subtype.ext
    funext i
    have h : ((v.1 i : ℕ) : ℤ) = ((w.1 i : ℕ) : ℤ) := congrFun (congrArg Subtype.val hvw) i
    exact_mod_cast h

/-- **Source `thm:DXmain1`, the upper bound** (blueprint `claude-dxmain:upper`), for `T = 𝒪_X`:
on an integral smooth projective complex scheme `X` of dimension `n = m + 1` carrying a smooth
flag, for every line bundle `L` with a smooth Hermitian metric `H` (`θ = c₁(L, H)`) and every
`φ ∈ PSH(X, θ)`,
`limsup_{k → ∞} n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ ≤ vol θ_φ = ∫_X θ_{P_θ[φ]_𝓘}ⁿ`. -/
theorem limsup_multiplierH0_le {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (multiplierH0 f (m + 1) E hφ.1.quasiPlurisubharmonic L k : ℝ≥0∞)) /
          (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  have : Nonempty (SchemeComplexPoint f) := PartialBody.nonempty_carrier 𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  have hφq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
  set u : ℕ → ℝ≥0∞ := fun k => (((m + 1).factorial : ℝ≥0∞) *
    (multiplierH0 f (m + 1) E hφq L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1) with hu
  set N : ℝ≥0∞ := ((m + 1).factorial : ℝ≥0∞) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  set V := volume (PartialBody.generalPartialBody 𝔽 θ φ) with hVdef
  have hV : V = iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ / N :=
    PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ
  -- for every `η > 0`: `limsup ≤ n! (vol Δ(θ, φ) + η)`
  have key : ∀ η : ℝ≥0∞, 0 < η → limsup u atTop ≤ N * (V + η) := by
    intro η hη
    obtain ⟨ε, ψ, hε, hψ, -, hle, hvol⟩ := exists_approximant (F := 𝔽) hφ hη
    obtain ⟨C, hC, hCsemi⟩ :=
      KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(θ + (ε / 2) • ω.form))
    have hpos : (0 : ℝ) < min (1 / 2) (ε / (4 * C)) := lt_min (by norm_num) (by positivity)
    obtain ⟨q, hq0, hqlt⟩ := exists_pos_rat_lt hpos
    have hq1 : q ≤ 1 / 2 := by
      have h : (q : ℝ) ≤ 1 / 2 := hqlt.le.trans (min_le_left _ _)
      exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact h)
    have hqC : 2 * (q : ℝ) * C ≤ ε / 2 := by
      have h : (q : ℝ) ≤ ε / (4 * C) := hqlt.le.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h
      linarith
    obtain ⟨k₀, hk₀, hcont⟩ := eventually_normalized_mem_smul_partialOkounkovBody f E Y hY a H
      hε hψ hle hC.le hCsemi hq0 hq1 hqC
    set P := partialOkounkovBody 𝔽 (θ + ε • ω.form) ψ with hP
    set K : Set (Fin (m + 1) → ℝ) := (1 - (q : ℝ)) • P with hK
    have hKc : IsCompact K := (isCompact_partialOkounkovBody _ _).smul _
    have hKconv : Convex ℝ K := (convex_partialOkounkovBody _ _).smul _
    have hq1R : (q : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hq1
      push_cast at h
      exact h
    have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
    have hvolK : volume K ≤ V + η := by
      rw [hK, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun]
      calc ENNReal.ofReal |(1 - (q : ℝ)) ^ (m + 1)| * volume P ≤ 1 * volume P := by
            gcongr
            rw [ENNReal.ofReal_le_one, abs_of_nonneg (pow_nonneg (by linarith) _)]
            exact pow_le_one₀ (by linarith) (by linarith)
        _ = volume P := one_mul _
        _ ≤ V + η := hvol
    -- eventual bound by the lattice count
    have hev : ∀ᶠ k in atTop, u k ≤ N * ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
        (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ)) := by
      filter_upwards [eventually_ge_atTop k₀] with k hk
      have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
      have hcnt := multiplierH0_le_integerLatticeCount f E Y hY a hφq hKc hkpos
        (fun s hs hm => hcont k hk s hs hm)
      rw [hu]
      dsimp only
      rw [mul_div_assoc]
      gcongr
      have hpow : ((k : ℝ≥0∞) ^ (m + 1)) = ENNReal.ofReal ((k : ℝ) ^ (m + 1)) := by
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      have hcnt' : (multiplierH0 f (m + 1) E hφq L k : ℝ≥0∞) ≤
          ENNReal.ofReal (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        exact_mod_cast hcnt
      calc (multiplierH0 f (m + 1) E hφq L k : ℝ≥0∞) / (k : ℝ≥0∞) ^ (m + 1)
          ≤ ENNReal.ofReal (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ) /
              ENNReal.ofReal ((k : ℝ) ^ (m + 1)) := by
            rw [hpow]
            exact ENNReal.div_le_div_right hcnt' _
        _ = ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
              (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ)) := by
            rw [← ENNReal.ofReal_div_of_pos (pow_pos hkR _), inv_pow, div_eq_inv_mul]
    have hlim := ENNReal.Tendsto.const_mul (a := N)
      (ENNReal.tendsto_ofReal (SGPT.AlmostSemigroup.Counting.tendsto_integer_lattice_count hKc hKconv))
      (Or.inr hNtop)
    calc limsup u atTop ≤ limsup (fun k : ℕ => N * ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
          (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ))) atTop :=
          Filter.limsup_le_limsup hev
      _ = N * ENNReal.ofReal (volume.real K) := hlim.limsup_eq
      _ = N * volume K := by
          rw [measureReal_def, ENNReal.ofReal_toReal hKc.measure_lt_top.ne]
      _ ≤ N * (V + η) := by gcongr
  -- let `η → 0`
  have hfinal : limsup u atTop ≤ N * V := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδ' : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / N :=
      ENNReal.div_pos (by exact_mod_cast hδ.ne') hNtop
    calc limsup u atTop ≤ N * (V + (δ : ℝ≥0∞) / N) := key _ hδ'
      _ = N * V + (δ : ℝ≥0∞) := by rw [mul_add, ENNReal.mul_div_cancel hN0 hNtop]
  calc limsup u atTop ≤ N * V := hfinal
    _ = iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ := by
        rw [hV, ENNReal.mul_div_cancel hN0 hNtop]

end SGPT.IGood.DXMain
