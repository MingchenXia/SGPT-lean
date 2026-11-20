import SGPT.IGood.DXMainUpper
import SGPT.IGood.SectionMinimalMultiplier

/-!
# Algebraic Okounkov bodies lie in transcendental ones

Consequences of the Okounkov upper bound of `thm:DXmain1` (blueprint `claude-dxmain`) for the
algebraic Okounkov bodies of the chapter *The theory of Okounkov bodies*.

Setting as in `SGPT.IGood.DXMainUpper`: `X` an integral smooth projective complex scheme of
dimension `n = m + 1` with a smooth flag `Y•`, `𝔽` its flag geometry (Fubini–Study background),
`L` a line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)`,
`Δ_{Y•}(θ, φ) = PartialBody.generalPartialBody 𝔽 θ φ` the partial Okounkov body of the current
`θ_φ` (`def:generalPOB`).

## Main results

* `eventually_normalized_mem_thickening`: for every `η > 0` and all `k ≫ 0`, every nonzero
  `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` has `k⁻¹ ν(s)` in the `η`-neighbourhood of `Δ_{Y•}(θ, φ)`.
* `eventually_multiplierDegreePolytope_subset_thickening`: hence
  `Δ_k(θ, φ) ⊆ Δ_{Y•}(θ, φ)^η` for `k ≫ 0` (`def:Okounkov:L484`), i.e. every Hausdorff limit
  point of the polytopes `Δ_k(θ, φ)` lies in `Δ_{Y•}(θ_φ)` (the inclusion `⊆` of
  `cor:transalgPOB` at the level of the polytopes).
* `body_subset_of_normalized_mem`: an Okounkov body `Δ(S)` lies in every closed convex set
  containing all normalized points of `S` (pure cone lemma).
* `lineBundleOkounkovBody_subset_generalPartialBody`, `lineBundleOkounkovBody_subset_tradOkounkovBody`:
  `Δ_{Y•}(L) ⊆ Δ_{Y•}(θ, V_θ) = Δ_{Y•}(c₁(L))` (the latter for big `c₁(L)`; `def:Okobd`,
  `def:tradOk`; the inclusion `⊆` of the comparison of algebraic and transcendental Okounkov
  bodies, `cor:transalgPOB` for minimal singularities).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.Okounkov.AlgebraicDX

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.IGood.DXMain
open scoped Topology ENNReal NNReal Pointwise

/-! ### Approximation of the partial body by DRWNXZ bodies, in the Hausdorff sense -/

section Approximant

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- For every open neighbourhood-type thickening `Δ_{Y•}(θ, φ)^η` there are `ε > 0` and
`ψ ∈ 𝒜ᵍ(θ + ε ω)` (a Kähler current, `φ ⪯ ψ`) with `Δ(θ + ε ω; ψ) ⊆ Δ_{Y•}(θ, φ)^η`. -/
theorem exists_approximant_subset_thickening {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (ψ : F.carrier → EReal), 0 < ε ∧
      ψ ∈ globalAnalyticCurrents (θ + ε • F.omega.form) ∧
      IsKahlerCurrentPotential (θ + ε • F.omega.form) ψ ∧ SingularityLE φ ψ ∧
      TranscendentalPartial.partialOkounkovBody F (θ + ε • F.omega.form) ψ ⊆
        thickening η (PartialBody.generalPartialBody F θ φ) := by
  set U := thickening η (PartialBody.generalPartialBody F θ φ) with hU
  have hUo : IsOpen U := isOpen_thickening
  have hsub : PartialBody.generalPartialBody F θ φ ⊆ U := self_subset_thickening hη _
  -- Step 1
  set K : ℕ → Set (Fin (m + 1) → ℝ) := fun j =>
    PartialBody.kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ with hK
  have hKanti : Antitone K := by
    intro i j hij
    refine PartialBody.kahlerPartialBody_add_smul_mono hφ F.omega (by positivity) ?_
    have : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact inv_anti₀ (by positivity) this
  have hKc : ∀ j, IsCompact (K j) := fun j =>
    (PartialBody.kahlerPartialBody_convexBody
      (PartialBody.isKahlerCurrentPotential_add_smul hφ F.omega (by positivity))).2.1
  obtain ⟨j, hj⟩ := exists_subset_nhds_of_isCompact hKanti.directed_ge hKc
    (fun x hx => hUo.mem_nhds (hsub hx))
  -- Step 2
  set ε : ℝ := ((j : ℝ) + 1)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hφK : IsKahlerCurrentPotential (θ + ε • F.omega.form) φ :=
    PartialBody.isKahlerCurrentPotential_add_smul hφ F.omega hε0
  obtain ⟨V, hV⟩ := PartialBody.exists_isKahlerQEA hφK
  set P : ℕ → Set (Fin (m + 1) → ℝ) := fun i =>
    TranscendentalPartial.partialOkounkovBody F (θ + ε • F.omega.form) (V i) with hP
  have hPanti : Antitone P := fun i i' hii' =>
    TranscendentalPartial.partialOkounkovBody_mono _
      (PartialBody.singularityLE_succ_of_sourceQuasiEquisingularApproximation hV.1 hii')
  have hPc : ∀ i, IsCompact (P i) := fun i => TranscendentalPartial.isCompact_partialOkounkovBody _ _
  have hKj : (⋂ i, P i) = K j := (PartialBody.kahlerPartialBody_eq_iInter hV).symm
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact hPanti.directed_ge hPc
    (fun x hx => hUo.mem_nhds (hj (hKj ▸ hx)))
  exact ⟨ε, V i, hε0, (hV.2 i).1, (hV.2 i).2,
    PartialBody.le_of_sourceQuasiEquisingularApproximation hV.1 i, hi⟩

end Approximant

/-! ### A cone lemma -/

section Cone

variable {n : ℕ}

/-- **Okounkov bodies and their normalized points**: if `K` is closed and convex and every
`(x, k) ∈ S` has `k ≥ 0`, `x = 0` when `k = 0`, and `k⁻¹ x ∈ K` when `k > 0`, then
`Δ(S) ⊆ K`. -/
theorem body_subset_of_normalized_mem (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    {K : Set (Fin n → ℝ)} (hKc : IsClosed K) (hKv : Convex ℝ K)
    (hS : ∀ z ∈ S, 0 ≤ z.2 ∧ (z.2 = 0 → z.1 = 0) ∧
      (0 < z.2 → ((z.2 : ℝ))⁻¹ • Counting.integerCast z.1 ∈ K)) :
    Okounkov.body S ⊆ K := by
  let D : PointedCone ℝ ((Fin n → ℝ) × ℝ) :=
    { carrier := {w | 0 ≤ w.2 ∧ (w.2 = 0 → w.1 = 0) ∧ (0 < w.2 → w.2⁻¹ • w.1 ∈ K)}
      add_mem' := by
        rintro ⟨x, t⟩ ⟨x', t'⟩ ⟨ht, ht0, htK⟩ ⟨ht', ht0', htK'⟩
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at *
        refine ⟨add_nonneg ht ht', fun h0 => ?_, fun hpos => ?_⟩
        · have h1 : t = 0 := by linarith
          have h2 : t' = 0 := by linarith
          rw [ht0 h1, ht0' h2, add_zero]
        · rcases ht.lt_or_eq with htp | rfl
          · rcases ht'.lt_or_eq with htp' | rfl
            · have hsum : (t + t')⁻¹ • (x + x') =
                  (t / (t + t')) • (t⁻¹ • x) + (t' / (t + t')) • (t'⁻¹ • x') := by
                have hs : 0 < t + t' := add_pos htp htp'
                rw [smul_smul, smul_smul, smul_add]
                congr 2 <;> field_simp
              rw [hsum]
              exact hKv (htK htp) (htK' htp') (by positivity) (by positivity)
                (by field_simp)
            · rw [ht0' rfl, add_zero, add_zero]
              exact htK htp
          · rw [ht0 rfl, zero_add, zero_add]
            rw [zero_add] at hpos
            exact htK' hpos
      zero_mem' := ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl _)⟩
      smul_mem' := by
        rintro c ⟨x, t⟩ ⟨ht, ht0, htK⟩
        simp only [Set.mem_ofPred_eq] at *
        change 0 ≤ (c : ℝ) * t ∧ ((c : ℝ) * t = 0 → (c : ℝ) • x = 0) ∧
          (0 < (c : ℝ) * t → ((c : ℝ) * t)⁻¹ • ((c : ℝ) • x) ∈ K)
        refine ⟨mul_nonneg c.2 ht, fun h0 => ?_, fun hpos => ?_⟩
        · rcases mul_eq_zero.mp h0 with hc | htz
          · rw [hc, zero_smul]
          · rw [ht0 htz, smul_zero]
        · have hc : (0 : ℝ) < c := pos_of_mul_pos_left hpos ht
          have htp : 0 < t := pos_of_mul_pos_right hpos c.2
          rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
          exact htK htp }
  have hhull : PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hS z hz
    refine ⟨by simpa [latticeCast] using h1, fun h0 => ?_, fun hpos => ?_⟩
    · have : z.2 = 0 := by simpa [latticeCast] using h0
      funext i
      simp [latticeCast, h2 this]
    · have : 0 < z.2 := by simpa [latticeCast] using hpos
      exact h3 this
  intro x hx
  have hx' : (x, (1 : ℝ)) ∈ closure (D : Set ((Fin n → ℝ) × ℝ)) := by
    have hmem : (x, (1 : ℝ)) ∈ closure ((PointedCone.hull ℝ
        (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) : Set ((Fin n → ℝ) × ℝ))) := hx
    exact closure_mono hhull hmem
  set O : Set ((Fin n → ℝ) × ℝ) := {w | 1 / 2 < w.2} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const continuous_snd
  have hxO : (x, (1 : ℝ)) ∈ O := by norm_num [hO]
  have hcl : (x, (1 : ℝ)) ∈ closure (O ∩ (D : Set ((Fin n → ℝ) × ℝ))) := hOo.inter_closure ⟨hxO, hx'⟩
  let g : (Fin n → ℝ) × ℝ → Fin n → ℝ := fun w => w.2⁻¹ • w.1
  have hg : ContinuousAt g (x, (1 : ℝ)) :=
    (continuous_snd.continuousAt.inv₀ (by norm_num)).smul continuous_fst.continuousAt
  have himg := hg.continuousWithinAt.mem_closure_image hcl
  have hsubK : g '' (O ∩ (D : Set ((Fin n → ℝ) × ℝ))) ⊆ K := by
    rintro _ ⟨w, ⟨hwO, hwD⟩, rfl⟩
    have hwpos : 0 < w.2 := lt_trans (by norm_num) hwO
    exact hwD.2.2 hwpos
  have := closure_minimal hsubK hKc himg
  simpa [g] using this

end Cone

/-! ### The scheme setting -/

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance dxBodyTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxBodyCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance dxBodyManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **Normalized valuative points approach the partial body**: for every `η > 0` and all
`k ≫ 0`, `k⁻¹ ν(s) ∈ Δ_{Y•}(θ, φ)^η` for every nonzero `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem eventually_normalized_mem_thickening {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {η : ℝ} (hη : 0 < η) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      IsMultiplierSection f (m + 1) E φ k s →
        (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)) ∈
          thickening η (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨ε, ψ, hε, hψ, -, hle, hsub⟩ := exists_approximant_subset_thickening (F := 𝔽) hφ hη2
  obtain ⟨C, hC, hCsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(θ + (ε / 2) • ω.form))
  obtain ⟨R, hR⟩ := (TranscendentalPartial.isCompact_partialOkounkovBody (F := 𝔽) (θ + ε • ω.form) ψ).isBounded.exists_norm_le
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
  obtain ⟨k₀, hk₀, hcont⟩ := eventually_normalized_mem_smul_partialOkounkovBody f E Y hY a H
    hε hψ hle hC.le hCsemi hq0 hq1 hqC
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

/-- **`Δ_k(θ, φ) ⊆ Δ_{Y•}(θ, φ)^η` for `k ≫ 0`** (the polytopes of `def:Okounkov:L484`
accumulate inside the partial Okounkov body of the current `θ_φ`). -/
theorem eventually_multiplierDegreePolytope_subset_thickening {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {η : ℝ} (hη : 0 < η) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ᶠ k : ℕ in atTop, multiplierDegreePolytope f (m + 1) E Y hY a φ k ⊆
      thickening η (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨k₀, -, h⟩ := eventually_normalized_mem_thickening f E Y hY a H hφ hη
  filter_upwards [eventually_ge_atTop k₀] with k hk
  refine convexHull_min ?_ ((PartialBody.convex_isCompact_generalPartialBody hφ).1.thickening η)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k', s, hs, hP, hz⟩ := hx
  obtain ⟨hx1, hx2⟩ := Prod.mk.inj hz
  have hkk : k = k' := by exact_mod_cast hx2
  subst hkk
  have hm : IsMultiplierSection f (m + 1) E φ k s := hP
  have hmem := h k hk s hs hm
  convert hmem using 2
  funext i
  rw [hx1]
  simp [Counting.integerCast]

/-- **`Δ_{Y•}(L) ⊆ Δ_{Y•}(θ, V_θ)`**: the Okounkov body of `L` (`def:Okobd`) lies in the partial
Okounkov body of the current of minimal singularities in `c₁(L)` (`L` pseudo-effective:
`PSH(X, θ) ≠ ∅`). -/
theorem lineBundleOkounkovBody_subset_generalPartialBody
    (hpsef : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ u : SchemeComplexPoint f → EReal, IsThetaPshPotential (H.curvature a).val u) :
    letI := E.isSeparated
    letI := E.quasiCompact
    lineBundleOkounkovBody f (m + 1) E Y hY a ⊆
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) (thetaPshSupremum (H.curvature a).val) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  have : Nonempty (SchemeComplexPoint f) := PartialBody.nonempty_carrier 𝔽
  set θ := H.curvature a with hθ
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hpsef
  set Δ := PartialBody.generalPartialBody 𝔽 θ (thetaPshSupremum θ.val) with hΔ
  have hΔc : IsClosed Δ := PartialBody.isClosed_generalPartialBody _ _
  have hΔv : Convex ℝ Δ := (PartialBody.convex_isCompact_generalPartialBody hV).1
  rw [← hΔc.closure_eq, closure_eq_iInter_cthickening]
  refine subset_iInter₂ fun η hη => ?_
  obtain ⟨k₀, hk₀, h⟩ := eventually_normalized_mem_thickening f E Y hY a H hV hη
  refine body_subset_of_normalized_mem _ isClosed_cthickening (hΔv.cthickening η) ?_
  intro z hz
  have hz' := hz
  obtain ⟨k, s, hs, rfl⟩ := hz'
  refine ⟨by simp, fun h0 => ?_, fun hpos => ?_⟩
  · have hk0 : k = 0 := by
      change ((k : ℕ) : ℤ) = 0 at h0
      exact_mod_cast h0
    subst hk0
    rw [schemeFubiniStudySectionVector_degree_zero f m E Y hY a s hs]
    funext i
    simp
  · have hkpos : 0 < k := by
      change (0 : ℤ) < ((k : ℕ) : ℤ) at hpos
      exact_mod_cast hpos
    -- the power `s^(k₀ + 1)` has degree `(k₀ + 1) k ≥ k₀` and valuation `(k₀ + 1) ν(s)`
    have hpow := AlgebraicBody.succ_nsmul_mem (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a)
      hz k₀
    obtain ⟨d, t, ht, hdt⟩ := hpow
    simp only [Prod.smul_mk] at hdt
    obtain ⟨hv, hd⟩ := Prod.mk.inj hdt
    have hdk : (d : ℤ) = (k₀ + 1 : ℕ) * (k : ℤ) := by rw [← hd, nsmul_eq_mul]
    have hdk' : d = (k₀ + 1) * k := by exact_mod_cast hdk
    have hdge : k₀ ≤ d := by rw [hdk']; nlinarith
    have hmt := h d hdge t ht (SGPT.IGood.isMultiplierSection_thetaPshSupremum_all H a d t)
    refine thickening_subset_cthickening η Δ ?_
    convert hmt using 1
    funext i
    have hvi := congrFun hv i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hvi
    have hvi' : ((k₀ + 1 : ℕ) : ℝ) *
        (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ) =
        (schemeFubiniStudySectionVector f (m + 1) E Y hY a d t ht i : ℝ) := by
      exact_mod_cast hvi
    simp only [Pi.smul_apply, smul_eq_mul, Counting.integerCast]
    rw [← hvi', hdk']
    push_cast
    have hk1 : ((k₀ : ℝ) + 1) ≠ 0 := by positivity
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    field_simp

/-- **`Δ_{Y•}(L) ⊆ Δ_{Y•}(c₁(L))`** for `c₁(L)` big (`def:Okobd` ⊆ `def:tradOk`; the inclusion
`⊆` of `cor:transalgPOB` for minimal singularities). -/
theorem lineBundleOkounkovBody_subset_tradOkounkovBody
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative (H.curvature a)))
    (hpsef : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ u : SchemeComplexPoint f → EReal, IsThetaPshPotential (H.curvature a).val u) :
    letI := E.isSeparated
    letI := E.quasiCompact
    lineBundleOkounkovBody f (m + 1) E Y hY a ⊆
      tradOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
  set θ := H.curvature a with hθ
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hpsef
  have hmin : ∀ ψ : SchemeComplexPoint f → EReal, IsThetaPshPotential θ.val ψ →
      SingularityLE ψ (thetaPshSupremum θ.val) := fun ψ hψ =>
    FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hpsef ψ hψ
  rw [← PartialBody.generalPartialBody_eq_tradOkounkovBody_of_minimal
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hbig hV hmin]
  exact lineBundleOkounkovBody_subset_generalPartialBody f E Y hY a H hpsef

end SGPT.Okounkov.AlgebraicDX
