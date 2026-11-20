import SGPT.Okounkov.PartialBodyContinuity
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformComparison
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAddition
import SGPT.PSH.SourceGentleApproximation

/-!
# Partial Okounkov bodies of Kähler currents

Source: the book's `def:POBKahcurr`, `lma:Okounkov:L1517`, `cor:Kahlercurrentcase` and
`lma:Okomonotone` (chapter *The theory of Okounkov bodies*, section *Transcendental partial
Okounkov bodies*, subsection *The case of Kähler currents*); blueprint chapter `claude-pob`.

Let `T = θ + dd^c φ ∈ 𝒵₊(X, α)` be a Kähler current. The book takes a quasi-equisingular
approximation `(T_j)_j` of `T` in `𝒵₊(X, α)` and sets `Δ_{Y•}(T) = ⋂_j Δ_{Y•}(T_j)`, the
`Δ_{Y•}(T_j)` being the bodies of `def:POBanalsing`.

## Formal conventions

* A quasi-equisingular approximation is the project's `SGPT.PSH.SourceQuasiEquisingularApproximation`
  (all four clauses of the book's `def:quasiequsing`). "In `𝒵₊(X, α)`" means `T_j = θ + dd^c φ_j`
  with `φ_j ∈ PSH(X, θ)`. Since the book applies `def:POBanalsing` to the `T_j`, they must be
  **Kähler currents with analytic singularities** (of a global type `(c, 𝓘)`, which the book
  asserts every potential with analytic singularities has); this is implicit in the book and is
  part of `IsKahlerQEA`. Such approximations exist for every Kähler current
  (`exists_isKahlerQEA`, from `thm:qequi`); a quasi-equisingular approximation in `𝒵₊(X, α)` need
  not consist of Kähler currents in general, so the extra clause is necessary.
* `kahlerPartialBodyOf F θ U = ⋂_j Δ(T_j)` for a given approximation; `kahlerPartialBody F θ φ`
  is the book's body, with a chosen approximation (empty if `T` is not a Kähler current).

## Main results

* `kahlerPartialBodyOf_eq_of_isKahlerQEA`, `kahlerPartialBody_eq_kahlerPartialBodyOf`
  (`lma:Okounkov:L1517`): the body does not depend on the approximation; and
  `kahlerPartialBody_eq_analyticPartialBody` (the sentence after `lma:Okounkov:L1517`): for `T`
  with analytic singularities it is the body of `def:POBanalsing`. **Unconditional**: the step
  `⋂_ε Δ(θ, (1 - ε) φ_j) = Δ(θ, φ_j)`, proved in the book by comparing volumes with
  `eq:volpobanaly` (which rests on `thm:Okounkovtranmain` (1)), is proved here by the limit in
  the class (`PartialBody.mem_partialOkounkovBody_of_forall_smul`).
* `kahlerPartialBody_convexBody`: `Δ(T)` is a convex body (nonempty, compact, convex).
* `kahlerPartialBody_subset_of_iOrder` (`cor:Kahlercurrentcase`): `T ⪯_𝓘 S` gives
  `Δ(T) ⊆ Δ(S) ⊆ Δ(α)`; the comparison `exists_singularityLE_smul_of_iOrder` extends
  `prop:compqequi` to the multiplier-ideal order.
* `kahlerPartialBody_subset_add_kahler`, `kahlerPartialBody_eq_iInter_add_kahler`
  (`lma:Okomonotone`): `Δ(T) ⊆ Δ(T + ω)` and `Δ(T) = ⋂_{ε > 0} Δ(T + ε ω)`; **unconditional**
  (the book uses `prop:vollinearlimit` and volumes).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.PartialBody

open Set Filter
open scoped Pointwise Topology Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial

/-! ### Comparison of quasi-equisingular approximations -/

section Comparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **`prop:compqequi` for the multiplier-ideal order** (blueprint `claude-pob:compqequi-I`): let
`(U_j)` be a quasi-equisingular approximation of `u`, `(V_k)` one of `v`, and `v ⪯_𝓘 u`. For
every `a ∈ (0, 1)` and `j`, `V_k ⪯ (1 - a) U_j` for all large `k`. (For `v = u` this is the
book's `prop:compqequi`, `SGPT.PSH.sourceQuasiEquisingular_eventually_singularityLE`; the proof
is the same, with `𝓘(q v) ⊆ 𝓘(q u)` inserted in the chain of multiplier ideals.) -/
theorem exists_singularityLE_smul_of_iOrder (hn : 0 < n) {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {U V : ℕ → M → EReal} (hU : SourceQuasiEquisingularApproximation θ u U)
    (hV : SourceQuasiEquisingularApproximation σ v V) (hvu : IOrderOnManifold (n := n) v u)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, SingularityLE (V k) (fun x => ((1 - a : ℝ) : EReal) * U j x) := by
  obtain ⟨ω₀, ε, hu⟩ := native_of_sourceQuasiEquisingularApproximation hU
  obtain ⟨ω₁, δ, hv⟩ := native_of_sourceQuasiEquisingularApproximation hV
  obtain ⟨R, hR, hgap⟩ :=
    CompactAnalyticBoundedMultiplierInclusion.exists_pos_uniform_bounded_multiplier_gap
      (hu.term_hasAnalyticSingularityType j)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (2 * R / a)
  have hmR : (0 : ℝ) < m := (div_pos (mul_pos (by norm_num) hR) ha0).trans hmgt
  have hm : 0 < m := by exact_mod_cast hmR
  have hscale : 2 * R < (m : ℝ) * a := (div_lt_iff₀ ha0).mp hmgt
  set p : ℝ := (1 - a) * m with hp_def
  set q : ℝ := (1 - a / 2) * m with hq_def
  have hp : 0 < p := mul_pos (sub_pos.mpr ha1) hmR
  have hq : 0 < q := mul_pos (by linarith) hmR
  have hqm : q < m := by rw [hq_def]; nlinarith
  have hqgap : p + R ≤ q := by rw [hp_def, hq_def]; nlinarith
  have hle : u ≤ U j := fun x => (hu.term_antitone x).le_of_tendsto (hu.term_tendsto x) j
  have hI : (multiplierIdeal (n := n) q u).Le (multiplierIdeal (n := n) q (U j)) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
      (iOrderOnManifold_of_le (hu.term j).1.quasiPlurisubharmonic hle) hq
  have hIvu : (multiplierIdeal (n := n) q v).Le (multiplierIdeal (n := n) q u) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hvu hq
  have hB := hgap p hp q hqgap
  have hpm : p / (m : ℝ) = 1 - a := by
    rw [hp_def]
    exact mul_div_cancel_right₀ (1 - a) hmR.ne'
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hv.eventually_multiplierIdealIncluded hq hqm)
  refine ⟨k₀, fun k hk => ?_⟩
  have hK := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded (hk₀ k hk)
  have hKB : (multiplierIdeal (n := n) (m : ℝ) (V k)).Le
      (AnalyticBoundedMultiplierIdeal.boundedMultiplierIdeal (n := n)
        (fun x => (p : EReal) * U j x)) :=
    fun x f hf => hB x f (hI x f (hIvu x f (hK x f hf)))
  have hcomp :=
    BoundedMultiplierPotentialComparison.moreSingularOn_of_multiplierIdeal_le_boundedMultiplierIdeal
      hn (hv.term k) hm hKB
  rw [hpm] at hcomp
  exact hcomp

end Comparison

/-! ### Quasi-equisingular approximations by Kähler currents -/

section Approximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A quasi-equisingular approximation of `T = θ + dd^c φ` in `𝒵₊(X, α)` by Kähler currents
with analytic singularities** (the approximations used in the book's `def:POBKahcurr`): a
quasi-equisingular approximation `(φ_j)` of `φ` (`def:quasiequsing`, all four clauses) with
`θ + dd^c φ_j` a Kähler current with analytic singularities of a global type, `φ_j ∈ PSH(X, θ)`. -/
def IsKahlerQEA (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (U : ℕ → M → EReal) : Prop :=
  SourceQuasiEquisingularApproximation θ φ U ∧
    ∀ j, U j ∈ globalAnalyticCurrents θ ∧ IsKahlerCurrentPotential θ (U j)

/-- A quasi-equisingular approximation for `θ` is one for `θ' ≥ θ`. -/
theorem sourceQuasiEquisingularApproximation_of_le {θ θ' : ClosedRealOneOneForm n M}
    {φ : M → EReal} {U : ℕ → M → EReal} (h : SourceQuasiEquisingularApproximation θ φ U)
    (hle : (θ' - θ).val.IsSemipositive) : SourceQuasiEquisingularApproximation θ' φ U := by
  obtain ⟨hu, ha, hd, ⟨ω, ε, hε, ht⟩, hI⟩ := h
  refine ⟨TranscendentalBody.isThetaPshPotential_of_le hu hle, ha, hd,
    ⟨ω, ε, hε, fun j => TranscendentalBody.isThetaPshPotential_of_le (ht j) ?_⟩, hI⟩
  have heq : θ' + ε j • ω.form - (θ + ε j • ω.form) = θ' - θ := by abel
  rwa [heq]

/-- A Kähler approximation for `θ` is one for `θ' ≥ θ` (`T + γ`, `γ ≥ 0`). -/
theorem IsKahlerQEA.of_le {θ θ' : ClosedRealOneOneForm n M} {φ : M → EReal}
    {U : ℕ → M → EReal} (h : IsKahlerQEA θ φ U) (hle : (θ' - θ).val.IsSemipositive) :
    IsKahlerQEA θ' φ U :=
  ⟨sourceQuasiEquisingularApproximation_of_le h.1 hle, fun j =>
    ⟨⟨TranscendentalBody.isThetaPshPotential_of_le (h.2 j).1.1 hle, (h.2 j).1.2⟩,
      isKahlerCurrentPotential_of_le (h.2 j).2 hle⟩⟩

/-- A potential with analytic singularities of a global type of a Kähler current is its own
(constant) Kähler approximation. -/
theorem isKahlerQEA_const (ω : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {φ : M → EReal} (hφ : φ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ φ) :
    IsKahlerQEA θ φ (fun _ => φ) :=
  ⟨sourceQuasiEquisingularApproximation_of_native
    (isQuasiEquisingularApproximation_const ω θ hφ.1
      (globalAnalyticCurrents_subset_analyticCurrents θ hφ).2), fun _ => ⟨hφ, hK⟩⟩

/-- **Existence** (blueprint `claude-pob:qea-exists`; the book's `thm:qequi` with the
Kähler-preserving shift): every Kähler current `θ + dd^c φ` has a quasi-equisingular
approximation in `𝒵₊(X, {θ})` by Kähler currents with (gentle) analytic singularities. -/
theorem exists_isKahlerQEA [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) : ∃ U, IsKahlerQEA θ φ U := by
  obtain ⟨κ, hκ⟩ := hφ
  have hφ2 : IsThetaPshPotential (θ - (1 / 2 : ℝ) • κ.form).val φ := by
    refine TranscendentalBody.isThetaPshPotential_of_le hκ ?_
    have heq : θ - (1 / 2 : ℝ) • κ.form - (θ - κ.form) = (1 / 2 : ℝ) • κ.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  obtain ⟨v, hqea, hgentle⟩ := exists_sourceGentleQuasiEquisingularApproximation κ _ hφ2
  obtain ⟨ω₀, ε, hnat⟩ := native_of_sourceQuasiEquisingularApproximation hqea
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω₀.form)
  have hev : ∀ᶠ j in atTop, ε j < 1 / (4 * C) :=
    hnat.error_tendsto.eventually (gt_mem_nhds (by positivity))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  have hterm : ∀ j, j₀ ≤ j → IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val (v j) := by
    intro j hj
    refine TranscendentalBody.isThetaPshPotential_of_le (hnat.term j) ?_
    have hεj := hj₀ j hj
    have hε0 := hnat.error_nonneg j
    have heq : θ - (1 / 4 : ℝ) • κ.form - (θ - (1 / 2 : ℝ) • κ.form + ε j • ω₀.form) =
        ε j • (-ω₀.form + C • κ.form) + (1 / 4 - ε j * C) • κ.form := by module
    rw [heq]
    refine UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hdom hε0)
      (KahlerDomination.isSemipositive_smul κ.isSemipositive ?_)
    have : ε j * C < 1 / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hεj
      nlinarith
    linarith
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨fun j => v (j + j₀),
    sourceQuasiEquisingularApproximation_of_le (sourceQuasiEquisingularApproximation_tail hqea j₀)
      ?_, fun j => ?_⟩
  · have heq : θ - (θ - (1 / 2 : ℝ) • κ.form) = (1 / 2 : ℝ) • κ.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  · have h4 := hterm (j + j₀) (Nat.le_add_left _ _)
    have hθ : IsThetaPshPotential θ.val (v (j + j₀)) := by
      refine TranscendentalBody.isThetaPshPotential_of_le h4 ?_
      have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive hquarter.le
    refine ⟨gentleCurrents_subset_globalAnalyticCurrents ⟨hθ, _, _, hgentle (j + j₀)⟩,
      KahlerBackground.smul hquarter κ, ?_⟩
    simpa only [KahlerBackground.smul_form] using h4

/-- The terms of a quasi-equisingular approximation lie above the limit. -/
theorem le_of_sourceQuasiEquisingularApproximation {θ : ClosedRealOneOneForm n M}
    {φ : M → EReal} {U : ℕ → M → EReal} (h : SourceQuasiEquisingularApproximation θ φ U)
    (j : ℕ) : SingularityLE φ (U j) := by
  obtain ⟨-, -, hd, -, -⟩ := h
  refine (singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => ?_⟩
  rw [EReal.coe_zero, add_zero]
  exact (hd.1 x).le_of_tendsto (hd.2 x) j

/-- The terms of a quasi-equisingular approximation decrease in the singularity order. -/
theorem singularityLE_succ_of_sourceQuasiEquisingularApproximation
    {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {U : ℕ → M → EReal}
    (h : SourceQuasiEquisingularApproximation θ φ U) {i j : ℕ} (hij : i ≤ j) :
    SingularityLE (U j) (U i) := by
  obtain ⟨-, -, hd, -, -⟩ := h
  refine (singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => ?_⟩
  rw [EReal.coe_zero, add_zero]
  exact hd.1 x hij

end Approximation

/-! ### The book's body of a Kähler current -/

section Body

variable {m : ℕ}

/-- **The book's formula of `def:POBKahcurr`** for a given approximation:
`⋂_j Δ_{Y•}(T_j)`, with `Δ_{Y•}(T_j)` the body of `def:POBanalsing`
(`TranscendentalPartial.analyticPartialBody`). -/
def kahlerPartialBodyOf (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (U : ℕ → F.carrier → EReal) :
    Set (Fin (m + 1) → ℝ) :=
  ⋂ j, analyticPartialBody F θ (U j)

open scoped Classical in
/-- **The partial Okounkov body of a Kähler current** (the book's `def:POBKahcurr`):
`Δ_{Y•}(T) = ⋂_j Δ_{Y•}(T_j)` for a chosen quasi-equisingular approximation `(T_j)` of
`T = θ + dd^c φ` in `𝒵₊(X, α)` by Kähler currents with analytic singularities (they exist,
`exists_isKahlerQEA`; the choice does not matter, `kahlerPartialBody_eq_kahlerPartialBodyOf`).
Empty if there is no such approximation (never for a Kähler current). -/
def kahlerPartialBody (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (φ : F.carrier → EReal) :
    Set (Fin (m + 1) → ℝ) :=
  if h : ∃ U, IsKahlerQEA θ φ U then kahlerPartialBodyOf F θ h.choose else ∅

variable {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `⋂_j Δ_{Y•}(T_j)` is the intersection of the DRWNXZ partial bodies `Δ(ξ; T_j)`. -/
theorem kahlerPartialBodyOf_eq_iInter {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) :
    kahlerPartialBodyOf F θ U = ⋂ j, partialOkounkovBody F θ (U j) :=
  iInter_congr fun j =>
    TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody (hU.2 j).1 (hU.2 j).2

/-- **The comparison step** (`lma:Okounkov:L1517`, `cor:Kahlercurrentcase`): for approximations
`(U_k)` of `φ` and `(V_j)` of `ψ` with `φ ⪯_𝓘 ψ`, `⋂_k Δ(U_k) ⊆ ⋂_j Δ(V_j)`. -/
theorem kahlerPartialBodyOf_subset_of_iOrder {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} {U V : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    (hV : IsKahlerQEA θ ψ V) (hI : IOrderOnManifold (n := m + 1) φ ψ) :
    kahlerPartialBodyOf F θ U ⊆ kahlerPartialBodyOf F θ V := by
  rw [kahlerPartialBodyOf_eq_iInter hU, kahlerPartialBodyOf_eq_iInter hV]
  intro x hx
  rw [mem_iInter] at hx ⊢
  intro j
  refine mem_partialOkounkovBody_of_forall_singularityLE (hV.2 j).1 (hV.2 j).2 (V := U) ?_ hx
  intro a ha0 ha1
  have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
  have ha1' : (a : ℝ) < 1 := by exact_mod_cast ha1
  obtain ⟨k₀, hk₀⟩ :=
    exists_singularityLE_smul_of_iOrder (Nat.succ_pos m) hV.1 hU.1 hI ha0' ha1' j
  exact ⟨k₀, hk₀ k₀ le_rfl⟩

/-- **`lma:Okounkov:L1517`** (for given approximations): two quasi-equisingular approximations
of `T` in `𝒵₊(X, α)` by Kähler currents with analytic singularities give the same body
`⋂_j Δ_{Y•}(T_j)`. Unconditional. -/
theorem kahlerPartialBodyOf_eq_of_isKahlerQEA {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U V : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    (hV : IsKahlerQEA θ φ V) : kahlerPartialBodyOf F θ U = kahlerPartialBodyOf F θ V :=
  (kahlerPartialBodyOf_subset_of_iOrder hU hV (iOrderOnManifold_refl φ)).antisymm
    (kahlerPartialBodyOf_subset_of_iOrder hV hU (iOrderOnManifold_refl φ))

/-- **`lma:Okounkov:L1517`**: the body of `def:POBKahcurr` is `⋂_j Δ_{Y•}(T_j)` for **every**
quasi-equisingular approximation `(T_j)` of `T` in `𝒵₊(X, α)` by Kähler currents with analytic
singularities, i.e. it does not depend on the choice. -/
theorem kahlerPartialBody_eq_kahlerPartialBodyOf {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) :
    kahlerPartialBody F θ φ = kahlerPartialBodyOf F θ U := by
  classical
  have h : ∃ U, IsKahlerQEA θ φ U := ⟨U, hU⟩
  rw [kahlerPartialBody, dif_pos h]
  exact kahlerPartialBodyOf_eq_of_isKahlerQEA h.choose_spec hU

/-- `Δ_{Y•}(T) = ⋂_j Δ(ξ; T_j)` for every Kähler approximation. -/
theorem kahlerPartialBody_eq_iInter {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) :
    kahlerPartialBody F θ φ = ⋂ j, partialOkounkovBody F θ (U j) := by
  rw [kahlerPartialBody_eq_kahlerPartialBodyOf hU, kahlerPartialBodyOf_eq_iInter hU]

/-- **The sentence after `lma:Okounkov:L1517`**: if the Kähler current `T` also has analytic
singularities (of a global type), the bodies of `def:POBKahcurr` and `def:POBanalsing`
coincide. -/
theorem kahlerPartialBody_eq_analyticPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : φ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ φ) :
    kahlerPartialBody F θ φ = analyticPartialBody F θ φ := by
  rw [kahlerPartialBody_eq_kahlerPartialBodyOf (isKahlerQEA_const F.omega hφ hK),
    kahlerPartialBodyOf, iInter_const]

/-- The DRWNXZ partial body of a Kähler current lies in the book's body:
`Δ(ξ; T) = closure ν(Ω(ξ; T)) ⊆ Δ_{Y•}(T)` (`T ⪯ T_j`). -/
theorem partialOkounkovBody_subset_kahlerPartialBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    partialOkounkovBody F θ φ ⊆ kahlerPartialBody F θ φ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU]
  exact subset_iInter fun j =>
    partialOkounkovBody_mono θ (le_of_sourceQuasiEquisingularApproximation hU.1 j)

/-- **`Δ_{Y•}(T)` is a convex body** (the book: "We shall define a convex body `Δ_{Y•}(T)`"):
for a Kähler current `T`, `Δ_{Y•}(T)` is convex, compact and nonempty (a decreasing intersection
of the convex bodies `Δ_{Y•}(T_j)`), and contained in `Δ_{Y•}(α)`. -/
theorem kahlerPartialBody_convexBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    Convex ℝ (kahlerPartialBody F θ φ) ∧ IsCompact (kahlerPartialBody F θ φ) ∧
      (kahlerPartialBody F θ φ).Nonempty ∧ kahlerPartialBody F θ φ ⊆ tradOkounkovBody F θ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU]
  have hcl : ∀ j, IsClosed (partialOkounkovBody F θ (U j)) := fun j =>
    isClosed_partialOkounkovBody θ (U j)
  refine ⟨convex_iInter fun j => convex_partialOkounkovBody θ (U j),
    (isCompact_partialOkounkovBody θ (U 0)).of_isClosed_subset (isClosed_iInter hcl)
      (iInter_subset _ 0), ?_,
    (iInter_subset _ 0).trans (partialOkounkovBody_subset_tradOkounkovBody θ (U 0))⟩
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun j => partialOkounkovBody F θ (U j)) (fun j => partialOkounkovBody_mono θ
      (singularityLE_succ_of_sourceQuasiEquisingularApproximation hU.1 (Nat.le_succ j)))
    (fun j => (partialOkounkovBody_convexBody (hU.2 j).2
      (globalAnalyticCurrents_subset_analyticCurrents θ (hU.2 j).1)).2.2.1.mono interior_subset)
    (isCompact_partialOkounkovBody θ (U 0)) hcl

/-- `Δ_{Y•}(T)` is closed (for every potential; empty if `T` is not a Kähler current). -/
theorem isClosed_kahlerPartialBody (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (φ : F.carrier → EReal) : IsClosed (kahlerPartialBody F θ φ) := by
  classical
  by_cases h : ∃ U, IsKahlerQEA θ φ U
  · rw [kahlerPartialBody_eq_iInter h.choose_spec]
    exact isClosed_iInter fun j => isClosed_partialOkounkovBody θ _
  · rw [kahlerPartialBody, dif_neg h]
    exact isClosed_empty

/-- **`cor:Kahlercurrentcase`**: for Kähler currents `T = θ + dd^c φ`, `S = θ + dd^c ψ` in
`𝒵₊(X, α)` with `T ⪯_𝓘 S` (`𝓘(λ φ) ⊆ 𝓘(λ ψ)` for all `λ > 0`),
`Δ_{Y•}(T) ⊆ Δ_{Y•}(S) ⊆ Δ_{Y•}(α)`. Unconditional. -/
theorem kahlerPartialBody_subset_of_iOrder {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hψ : IsKahlerCurrentPotential θ ψ) (hI : IOrderOnManifold (n := m + 1) φ ψ) :
    kahlerPartialBody F θ φ ⊆ kahlerPartialBody F θ ψ ∧
      kahlerPartialBody F θ ψ ⊆ tradOkounkovBody F θ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  obtain ⟨V, hV⟩ := exists_isKahlerQEA hψ
  rw [kahlerPartialBody_eq_kahlerPartialBodyOf hU, kahlerPartialBody_eq_kahlerPartialBodyOf hV]
  refine ⟨kahlerPartialBodyOf_subset_of_iOrder hU hV hI, ?_⟩
  rw [kahlerPartialBodyOf_eq_iInter hV]
  exact (iInter_subset _ 0).trans (partialOkounkovBody_subset_tradOkounkovBody θ (V 0))

/-- **`lma:Okomonotone`, first claim, for semipositive forms**: `Δ_{Y•}(T) ⊆ Δ_{Y•}(T + γ)` for
a Kähler current `T = θ + dd^c φ` and a semipositive form `γ` (the current `T + γ` has the
potential `φ` for `θ + γ`). -/
theorem kahlerPartialBody_subset_of_le {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hle : (θ' - θ).val.IsSemipositive) :
    kahlerPartialBody F θ φ ⊆ kahlerPartialBody F θ' φ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU, kahlerPartialBody_eq_iInter (hU.of_le hle)]
  exact iInter_mono fun j => partialOkounkovBody_subset_of_le hle (U j)

/-- **`lma:Okomonotone`, eq. `DeltaTincreaseomegatemp1`**: for a Kähler current
`T = θ + dd^c φ` and a Kähler form `ω`, `Δ_{Y•}(T) ⊆ Δ_{Y•}(T + ω)`. -/
theorem kahlerPartialBody_subset_add_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (ω : KahlerBackground (m + 1) F.carrier) :
    kahlerPartialBody F θ φ ⊆ kahlerPartialBody F (θ + ω.form) φ :=
  kahlerPartialBody_subset_of_le hφ (by rw [add_sub_cancel_left]; exact ω.isSemipositive)

/-- **`lma:Okomonotone`, second claim, for semipositive forms**:
`Δ_{Y•}(T) = ⋂_{ε > 0} Δ_{Y•}(T + ε γ)`. -/
theorem kahlerPartialBody_eq_iInter_add {θ γ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) (hγ : γ.val.IsSemipositive) :
    kahlerPartialBody F θ φ = ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • γ) φ := by
  have hle : ∀ ε : ℝ, 0 ≤ ε → (θ + ε • γ - θ).val.IsSemipositive := fun ε hε => by
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hγ hε
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε hε => kahlerPartialBody_subset_of_le hφ (hle ε hε.le)
  · intro x hx
    rw [mem_iInter₂] at hx
    obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
    rw [kahlerPartialBody_eq_iInter hU, mem_iInter]
    intro j
    rw [partialOkounkovBody_eq_iInter_add (hU.2 j).1 (hU.2 j).2 hγ, mem_iInter₂]
    intro ε hε
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have h := hx ε hε'
    rw [kahlerPartialBody_eq_iInter (hU.of_le (hle ε hε'.le)), mem_iInter] at h
    exact h j

/-- **`lma:Okomonotone`, eq. `DeltaTincreaseomegatemp2`**: for a Kähler current `T` and a Kähler
form `ω`, `Δ_{Y•}(T) = ⋂_{ε > 0} Δ_{Y•}(T + ε ω)`. Unconditional. -/
theorem kahlerPartialBody_eq_iInter_add_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (ω : KahlerBackground (m + 1) F.carrier) :
    kahlerPartialBody F θ φ = ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • ω.form) φ :=
  kahlerPartialBody_eq_iInter_add hφ ω.isSemipositive

end Body

end SGPT.Okounkov.PartialBody
