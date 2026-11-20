import SGPT.Okounkov.PartialBodyDS
import SGPT.Okounkov.TranscendentalPartialDefs
import SGPT.Foundations.Analysis.Pending.PositiveNativeDivisorialLelongLimit
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Okounkov.PotentialFlagValuationOrder

/-!
# The first coordinate of the valuative characterization of partial Okounkov bodies

Source: the book's `thm:KahcurrminOkoun`, `cor:valuationcurrentinPOB`, `cor:KahcurrminOkoun`
and `thm:Deltapartialint` (chapter *The theory of Okounkov bodies*, subsection *The valuative
characterization*, lines 1786--1940); blueprint chapter `claude-okoun-val`.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag
`Y•`, `θ` a closed real `(1,1)`-form and `T = θ + dd^c φ ∈ 𝒵₊(X, {θ})`. The book proves
`min_lex Δ_{Y•}(T) = ν_{Y•}(T)` (`thm:KahcurrminOkoun` for Kähler currents,
`cor:KahcurrminOkoun` for positive mass) and `ν_{Y•}(T) ∈ Δ_{Y•}(T) ⊆ Δ_{Y•}(α)`
(`cor:valuationcurrentinPOB`). This file proves the **first coordinate** of these statements
for every `T` (no Kähler or positive-mass assumption):

* `flagValuation_zero_le_of_mem_generalPartialBody`: `ν(T, Y₁) ≤ x₁` for every
  `x ∈ Δ_{Y•}(T)`;
* `exists_mem_generalPartialBody_zero_eq`: some `x ∈ Δ_{Y•}(T)` has `x₁ = ν(T, Y₁)`;
  i.e. `min_{x ∈ Δ_{Y•}(T)} x₁ = ν(T, Y₁)`, the transcendental analogue of `thm:nuOk`;
* `lexLeast_zero_eq`: the first coordinate of every lexicographic minimum of `Δ_{Y•}(T)` is
  `ν_{Y•}(T)₁ = ν(T, Y₁)`;

and the **whole** statements in the following cases:

* `flagValuation_mem_generalPartialBody_of_analytic`: `ν_{Y•}(T) ∈ Δ_{Y•}(T)` if `T` has analytic
  singularities (`cor:valuationcurrentinPOB` for such `T`);
* dimension `n = 1` (`m = 0`): `flagValuation_mem_generalPartialBody_dim_one`
  (`cor:valuationcurrentinPOB`), `isLeast_generalPartialBody_dim_one` (`thm:KahcurrminOkoun` and
  `cor:KahcurrminOkoun`: `ν_{Y•}(T)` is the lexicographic minimum of `Δ_{Y•}(T)`, for every `T`);
* `generalPartialBody_subset_tradOkounkovBody`: `Δ_{Y•}(T) ⊆ Δ_{Y•}(α)` for big `α` (the second
  inclusion of `cor:valuationcurrentinPOB`, `thm:pobmain` (2));
* `generalPartialBody_subset_closure_valuations_of_analytic`: `Δ_{Y•}(T) ⊆
  closure {ν(S) : S ∈ 𝒵₊(X, α), S ⪯_𝓘 T}` for a Kähler current `T` with analytic singularities
  of a global type (`thm:Deltapartialint`, `⊆` in Step 1), and
  `tradOkounkovBody_subset_closure_valuations` (`⊆` in `eq:TPOB_val`);
* in dimension `1`, `valuations_subset_generalPartialBody_dim_one` (`⊇` in `eq:DeltaTequalallval`)
  and `tradOkounkovBody_eq_closure_valuations_dim_one` (`eq:TPOB_val`).

## Proof

For a Kähler current `T` and a quasi-equisingular approximation `(T_j)` by Kähler currents
with analytic singularities, `Δ(T) = ⋂_j Δ(ξ; T_j)` and `Δ(ξ; T_j) = closure ν(Ω(ξ; T_j))`.
Every `S ∈ Ω(ξ; T_j)` is more singular than `T_j`, so `ν(S, Y₁) ≥ ν(T_j, Y₁)`: a closed condition.
The generic Lelong numbers `ν(T_j, Y₁)` converge to `ν(T, Y₁)`: `T_j → P_θ[φ]_𝓘` in `d_S`
(`cor:quasi-equichar`), generic Lelong numbers along `Y₁` are `d_S`-continuous at positive mass
(`thm:Lelongcont`) and `𝓘`-invariant. Conversely `ν(T_k) ∈ Δ(ξ; T_k) ⊆ Δ(ξ; T_j)` for `k ≥ j`,
and a limit point of `ν(T_k)` lies in `Δ(T)` with first coordinate `ν(T, Y₁)`. A general `T` is
the decreasing intersection of the Kähler currents `T + j⁻¹ ω`, which have the same valuation.
In dimension `1` the valuation is its first coordinate.

The higher coordinates (`n ≥ 2`) need the slice formula `lma:slicepob` for traces of general
currents and the volume identity `prop:vollinearlimit` (5), see the blueprint.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.Valuative

open Set Filter Metric
open scoped Topology NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody

section Lelong

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- The first coordinate of `ν_{Y•}(θ + dd^c u)` is half the divisorial Lelong number
`inf_{x ∈ Y₁} ν(u, x)` (the generic Lelong number along `Y₁`, source normalization). -/
theorem ofReal_flagValuation_zero {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    ENNReal.ofReal (flagValuation F u 0) =
      DemaillyApproximantDivisorialLelong.divisorialLelongNumber m u
        (F.flag (1 : Fin (m + 2))) / 2 := by
  rw [flagValuation_eq hu, ENNReal.ofReal_coe_nnreal, potentialFlagValuation_first F hu]
  have h := nativeGeneric_eq_two_mul_source (n := m + 1) (Nat.succ_ne_zero m)
    (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u
  have hdiv : DemaillyApproximantDivisorialLelong.divisorialLelongNumber m u
      (F.flag (1 : Fin (m + 2))) =
        ⨅ y : F.flag (1 : Fin (m + 2)), lelongNumber (n := m + 1) u y.val := by
    unfold DemaillyApproximantDivisorialLelong.divisorialLelongNumber
    exact (iInf_subtype' (p := fun x => x ∈ F.flag (1 : Fin (m + 2)))
      (f := fun x _ => lelongNumber (n := m + 1) u x))
  rw [hdiv, h, mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- **Convergence of the generic Lelong numbers along `Y₁` along a Kähler approximation**:
for a Kähler current `T = θ + dd^c φ` and a quasi-equisingular approximation `(T_j)` by Kähler
currents with analytic singularities, `ν(T_j, Y₁) → ν(T, Y₁)` (`cor:quasi-equichar`,
`thm:Lelongcont`, `𝓘`-invariance of Lelong numbers). -/
theorem tendsto_flagValuation_zero_of_isKahlerQEA {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hU : IsKahlerQEA θ φ U) :
    Tendsto (fun j => flagValuation F (U j) 0) atTop (𝓝 (flagValuation F φ 0)) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have _ : CompactSpace F.carrier := F.compact
  have _ : ConnectedSpace F.carrier := F.connected
  have _ : Nonempty F.carrier := nonempty_carrier F
  have hφθ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hpos := diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hφθ
  have hbig := isBigClass_of_isKahlerCurrentPotential hφ
  obtain ⟨ω, ε, hnat⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  obtain ⟨-, hI, -, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit ω θ hbig
      hnat (fun j => (hU.2 j).1.1) hpos
  have hposI : 0 < diagonalPotentialMass θ (iSingularityEnvelope θ.val φ) hI :=
    hpos.trans_le (diagonalPotentialMass_le_iVolume ω hφθ)
  have hdiv := PositiveNativeDivisorialLelongLimit.tendsto_divisorialLelongNumber_of_native_positive
    ω θ hbig atTop (fun j => ⟨U j, (hU.2 j).1.1⟩) ⟨iSingularityEnvelope θ.val φ, hI⟩ hposI hlim
    (F.flag (1 : Fin (m + 2)))
  have hIeq : flagValuation F φ = flagValuation F (iSingularityEnvelope θ.val φ) :=
    flagValuation_eq_of_iEquivalent hφθ hI
      (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
        (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ)
  have hofReal : Tendsto (fun j => ENNReal.ofReal (flagValuation F (U j) 0)) atTop
      (𝓝 (ENNReal.ofReal (flagValuation F φ 0))) := by
    simp only [ofReal_flagValuation_zero (hU.2 _).1.1, hIeq, ofReal_flagValuation_zero hI]
    exact ENNReal.Tendsto.div_const hdiv (Or.inr (by norm_num))
  have hreal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hofReal
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (flagValuation_nonneg _ _)] using hreal

end Lelong

section Kahler

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `ν(T_j, Y₁) ≤ x₁` on `Δ(ξ; T_j) = closure ν(Ω(ξ; T_j))`. -/
theorem flagValuation_zero_le_of_mem_partialOkounkovBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ partialOkounkovBody F θ ψ) : flagValuation F ψ 0 ≤ x 0 := by
  have hclosed : IsClosed {y : Fin (m + 1) → ℝ | flagValuation F ψ 0 ≤ y 0} :=
    isClosed_le continuous_const (continuous_apply 0)
  refine closure_minimal ?_ hclosed hx
  rintro _ ⟨s, ⟨hsΩ, hsψ⟩, rfl⟩
  have hs := isThetaPshPotential_of_mem_gentleCurrents hsΩ.1
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hsψ
  have hI : IOrderOnManifold (n := m + 1) s ψ :=
    iOrderOnManifold_of_le_add hψ.1.quasiPlurisubharmonic hC
  have hlex := SGPT.Okounkov.potentialFlagValuation_lex_le_of_iOrder F hs hψ hI
  show flagValuation F ψ 0 ≤ flagValuation F s 0
  rw [flagValuation_eq hψ, flagValuation_eq hs]
  exact NNReal.coe_le_coe.mpr (lex_le_zero hlex)
where
  /-- The first coordinate is monotone for the lexicographic order. -/
  lex_le_zero {k : ℕ} {a b : Fin (k + 1) → ℝ≥0} (h : toLex a ≤ toLex b) : a 0 ≤ b 0 := by
    rcases h.lt_or_eq with h | h
    · obtain ⟨i, hi, hlt⟩ := h
      rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
      · subst h0; exact hlt.le
      · exact (hi 0 (Fin.succ_pos j)).le
    · rw [toLex_inj.mp h]

/-- **First coordinate, lower bound, Kähler currents**: `ν(T, Y₁) ≤ x₁` for `x ∈ Δ_{Y•}(T)`. -/
theorem flagValuation_zero_le_of_mem_kahlerPartialBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ kahlerPartialBody F θ φ) : flagValuation F φ 0 ≤ x 0 := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU, mem_iInter] at hx
  exact le_of_tendsto' (tendsto_flagValuation_zero_of_isKahlerQEA hφ hU) fun j =>
    flagValuation_zero_le_of_mem_partialOkounkovBody (hU.2 j).1.1 (hx j)

/-- **First coordinate, attained, Kähler currents**: some `x ∈ Δ_{Y•}(T)` has
`x₁ = ν(T, Y₁)`. -/
theorem exists_mem_kahlerPartialBody_zero_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ x ∈ kahlerPartialBody F θ φ, x 0 = flagValuation F φ 0 := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  have hmem : ∀ k, flagValuation F (U k) ∈ partialOkounkovBody F θ (U k) := fun k =>
    flagValuation_self_mem_partialOkounkovBody_of_analytic (hU.2 k).2
      (globalAnalyticCurrents_subset_analyticCurrents θ (hU.2 k).1)
  have hmono : ∀ {j k : ℕ}, j ≤ k → partialOkounkovBody F θ (U k) ⊆ partialOkounkovBody F θ (U j) :=
    fun hjk => partialOkounkovBody_mono θ (singularityLE_succ_of_sourceQuasiEquisingularApproximation
      hU.1 hjk)
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := (isCompact_partialOkounkovBody θ (U 0)).tendsto_subseq
    (x := fun k => flagValuation F (U k)) fun k => hmono (Nat.zero_le k) (hmem k)
  refine ⟨x, ?_, ?_⟩
  · rw [kahlerPartialBody_eq_iInter hU, mem_iInter]
    intro j
    refine (isClosed_partialOkounkovBody θ (U j)).mem_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hmono (hk.trans (hψ.id_le k)) (hmem (ψ k))
  · have h1 := ((continuous_apply (0 : Fin (m + 1))).tendsto x).comp hlim
    have h2 := (tendsto_flagValuation_zero_of_isKahlerQEA hφ hU).comp hψ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2

end Kahler

section General

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **First coordinate, lower bound** (`thm:KahcurrminOkoun`, `cor:KahcurrminOkoun`, first
coordinate, every `T ∈ 𝒵₊(X, α)`): `ν(T, Y₁) ≤ x₁` for every `x ∈ Δ_{Y•}(T)`. -/
theorem flagValuation_zero_le_of_mem_generalPartialBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ generalPartialBody F θ φ) : flagValuation F φ 0 ≤ x 0 := by
  rw [generalPartialBody, mem_iInter] at hx
  exact flagValuation_zero_le_of_mem_kahlerPartialBody
    (isKahlerCurrentPotential_add_smul hφ F.omega (t := ((0 : ℕ) + 1 : ℝ)⁻¹) (by positivity))
    (hx 0)

/-- **First coordinate, attained** (every `T ∈ 𝒵₊(X, α)`): some `x ∈ Δ_{Y•}(T)` has
`x₁ = ν(T, Y₁)`. Together with `flagValuation_zero_le_of_mem_generalPartialBody`,
`min_{x ∈ Δ_{Y•}(T)} x₁ = ν(T, Y₁)`. -/
theorem exists_mem_generalPartialBody_zero_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    ∃ x ∈ generalPartialBody F θ φ, x 0 = flagValuation F φ 0 := by
  have ht0 : ∀ j : ℕ, (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := fun j => by positivity
  have hK := fun j : ℕ => isKahlerCurrentPotential_add_smul hφ F.omega (ht0 j)
  set t : ℕ → Set (Fin (m + 1) → ℝ) := fun j =>
    kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ ∩
      {x | x 0 = flagValuation F φ 0} with htdef
  have hclosed0 : IsClosed {x : Fin (m + 1) → ℝ | x 0 = flagValuation F φ 0} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hcpt : ∀ j, IsCompact (t j) := fun j =>
    (kahlerPartialBody_convexBody (hK j)).2.1.inter_right hclosed0
  have hdec : ∀ j, t (j + 1) ⊆ t j := by
    intro j
    refine inter_subset_inter_left _ (kahlerPartialBody_add_smul_mono hφ F.omega (ht0 (j + 1)) ?_)
    exact inv_anti₀ (by positivity) (by push_cast; linarith)
  have hne : ∀ j, (t j).Nonempty := by
    intro j
    obtain ⟨x, hx, hx0⟩ := exists_mem_kahlerPartialBody_zero_eq (hK j)
    exact ⟨x, hx, hx0⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcpt 0) fun j => (hcpt j).isClosed
  rw [mem_iInter] at hx
  refine ⟨x, ?_, (hx 0).2⟩
  rw [generalPartialBody, mem_iInter]
  exact fun j => (hx j).1

/-- **`min_{x ∈ Δ_{Y•}(T)} x₁ = ν(T, Y₁)`** (the first coordinate of `eq:minOkounkov3`, every
`T ∈ 𝒵₊(X, α)`). -/
theorem isLeast_image_zero_generalPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' generalPartialBody F θ φ)
      (flagValuation F φ 0) := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_generalPartialBody_zero_eq hφ
  refine ⟨⟨x, hx, hx0⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact flagValuation_zero_le_of_mem_generalPartialBody hφ hy

/-- **The first coordinate of the lexicographic minimum** (`thm:KahcurrminOkoun`,
`cor:KahcurrminOkoun`, first coordinate): if `p` is a lexicographic minimum of `Δ_{Y•}(T)`, then
`p₁ = ν_{Y•}(T)₁ = ν(T, Y₁)`. -/
theorem lexLeast_zero_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) {p : Fin (m + 1) → ℝ}
    (hp : IsLeast (toLex '' generalPartialBody F θ φ) (toLex p)) :
    p 0 = flagValuation F φ 0 := by
  obtain ⟨⟨p', hp', hpp'⟩, hleast⟩ := hp
  rw [toLex_inj] at hpp'
  subst hpp'
  refine le_antisymm ?_ (flagValuation_zero_le_of_mem_generalPartialBody hφ hp')
  obtain ⟨x, hx, hx0⟩ := exists_mem_generalPartialBody_zero_eq hφ
  have hle : toLex p' ≤ toLex x := hleast ⟨x, hx, rfl⟩
  rw [← hx0]
  rcases hle.lt_or_eq with h | h
  · obtain ⟨i, hi, hlt⟩ := h
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · subst h0; exact hlt.le
    · exact (hi 0 (Fin.succ_pos j)).le
  · rw [toLex_inj.mp h]

/-- **`cor:valuationcurrentinPOB`, second inclusion** (`thm:pobmain` (2)): `Δ_{Y•}(T) ⊆ Δ_{Y•}(α)`
for `T ∈ 𝒵₊(X, α)`, `α` big. -/
theorem generalPartialBody_subset_tradOkounkovBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    generalPartialBody F θ φ ⊆ tradOkounkovBody F θ :=
  (generalPartialBody_subset_of_iOrder hφ hφ (iOrderOnManifold_refl φ) hbig).2

/-- **`cor:valuationcurrentinPOB` for currents with analytic singularities**: if
`T = θ + dd^c φ ∈ 𝒵₊(X, α)` has analytic singularities, `ν_{Y•}(T) ∈ Δ_{Y•}(T)`. -/
theorem flagValuation_mem_generalPartialBody_of_analytic
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : φ ∈ analyticCurrents θ) : flagValuation F φ ∈ generalPartialBody F θ φ := by
  rw [generalPartialBody, mem_iInter]
  intro j
  have ht : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  have hK := isKahlerCurrentPotential_add_smul hφ.1 F.omega ht
  have hA : φ ∈ analyticCurrents (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) :=
    ⟨isThetaPshPotential_of_isKahlerCurrentPotential hK, hφ.2⟩
  exact partialOkounkovBody_subset_kahlerPartialBody hK
    (flagValuation_self_mem_partialOkounkovBody_of_analytic hK hA)

end General

section DimOne

variable {F : OriginalFlagGeometry.{u} 1}

/-- In dimension `1` a point of `ℝ¹` is its first coordinate. -/
theorem eq_of_zero_eq {x y : Fin 1 → ℝ} (h : x 0 = y 0) : x = y := by
  funext i
  rw [Fin.fin_one_eq_zero i, h]

/-- **`cor:valuationcurrentinPOB` in dimension `1`**: `ν_{Y•}(T) ∈ Δ_{Y•}(T)` for every
`T ∈ 𝒵₊(X, α)`. -/
theorem flagValuation_mem_generalPartialBody_dim_one {θ : ClosedRealOneOneForm 1 F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    flagValuation F φ ∈ generalPartialBody F θ φ := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_generalPartialBody_zero_eq (m := 0) hφ
  rwa [← eq_of_zero_eq hx0]

/-- **`thm:KahcurrminOkoun` and `cor:KahcurrminOkoun` in dimension `1`**: `ν_{Y•}(T)` is the
lexicographic minimum of `Δ_{Y•}(T)` for every `T ∈ 𝒵₊(X, α)` (in particular for Kähler currents
and for currents of positive mass). -/
theorem isLeast_generalPartialBody_dim_one {θ : ClosedRealOneOneForm 1 F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    IsLeast (toLex '' generalPartialBody F θ φ) (toLex (flagValuation F φ)) := by
  refine ⟨⟨_, flagValuation_mem_generalPartialBody_dim_one hφ, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h := flagValuation_zero_le_of_mem_generalPartialBody (m := 0) hφ hy
  rcases h.lt_or_eq with h | h
  · exact (show toLex (flagValuation F φ) < toLex y from ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩).le
  · rw [eq_of_zero_eq h]

end DimOne

section ValuativeSets

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable (F) in
/-- The set `D_{Y•}(T) = {ν_{Y•}(S) : S ∈ 𝒵₊(X, α), S ⪯_𝓘 T}` of `thm:Deltapartialint`, for
`T = θ + dd^c φ` (currents of `𝒵₊(X, {θ})` are `θ + dd^c ψ`, `ψ ∈ PSH(X, θ)`). -/
def valuationsBelow (θ : ClosedRealOneOneForm (m + 1) F.carrier) (φ : F.carrier → EReal) :
    Set (Fin (m + 1) → ℝ) :=
  {x | ∃ ψ : F.carrier → EReal, IsThetaPshPotential θ.val ψ ∧
    IOrderOnManifold (n := m + 1) ψ φ ∧ x = flagValuation F ψ}

variable (F) in
/-- The set `{ν_{Y•}(S) : S ∈ 𝒵₊(X, α)}` of `eq:TPOB_val`. -/
def classValuations (θ : ClosedRealOneOneForm (m + 1) F.carrier) : Set (Fin (m + 1) → ℝ) :=
  {x | ∃ ψ : F.carrier → EReal, IsThetaPshPotential θ.val ψ ∧ x = flagValuation F ψ}

/-- **`thm:Deltapartialint`, `⊆` for Kähler currents with analytic singularities** (Step 1 of the
book): `Δ_{Y•}(T) ⊆ closure D_{Y•}(T)`; indeed `Δ_{Y•}(T) = closure ν(Ω(ξ; T))` and every gentle
Kähler current `S ⪯ T` is in `𝒵₊(X, α)` with `S ⪯_𝓘 T`. -/
theorem generalPartialBody_subset_closure_valuations_of_analytic
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : φ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ φ) :
    generalPartialBody F θ φ ⊆ closure (valuationsBelow F θ φ) := by
  rw [generalPartialBody_eq_analyticPartialBody hφ hK,
    TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody hφ hK]
  refine closure_mono ?_
  rintro _ ⟨s, ⟨hsΩ, hsφ⟩, rfl⟩
  have hs := isThetaPshPotential_of_mem_gentleCurrents hsΩ.1
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hsφ
  exact ⟨s, hs, iOrderOnManifold_of_le_add hφ.1.1.quasiPlurisubharmonic hC, rfl⟩

/-- **`eq:TPOB_val`, `⊆`**: `Δ_{Y•}(α) ⊆ closure {ν_{Y•}(S) : S ∈ 𝒵₊(X, α)}`. -/
theorem tradOkounkovBody_subset_closure_valuations (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    tradOkounkovBody F θ ⊆ closure (classValuations F θ) := by
  rw [tradOkounkovBody_eq_closure_image]
  refine closure_mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, isThetaPshPotential_of_mem_gentleCurrents hs, rfl⟩

end ValuativeSets

section ValuativeDimOne

variable {F : OriginalFlagGeometry.{u} 1}

/-- **`thm:Deltapartialint`, `⊇` in dimension `1`**: `D_{Y•}(T) ⊆ Δ_{Y•}(T)` for every
`T ∈ 𝒵₊(X, α)`, `α` big (`ν(S) ∈ Δ(S) ⊆ Δ(T)` for `S ⪯_𝓘 T`, `thm:pobmain` (2)). -/
theorem valuations_subset_generalPartialBody_dim_one {θ : ClosedRealOneOneForm 1 F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    valuationsBelow F θ φ ⊆ generalPartialBody F θ φ := by
  rintro _ ⟨ψ, hψ, hI, rfl⟩
  exact (generalPartialBody_subset_of_iOrder hψ hφ hI hbig).1
    (flagValuation_mem_generalPartialBody_dim_one hψ)

/-- **`eq:TPOB_val` in dimension `1`**: `Δ_{Y•}(α) = closure {ν_{Y•}(S) : S ∈ 𝒵₊(X, α)}` for a big
class `α = {θ}`. -/
theorem tradOkounkovBody_eq_closure_valuations_dim_one {θ : ClosedRealOneOneForm 1 F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody F θ = closure (classValuations F θ) := by
  refine (tradOkounkovBody_subset_closure_valuations θ).antisymm
    (closure_minimal ?_ (isClosed_tradOkounkovBody θ))
  rintro _ ⟨ψ, hψ, rfl⟩
  exact generalPartialBody_subset_tradOkounkovBody hψ hbig
    (flagValuation_mem_generalPartialBody_dim_one hψ)

end ValuativeDimOne

end SGPT.Okounkov.Valuative
