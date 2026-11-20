import SGPT.Okounkov.TranscendentalDensityTheorem
import SGPT.Okounkov.TranscendentalBody2Interior

/-!
# Partial Okounkov bodies: definition and convexity

Source: blueprint nodes `tok:partial-def` and `tok:partial-convex` (chapter
`claude-okounkov-transcendental`), i.e. Darvas--Reboulet--Witt Nyström--Xia--Zhang,
*Transcendental Okounkov bodies* (DRWNXZ), Definition 5.1 and Proposition 5.2.

For a class `ξ = {θ}` and a current `R = θ + dd^c ψ`, the **partial Okounkov body** is
`Δ(ξ; R) = closure ν(Ω(ξ; R))`, where `Ω(ξ; R)` is the set of gentle Kähler currents in `ξ`
more singular than `R` (`TranscendentalCore.gentleKahlerCurrentsBelow`). DRWNXZ define it for
Kähler currents `R ∈ 𝒜ᵍ(ξ)`; the definition makes sense for every `R` and the hypotheses are
put on the theorems.

* `partialOkounkovBody` (`tok:partial-def`);
* `partialOkounkovBody_eq_closure_analytic` (`tok:partial-analytic` in this language):
  `Δ(ξ; R) = closure ν(𝒜(ξ; R))` for a Kähler current `R ∈ 𝒜(ξ)` (DENSITY's
  `partialAnalyticStatement`);
* `partialOkounkovBody_subset_tradOkounkovBody`, `partialOkounkovBody_mono`: `Δ(ξ; R) ⊆ Δ(ξ)`
  and monotonicity in `R` for the singularity order;
* `convex_partialOkounkovBody`, `isCompact_partialOkounkovBody`,
  `interior_partialOkounkovBody_nonempty`, `partialOkounkovBody_convexBody`
  (`tok:partial-convex`, DRWNXZ Proposition 5.2): `Δ(ξ; R)` is a convex body with nonempty
  interior for a Kähler current `R ∈ 𝒜(ξ)` (in particular for `R ∈ 𝒜ᵍ(ξ)`).

Proof of the interior (DRWNXZ Prop. 5.2): if `θ + dd^c ψ ≥ κ` (`κ` Kähler) then for every
`s ∈ 𝒢({κ})` the potential `ψ + s` is `θ`-psh with analytic singularities, more singular than
`ψ` (`s` is bounded above) and `ν(ψ + s) = ν(ψ) + ν(s)`; hence `ν(ψ) + Δ(κ) ⊆ Δ(ξ; R)`, and
`Δ(κ)` has nonempty interior (`TranscendentalBody.interior_tradOkounkovBody_kahler_nonempty`).
The source's `R - εω + εS` is the same construction with `κ = εω`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set
open scoped Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore

section Def

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)

/-- **The partial Okounkov body** `Δ_{Y•}(ξ; R) = closure ν(Ω(ξ; R))` (DRWNXZ Definition 5.1,
blueprint `tok:partial-def`), `ξ = {θ}`, `R = θ + dd^c ψ`: the closure of the valuations of the
gentle Kähler currents in `ξ` more singular than `R`. (DRWNXZ use it for Kähler currents
`R ∈ 𝒜ᵍ(ξ)`; these hypotheses are on the theorems below.) -/
def partialOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) (ψ : F.carrier → EReal) :
    Set (Fin n → ℝ) :=
  closure (flagValuation F '' gentleKahlerCurrentsBelow θ ψ)

variable {F}

theorem isClosed_partialOkounkovBody (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) : IsClosed (partialOkounkovBody F θ ψ) :=
  isClosed_closure

/-- `Δ(ξ; R) ⊆ Δ(ξ)`. -/
theorem partialOkounkovBody_subset_tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) : partialOkounkovBody F θ ψ ⊆ tradOkounkovBody F θ :=
  closure_minimal ((image_mono (gentleKahlerCurrentsBelow_subset ψ)).trans
    (image_gentleKahlerCurrents_subset_tradOkounkovBody θ)) (isClosed_tradOkounkovBody θ)

/-- `R ⪯ R'` gives `Δ(ξ; R) ⊆ Δ(ξ; R')`. -/
theorem partialOkounkovBody_mono (θ : ClosedRealOneOneForm n F.carrier) {ψ ψ' : F.carrier → EReal}
    (h : SingularityLE ψ ψ') : partialOkounkovBody F θ ψ ⊆ partialOkounkovBody F θ ψ' :=
  closure_mono (image_mono (gentleKahlerCurrentsBelow_mono h))

/-- `Δ(ξ; R)` only depends on the singularity type of `R`. -/
theorem partialOkounkovBody_congr (θ : ClosedRealOneOneForm n F.carrier) {ψ ψ' : F.carrier → EReal}
    (h : SingularityLE ψ ψ') (h' : SingularityLE ψ' ψ) :
    partialOkounkovBody F θ ψ = partialOkounkovBody F θ ψ' :=
  (partialOkounkovBody_mono θ h).antisymm (partialOkounkovBody_mono θ h')

/-- `ν(T) ∈ Δ(ξ; R)` for `T ∈ Ω(ξ; R)`. -/
theorem flagValuation_mem_partialOkounkovBody {θ : ClosedRealOneOneForm n F.carrier}
    {ψ φ : F.carrier → EReal} (hφ : φ ∈ gentleKahlerCurrentsBelow θ ψ) :
    flagValuation F φ ∈ partialOkounkovBody F θ ψ :=
  subset_closure ⟨φ, hφ, rfl⟩

/-- `ν(R) ∈ Δ(ξ; R)` for `R ∈ Ω(ξ)`. -/
theorem flagValuation_self_mem_partialOkounkovBody {θ : ClosedRealOneOneForm n F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ gentleKahlerCurrents θ) :
    flagValuation F ψ ∈ partialOkounkovBody F θ ψ :=
  flagValuation_mem_partialOkounkovBody (self_mem_gentleKahlerCurrentsBelow hψ)

/-- `Δ(ξ; R) ≠ ∅` for `R ∈ Ω(ξ)`. -/
theorem partialOkounkovBody_nonempty_of_mem {θ : ClosedRealOneOneForm n F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ gentleKahlerCurrents θ) :
    (partialOkounkovBody F θ ψ).Nonempty :=
  ⟨_, flagValuation_self_mem_partialOkounkovBody hψ⟩

/-- **`tok:partial-convex`, compactness**: `Δ(ξ; R)` is compact (a closed subset of the compact
`Δ(ξ)`). -/
theorem isCompact_partialOkounkovBody (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) : IsCompact (partialOkounkovBody F θ ψ) :=
  (TranscendentalBody.isCompact_tradOkounkovBody θ).of_isClosed_subset
    (isClosed_partialOkounkovBody θ ψ) (partialOkounkovBody_subset_tradOkounkovBody θ ψ)

/-- `ν(Ω(ξ; R))` is closed under rational convex combinations (`tok:gentle-sum` and linearity
of the valuation; every `R`). -/
theorem ratConvex_image_gentleKahlerCurrentsBelow (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) :
    ∀ x ∈ flagValuation F '' gentleKahlerCurrentsBelow θ ψ,
      ∀ y ∈ flagValuation F '' gentleKahlerCurrentsBelow θ ψ, ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
        (t : ℝ) • x + (1 - (t : ℝ)) • y ∈ flagValuation F '' gentleKahlerCurrentsBelow θ ψ := by
  rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ t ht0 ht1
  have hs : (0 : ℚ) ≤ 1 - t := by linarith
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have hsR : (0 : ℝ) ≤ 1 - (t : ℝ) := by
    have : ((1 - t : ℚ) : ℝ) = 1 - (t : ℝ) := by push_cast; ring
    rw [← this]; exact_mod_cast hs
  set χ : F.carrier → EReal := fun x => ((t : ℝ) : EReal) * φ x + ((1 - (t : ℝ) : ℝ) : EReal) * φ' x
    with hχ
  have hform : ((t : ℝ) • θ + (((1 - t : ℚ)) : ℝ) • θ) = θ := by
    rw [← add_smul]
    push_cast
    simp
  have hcast : (((1 - t : ℚ) : ℝ) : EReal) = ((1 - (t : ℝ) : ℝ) : EReal) := by push_cast; rfl
  -- `χ ∈ Ω(ξ)`
  have hχΩ : χ ∈ gentleKahlerCurrents θ := by
    rcases ht0.lt_or_eq with htpos | htzero
    · have h := add_smul_mem_gentleKahlerCurrents hφ.1 hφ'.1.1 htpos hs
      rw [hform] at h
      simpa only [hχ, hcast] using h
    · -- `t = 0`: then `1 - t > 0`
      have h := add_smul_mem_gentleKahlerCurrents hφ'.1 hφ.1.1 (a := 1 - t) (b := t)
        (by rw [← htzero]; norm_num) ht0
      have hform' : ((((1 - t : ℚ)) : ℝ) • θ + (t : ℝ) • θ) = θ := by
        rw [add_comm]; exact hform
      rw [hform'] at h
      have hfun : (fun x => (((1 - t : ℚ) : ℝ) : EReal) * φ' x + ((t : ℝ) : EReal) * φ x) = χ := by
        funext x
        rw [hχ, hcast, add_comm]
      rwa [hfun] at h
  -- `χ ⪯ ψ`
  have hχψ : SingularityLE χ ψ := by
    refine singularityLE_trans
      (TranscendentalDensity.singularityLE_add (TranscendentalDensity.singularityLE_smul hφ.2 ht0R)
        (TranscendentalDensity.singularityLE_smul hφ'.2 hsR))
      (TranscendentalDensity.singularityLE_of_eq fun x => ?_)
    rw [TranscendentalDensity.ereal_add_smul_self ht0R hsR, add_sub_cancel, EReal.coe_one,
      one_mul]
  refine ⟨χ, ⟨hχΩ, hχψ⟩, ?_⟩
  rw [hχ, flagValuation_add_smul (isThetaPshPotential_of_mem_gentleCurrents hφ.1.1)
    (isThetaPshPotential_of_mem_gentleCurrents hφ'.1.1) ht0R hsR]

/-- **`tok:partial-convex`, convexity**: `Δ(ξ; R)` is convex (every `R`). -/
theorem convex_partialOkounkovBody (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) : Convex ℝ (partialOkounkovBody F θ ψ) :=
  TranscendentalBody.convex_closure_of_ratConvex (ratConvex_image_gentleKahlerCurrentsBelow θ ψ)

end Def

/-! ### Analytic currents and the interior -/

section Interior

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **`tok:partial-analytic`** in the language of partial bodies (DRWNXZ Lemma 5.3): for a
Kähler current `R = θ + dd^c ψ ∈ 𝒜(ξ)`, `Δ(ξ; R) = closure ν(𝒜(ξ; R))`. -/
theorem partialOkounkovBody_eq_closure_analytic {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    partialOkounkovBody F θ ψ = closure (flagValuation F '' analyticCurrentsBelow θ ψ) :=
  TranscendentalDensity.partialAnalyticStatement m F θ ψ hK hA

/-- `ν(T) ∈ Δ(ξ; R)` for `T ∈ 𝒜(ξ; R)`, `R ∈ 𝒜(ξ)` a Kähler current. -/
theorem flagValuation_mem_partialOkounkovBody_of_analytic
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ)
    (hφ : φ ∈ analyticCurrentsBelow θ ψ) : flagValuation F φ ∈ partialOkounkovBody F θ ψ := by
  rw [partialOkounkovBody_eq_closure_analytic hK hA]
  exact subset_closure ⟨φ, hφ, rfl⟩

/-- `ν(R) ∈ Δ(ξ; R)` for a Kähler current `R ∈ 𝒜(ξ)`. -/
theorem flagValuation_self_mem_partialOkounkovBody_of_analytic
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    flagValuation F ψ ∈ partialOkounkovBody F θ ψ :=
  flagValuation_mem_partialOkounkovBody_of_analytic hK hA ⟨hA, singularityLE_refl ψ⟩

/-- **The translated body `ν(R) + Δ(κ)` lies in `Δ(ξ; R)`** (DRWNXZ Proposition 5.2, proof): if
`θ + dd^c ψ ≥ κ` with `ψ` analytic, then `ν(ψ) + Δ(κ) ⊆ Δ(ξ; R)`. -/
theorem vadd_tradOkounkovBody_subset_partialOkounkovBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    {κ : KahlerBackground (m + 1) F.carrier} (hκ : IsThetaPshPotential (θ - κ.form).val ψ)
    (hA : ψ ∈ analyticCurrents θ) :
    flagValuation F ψ +ᵥ tradOkounkovBody F κ.form ⊆ partialOkounkovBody F θ ψ := by
  have hK : IsKahlerCurrentPotential θ ψ := ⟨κ, hκ⟩
  have hψA : ψ ∈ analyticCurrents (θ - κ.form) := ⟨hκ, hA.2⟩
  -- `ν(ψ) + ν(𝒢(κ)) ⊆ ν(𝒜(ξ; R))`
  have hsub : flagValuation F ψ +ᵥ flagValuation F '' gentleCurrents κ.form ⊆
      flagValuation F '' analyticCurrentsBelow θ ψ := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hsA : s ∈ analyticCurrents κ.form := gentleCurrents_subset_analyticCurrents _ hs
    have h := add_smul_mem_analyticCurrents hψA hsA (a := 1) (b := 1) zero_le_one zero_le_one
    have hform : ((1 : ℚ) : ℝ) • (θ - κ.form) + ((1 : ℚ) : ℝ) • κ.form = θ := by
      push_cast
      simp
    rw [hform] at h
    have hfun : (fun x => (((1 : ℚ) : ℝ) : EReal) * ψ x + (((1 : ℚ) : ℝ) : EReal) * s x) =
        fun x => ψ x + s x := by
      funext x
      push_cast
      simp
    rw [hfun] at h
    obtain ⟨C, hC⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hsA.1
    have hle : SingularityLE (fun x => ψ x + s x) ψ :=
      ⟨C, fun x _ => add_le_add le_rfl (hC x)⟩
    refine ⟨_, ⟨h, hle⟩, ?_⟩
    have hν := flagValuation_add_smul (F := F) hκ hsA.1 (a := 1) (b := 1) zero_le_one zero_le_one
    have hfun' : (fun x => ((1 : ℝ) : EReal) * ψ x + ((1 : ℝ) : EReal) * s x) =
        fun x => ψ x + s x := by
      funext x
      simp
    rw [hfun', one_smul, one_smul] at hν
    rw [hν]
    rfl
  rw [partialOkounkovBody_eq_closure_analytic hK hA, tradOkounkovBody_eq_closure_image]
  have hcont : Continuous (fun x : Fin (m + 1) → ℝ => flagValuation F ψ +ᵥ x) :=
    continuous_const.add continuous_id
  calc flagValuation F ψ +ᵥ closure (flagValuation F '' gentleCurrents κ.form)
      = (fun x => flagValuation F ψ +ᵥ x) '' closure (flagValuation F '' gentleCurrents κ.form) :=
        rfl
    _ ⊆ closure ((fun x => flagValuation F ψ +ᵥ x) '' (flagValuation F '' gentleCurrents κ.form)) :=
        image_closure_subset_closure_image hcont
    _ ⊆ closure (flagValuation F '' analyticCurrentsBelow θ ψ) := closure_mono hsub

/-- **`tok:partial-convex`, interior** (DRWNXZ Proposition 5.2): `Δ(ξ; R)` has nonempty interior
for a Kähler current `R ∈ 𝒜(ξ)`. -/
theorem interior_partialOkounkovBody_nonempty {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    (interior (partialOkounkovBody F θ ψ)).Nonempty := by
  obtain ⟨κ, hκ⟩ := hK
  obtain ⟨q, hq⟩ := TranscendentalBody.interior_tradOkounkovBody_kahler_nonempty F κ
  refine ⟨flagValuation F ψ +ᵥ q,
    interior_mono (vadd_tradOkounkovBody_subset_partialOkounkovBody hκ hA) ?_⟩
  rw [interior_vadd]
  exact vadd_mem_vadd_set hq

/-- **`tok:partial-convex`** (DRWNXZ Proposition 5.2): for a Kähler current `R ∈ 𝒜(ξ)` (in
particular `R ∈ 𝒜ᵍ(ξ)`), `Δ(ξ; R)` is a convex body with nonempty interior: convex, compact,
with nonempty interior (hence nonempty), and contained in `Δ(ξ)`. -/
theorem partialOkounkovBody_convexBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    Convex ℝ (partialOkounkovBody F θ ψ) ∧ IsCompact (partialOkounkovBody F θ ψ) ∧
      (interior (partialOkounkovBody F θ ψ)).Nonempty ∧
        partialOkounkovBody F θ ψ ⊆ tradOkounkovBody F θ :=
  ⟨convex_partialOkounkovBody θ ψ, isCompact_partialOkounkovBody θ ψ,
    interior_partialOkounkovBody_nonempty hK hA, partialOkounkovBody_subset_tradOkounkovBody θ ψ⟩

end Interior

end SGPT.Okounkov.TranscendentalPartial
