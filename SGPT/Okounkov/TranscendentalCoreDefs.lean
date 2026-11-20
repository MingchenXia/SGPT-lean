import SGPT.Okounkov.TranscendentalOkounkovBody
import SGPT.PSH.SingularityOrder
import SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData

/-!
# Classes of currents with analytic singularities (transcendental Okounkov bodies)

Source: blueprint node `tok:def-classes` (chapter `claude-okounkov-transcendental`), i.e.
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ),
Definitions 2.2 and 2.4 and Section 5, and the generating set of the book's `def:tradOk`.

Let `ξ = {θ}` be the class of a closed real smooth `(1,1)`-form `θ` on a complex manifold `X`.

* `𝒜(ξ)`: the currents `θ + dd^c φ`, `φ ∈ PSH(X, θ)`, with analytic singularities, i.e. near
  every point `φ = c log ∑ |f_i|² + O(1)` with `c ∈ ℚ_{>0}` and finitely many holomorphic `f_i`
  (`analyticCurrents`);
* `𝒜ᵍ(ξ) ⊆ 𝒜(ξ)`: those of a global type `(c, 𝓘)` with a coherent ideal sheaf `𝓘`
  (`globalAnalyticCurrents`);
* `𝒢(ξ) ⊆ 𝒜ᵍ(ξ)`: those with gentle analytic singularities (source `def:analy-sing`; the
  generating set of the book's Okounkov body `def:tradOk`) (`gentleCurrents`);
* `Ω(ξ) ⊆ 𝒢(ξ)`: the Kähler currents in `𝒢(ξ)` (`gentleKahlerCurrents`);
* `𝒜(ξ; R) = {T ∈ 𝒜(ξ) : T ⪯ R}` and `Ω(ξ; R) = {T ∈ Ω(ξ) : T ⪯ R}`, where `T ⪯ R` means that
  `T` is more singular than `R` (`φ ≤ ψ + C` for potentials `φ`, `ψ` of `T`, `R`; DRWNXZ §2)
  (`analyticCurrentsBelow`, `gentleKahlerCurrentsBelow`).

## Formal conventions

A current `T ∈ 𝒵₊(X, ξ)` is `θ + dd^c φ` with `φ ∈ PSH(X, θ)` (source `rmk:qpshtocurrents`); as
in `SGPT.Okounkov.tradOkounkovBody` the sets above are sets of the **potentials** `φ` relative
to the fixed representative `θ` (a current determines its potential up to an additive
constant, and every condition above is insensitive to additive constants). The dependence on
`θ` only through `ξ` (`θ' = θ + dd^c g` replaces `φ` by `φ - g`) is proved in
`SGPT.Okounkov.TranscendentalCoreRepresentative`.

* Analytic singularities: TN's `HasManifoldAnalyticSingularityType` (in every holomorphic chart,
  near every point, a positive rational logarithmic presentation with bounded remainder).
* Global type: TN's `GlobalAnalyticSingularities.HasAnalyticSingularities` (a global coefficient
  `c ∈ ℚ_{>0}` and a coherent ideal `𝔞`, `φ = c log ∑ |g_i|² + O(1)` for local generators of `𝔞`).
* Gentle analytic singularities: the project's `SGPT.PSH.SourceGentleAnalyticSingularities`
  (source `def:analy-sing`; for a flag geometry this is `HasSourceGentleAnalyticSingularities`).
* Kähler currents: TN's `IsKahlerCurrentPotential` (`θ + dd^c φ ≥ ω'` for a Kähler form `ω'`).
* `T ⪯ R`: `SGPT.PSH.SingularityLE` (one global additive constant, `def:parorder`).

The valuation `ν_{Y•}(θ + dd^c φ)` of a potential is `flagValuation F φ`, the real vector of
`SGPT.Okounkov.potentialFlagValuation`; it does not depend on the background `θ`
(`flagValuation_eq`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalCore

open Set
open scoped NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.PSH

section Classes

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`𝒜(ξ)`**, `ξ = {θ}` (DRWNXZ Definition 2.2, blueprint `tok:def-classes`): the potentials
`φ ∈ PSH(X, θ)` of the currents `θ + dd^c φ` with analytic singularities (near every point, in
every holomorphic chart, `φ = c log ∑ |f_i|² + O(1)` with `c ∈ ℚ_{>0}`, `f_i` holomorphic). -/
def analyticCurrents (θ : ClosedRealOneOneForm n M) : Set (M → EReal) :=
  {φ | IsThetaPshPotential θ.val φ ∧ HasManifoldAnalyticSingularityType (n := n) φ}

/-- **`𝒜ᵍ(ξ)`** (blueprint `tok:def-classes`): the potentials `φ ∈ PSH(X, θ)` with analytic
singularities of a global type `(c, 𝓘)`, `c ∈ ℚ_{>0}`, `𝓘` a coherent ideal sheaf. -/
def globalAnalyticCurrents (θ : ClosedRealOneOneForm n M) : Set (M → EReal) :=
  {φ | IsThetaPshPotential θ.val φ ∧
    GlobalAnalyticSingularities.HasAnalyticSingularities (n := n) φ}

/-- **`𝒢(ξ)`** (blueprint `tok:def-classes`; the generating set of the book's `def:tradOk`): the
potentials `φ ∈ PSH(X, θ)` with gentle analytic singularities (source `def:analy-sing`). -/
def gentleCurrents (θ : ClosedRealOneOneForm n M) : Set (M → EReal) :=
  {φ | IsThetaPshPotential θ.val φ ∧
    ∃ (c : ℚ) (𝔞 : GermIdeal n M), SourceGentleAnalyticSingularities φ c 𝔞}

/-- **`Ω(ξ)`** (DRWNXZ Definition 2.4, blueprint `tok:def-classes`): the potentials of the
Kähler currents `θ + dd^c φ ≥ ω'` (`ω'` a Kähler form) with gentle analytic singularities. -/
def gentleKahlerCurrents (θ : ClosedRealOneOneForm n M) : Set (M → EReal) :=
  {φ | φ ∈ gentleCurrents θ ∧ IsKahlerCurrentPotential θ φ}

/-- **`𝒜(ξ; R) = {T ∈ 𝒜(ξ) : T ⪯ R}`** (DRWNXZ §5, blueprint `tok:def-classes`), for the current
`R = θ + dd^c ψ`: the potentials in `𝒜(ξ)` more singular than `ψ` (`φ ≤ ψ + C`). -/
def analyticCurrentsBelow (θ : ClosedRealOneOneForm n M) (ψ : M → EReal) : Set (M → EReal) :=
  {φ | φ ∈ analyticCurrents θ ∧ SingularityLE φ ψ}

/-- **`Ω(ξ; R) = {T ∈ Ω(ξ) : T ⪯ R}`** (DRWNXZ §5, blueprint `tok:def-classes`), for the current
`R = θ + dd^c ψ`: the potentials in `Ω(ξ)` more singular than `ψ` (`φ ≤ ψ + C`). -/
def gentleKahlerCurrentsBelow (θ : ClosedRealOneOneForm n M) (ψ : M → EReal) :
    Set (M → EReal) :=
  {φ | φ ∈ gentleKahlerCurrents θ ∧ SingularityLE φ ψ}

variable {θ : ClosedRealOneOneForm n M}

theorem isThetaPshPotential_of_mem_analyticCurrents {φ : M → EReal}
    (h : φ ∈ analyticCurrents θ) : IsThetaPshPotential θ.val φ := h.1

theorem isThetaPshPotential_of_mem_globalAnalyticCurrents {φ : M → EReal}
    (h : φ ∈ globalAnalyticCurrents θ) : IsThetaPshPotential θ.val φ := h.1

theorem isThetaPshPotential_of_mem_gentleCurrents {φ : M → EReal}
    (h : φ ∈ gentleCurrents θ) : IsThetaPshPotential θ.val φ := h.1

/-- `Ω(ξ) ⊆ 𝒢(ξ)`. -/
theorem gentleKahlerCurrents_subset_gentleCurrents :
    gentleKahlerCurrents θ ⊆ gentleCurrents θ := fun _ h => h.1

/-- Gentle analytic singularities are analytic singularities of a global type:
`𝒢(ξ) ⊆ 𝒜ᵍ(ξ)`. -/
theorem gentleCurrents_subset_globalAnalyticCurrents :
    gentleCurrents θ ⊆ globalAnalyticCurrents θ := by
  rintro φ ⟨hφ, c, 𝔞, -, hgentle⟩
  exact ⟨hφ, c, 𝔞, hgentle.2.1⟩

/-- `Ω(ξ) ⊆ 𝒜ᵍ(ξ)`. -/
theorem gentleKahlerCurrents_subset_globalAnalyticCurrents :
    gentleKahlerCurrents θ ⊆ globalAnalyticCurrents θ :=
  gentleKahlerCurrents_subset_gentleCurrents.trans gentleCurrents_subset_globalAnalyticCurrents

/-- `𝒜(ξ; R) ⊆ 𝒜(ξ)`. -/
theorem analyticCurrentsBelow_subset (ψ : M → EReal) :
    analyticCurrentsBelow θ ψ ⊆ analyticCurrents θ := fun _ h => h.1

/-- `Ω(ξ; R) ⊆ Ω(ξ)`. -/
theorem gentleKahlerCurrentsBelow_subset (ψ : M → EReal) :
    gentleKahlerCurrentsBelow θ ψ ⊆ gentleKahlerCurrents θ := fun _ h => h.1

/-- `R ∈ Ω(ξ; R)` for `R ∈ Ω(ξ)`. -/
theorem self_mem_gentleKahlerCurrentsBelow {ψ : M → EReal} (hψ : ψ ∈ gentleKahlerCurrents θ) :
    ψ ∈ gentleKahlerCurrentsBelow θ ψ :=
  ⟨hψ, singularityLE_refl ψ⟩

/-- `Ω(ξ; R)` is monotone in `R` for the singularity order. -/
theorem gentleKahlerCurrentsBelow_mono {ψ ψ' : M → EReal} (h : SingularityLE ψ ψ') :
    gentleKahlerCurrentsBelow θ ψ ⊆ gentleKahlerCurrentsBelow θ ψ' :=
  fun _ hφ => ⟨hφ.1, singularityLE_trans hφ.2 h⟩

/-- `𝒜(ξ; R)` is monotone in `R` for the singularity order. -/
theorem analyticCurrentsBelow_mono {ψ ψ' : M → EReal} (h : SingularityLE ψ ψ') :
    analyticCurrentsBelow θ ψ ⊆ analyticCurrentsBelow θ ψ' :=
  fun _ hφ => ⟨hφ.1, singularityLE_trans hφ.2 h⟩

end Classes

section Valuation

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)

open scoped Classical in
/-- The flag valuation `ν_{Y•}(θ + dd^c φ) ∈ ℝⁿ_{≥ 0}` of a quasi-psh potential `φ` (source
`def:valcurr`, the real vector of `potentialFlagValuation`). It does not depend on the
background `θ` (`flagValuation_eq`); it is `0` on functions that are not quasi-psh. -/
def flagValuation (φ : F.carrier → EReal) : Fin n → ℝ :=
  if h : ∃ θ : ClosedRealOneOneForm n F.carrier, IsThetaPshPotential θ.val φ then
    fun i => ((potentialFlagValuation F h.choose_spec i : ℝ≥0) : ℝ)
  else 0

variable {F}

/-- The valuation of a `θ`-psh potential is its `potentialFlagValuation`, for every background
`θ`. -/
theorem flagValuation_eq {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    flagValuation F φ = fun i => ((potentialFlagValuation F hφ i : ℝ≥0) : ℝ) := by
  have h : ∃ θ : ClosedRealOneOneForm n F.carrier, IsThetaPshPotential θ.val φ := ⟨θ, hφ⟩
  rw [flagValuation, dif_pos h,
    potentialFlagValuation_eq_of_iEquivalent F h.choose_spec hφ (IEquivalentOnManifold.refl φ)]

theorem flagValuation_nonneg (φ : F.carrier → EReal) (i : Fin n) : 0 ≤ flagValuation F φ i := by
  unfold flagValuation
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

/-- The valuation depends only on the multiplier-ideal class of the potential. -/
theorem flagValuation_eq_of_iEquivalent {θ σ : ClosedRealOneOneForm n F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential σ.val ψ) (hI : IEquivalentOnManifold (n := n) φ ψ) :
    flagValuation F φ = flagValuation F ψ := by
  rw [flagValuation_eq hφ, flagValuation_eq hψ, potentialFlagValuation_eq_of_iEquivalent F hφ hψ hI]

/-- Membership in `𝒢(ξ)` for a flag geometry is the gentle condition of `def:tradOk`. -/
theorem mem_gentleCurrents_iff {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal} :
    φ ∈ gentleCurrents θ ↔
      IsThetaPshPotential θ.val φ ∧ HasSourceGentleAnalyticSingularities F φ :=
  Iff.rfl

/-- The generating set of `def:tradOk` is `ν(𝒢(ξ))`. -/
theorem gentleCurrentValuations_eq_image (θ : ClosedRealOneOneForm n F.carrier) :
    gentleCurrentValuations F θ = flagValuation F '' gentleCurrents θ := by
  ext x
  constructor
  · rintro ⟨φ, hφ, hgentle, rfl⟩
    exact ⟨φ, ⟨hφ, hgentle⟩, flagValuation_eq hφ⟩
  · rintro ⟨φ, ⟨hφ, hgentle⟩, rfl⟩
    exact ⟨φ, hφ, hgentle, flagValuation_eq hφ⟩

/-- The book's Okounkov body (`def:tradOk`) is `Δ(ξ) = closure ν(𝒢(ξ))`. -/
theorem tradOkounkovBody_eq_closure_image (θ : ClosedRealOneOneForm n F.carrier) :
    tradOkounkovBody F θ = closure (flagValuation F '' gentleCurrents θ) := by
  rw [tradOkounkovBody, gentleCurrentValuations_eq_image]

/-- `ν(Ω(ξ)) ⊆ Δ(ξ)`. -/
theorem image_gentleKahlerCurrents_subset_tradOkounkovBody
    (θ : ClosedRealOneOneForm n F.carrier) :
    flagValuation F '' gentleKahlerCurrents θ ⊆ tradOkounkovBody F θ := by
  rw [tradOkounkovBody_eq_closure_image]
  exact (image_mono gentleKahlerCurrents_subset_gentleCurrents).trans subset_closure

end Valuation

end SGPT.Okounkov.TranscendentalCore
