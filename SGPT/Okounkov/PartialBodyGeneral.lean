import SGPT.Okounkov.PartialBodyKahler

/-!
# Partial Okounkov bodies: the general case

Source: the book's `def:generalPOB` and `thm:pobmain` (chapter *The theory of Okounkov bodies*,
section *Transcendental partial Okounkov bodies*, subsection *The general case*); blueprint
chapter `claude-pob`.

For `T = θ + dd^c φ ∈ 𝒵₊(X, α)` (`φ ∈ PSH(X, θ)`, `α` pseudo-effective) and a Kähler form `ω`,
the book sets `Δ_{Y•}(T) = ⋂_{j ≥ 1} Δ_{Y•}(T + j⁻¹ ω)`, where `T + j⁻¹ ω` is a Kähler current
in `α + j⁻¹ {ω}` (with potential `φ` for `θ + j⁻¹ ω`) and its body is the one of
`def:POBKahcurr` (`PartialBody.kahlerPartialBody`).

* `generalPartialBody F θ φ`: the definition, with the Kähler form `ω = F.omega.form` of the
  flag geometry; `generalPartialBody_eq_of_kahler`: the same body for every Kähler form `ω`
  ("clearly independent of the choice of `ω` by `lma:Okomonotone`");
  `generalPartialBody_eq_kahlerPartialBody`, `generalPartialBody_eq_analyticPartialBody`:
  it extends `def:POBKahcurr` and `def:POBanalsing`. No bigness is assumed (the definition
  "makes sense when `α` is only pseudo-effective").
* `thm:pobmain` (2) `generalPartialBody_subset_of_iOrder`: `T ⪯_𝓘 S` gives
  `Δ(T) ⊆ Δ(S) ⊆ Δ(α)`;
* `thm:pobmain` (3) `generalPartialBody_eq_tradOkounkovBody_of_minimal`: `Δ(T) = Δ(α)` for `T`
  with minimal singularities;
* `thm:pobmain` (6) `generalPartialBody_add_subset`: `Δ(T) + Δ(S) ⊆ Δ(T + S)` (for `T`, `S` in
  arbitrary classes).

All unconditional. The book proves (3) from (1) (volumes, i.e. `thm:Okounkovtranmain` (1)) and
(6) from (4) (`d_S`-continuity); here (3) uses `Ω(ξ) ⊆ Ω(ξ; T)` for `T` with minimal
singularities and (6) uses the sum of quasi-equisingular approximations directly.
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

/-! ### Kähler perturbations -/

section Perturbation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `T + t ω` is a Kähler current for `T ∈ 𝒵₊(X, {θ})`, `ω` Kähler, `t > 0`. -/
theorem isKahlerCurrentPotential_add_smul {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (ω : KahlerBackground n M) {t : ℝ} (ht : 0 < t) :
    IsKahlerCurrentPotential (θ + t • ω.form) φ :=
  ⟨KahlerBackground.smul ht ω, by rwa [KahlerBackground.smul_form, add_sub_cancel_right]⟩

/-- The potential of a Kähler current is `θ`-psh. -/
theorem isThetaPshPotential_of_isKahlerCurrentPotential {θ : ClosedRealOneOneForm n M}
    {φ : M → EReal} (hφ : IsKahlerCurrentPotential θ φ) : IsThetaPshPotential θ.val φ := by
  obtain ⟨κ, hκ⟩ := hφ
  refine TranscendentalBody.isThetaPshPotential_of_le hκ ?_
  rw [sub_sub_cancel]
  exact κ.isSemipositive

end Perturbation

section Flag

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `Δ(T + s ω) ⊆ Δ(T + t ω)` for `0 < s ≤ t` (`lma:Okomonotone`). -/
theorem kahlerPartialBody_add_smul_mono {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (ω : KahlerBackground (m + 1) F.carrier) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    kahlerPartialBody F (θ + s • ω.form) φ ⊆ kahlerPartialBody F (θ + t • ω.form) φ := by
  refine kahlerPartialBody_subset_of_le (isKahlerCurrentPotential_add_smul hφ ω hs) ?_
  have heq : θ + t • ω.form - (θ + s • ω.form) = (t - s) • ω.form := by module
  rw [heq]
  exact KahlerDomination.isSemipositive_smul ω.isSemipositive (by linarith)

/-- `⋂_{j ≥ 1} Δ(T + j⁻¹ ω) = ⋂_{ε > 0} Δ(T + ε ω)`. -/
theorem iInter_kahlerPartialBody_nat_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (ω : KahlerBackground (m + 1) F.carrier) :
    ⋂ j : ℕ, kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • ω.form) φ =
      ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • ω.form) φ := by
  apply Subset.antisymm
  · refine subset_iInter₂ fun ε hε => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    refine (iInter_subset _ j).trans (kahlerPartialBody_add_smul_mono hφ ω (by positivity) ?_)
    rw [inv_eq_one_div]
    exact hj.le
  · exact subset_iInter fun j => iInter₂_subset ((j : ℝ) + 1)⁻¹ (by positivity)

/-- `⋂_{ε > 0} Δ(T + ε ω) ⊆ ⋂_{ε > 0} Δ(T + ε ω')` for Kähler forms `ω`, `ω'`. -/
theorem iInter_kahlerPartialBody_subset {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (ω ω' : KahlerBackground (m + 1) F.carrier) :
    ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • ω.form) φ ⊆
      ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • ω'.form) φ := by
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω' (-ω.form)
  refine subset_iInter₂ fun ε hε => ?_
  have hεC : 0 < ε / C := div_pos hε hC
  refine (iInter₂_subset (ε / C) hεC).trans
    (kahlerPartialBody_subset_of_le (isKahlerCurrentPotential_add_smul hφ ω hεC) ?_)
  have heq : θ + ε • ω'.form - (θ + (ε / C) • ω.form) = (ε / C) • (-ω.form + C • ω'.form) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ ε hC.ne']
    module
  rw [heq]
  exact KahlerDomination.isSemipositive_smul hdom hεC.le

/-! ### The definition -/

variable (F) in
/-- **The partial Okounkov body of a closed positive current** (the book's `def:generalPOB`):
for `T = θ + dd^c φ ∈ 𝒵₊(X, α)` (`α = {θ}` pseudo-effective, `φ ∈ PSH(X, θ)`),
`Δ_{Y•}(T) = ⋂_{j ≥ 1} Δ_{Y•}(T + j⁻¹ ω)`, with the bodies of the Kähler currents
`T + j⁻¹ ω` of `def:POBKahcurr` and the Kähler form `ω = F.omega.form` (any Kähler form gives
the same body, `generalPartialBody_eq_of_kahler`). -/
def generalPartialBody (θ : ClosedRealOneOneForm (m + 1) F.carrier) (φ : F.carrier → EReal) :
    Set (Fin (m + 1) → ℝ) :=
  ⋂ j : ℕ, kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ

/-- `Δ_{Y•}(T) = ⋂_{ε > 0} Δ_{Y•}(T + ε ω)` (`ω = F.omega.form`). -/
theorem generalPartialBody_eq_iInter_pos {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    generalPartialBody F θ φ =
      ⋂ (ε : ℝ) (_ : 0 < ε), kahlerPartialBody F (θ + ε • F.omega.form) φ :=
  iInter_kahlerPartialBody_nat_eq hφ F.omega

/-- **`def:generalPOB`, independence of `ω`**: for every Kähler form `ω`,
`Δ_{Y•}(T) = ⋂_{j ≥ 1} Δ_{Y•}(T + j⁻¹ ω)`. -/
theorem generalPartialBody_eq_of_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (ω : KahlerBackground (m + 1) F.carrier) :
    generalPartialBody F θ φ = ⋂ j : ℕ, kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • ω.form) φ := by
  rw [generalPartialBody_eq_iInter_pos hφ, iInter_kahlerPartialBody_nat_eq hφ ω]
  exact (iInter_kahlerPartialBody_subset hφ F.omega ω).antisymm
    (iInter_kahlerPartialBody_subset hφ ω F.omega)

/-- **`def:generalPOB` extends `def:POBKahcurr`**: for a Kähler current `T`, the two bodies
coincide (`lma:Okomonotone`). -/
theorem generalPartialBody_eq_kahlerPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    generalPartialBody F θ φ = kahlerPartialBody F θ φ := by
  rw [generalPartialBody_eq_iInter_pos (isThetaPshPotential_of_isKahlerCurrentPotential hφ),
    ← kahlerPartialBody_eq_iInter_add_kahler hφ F.omega]

/-- **`def:generalPOB` extends `def:POBanalsing`**: for a Kähler current `T` with analytic
singularities (of a global type), `Δ_{Y•}(T)` is the body of `def:POBanalsing`. -/
theorem generalPartialBody_eq_analyticPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφA : φ ∈ globalAnalyticCurrents θ)
    (hφ : IsKahlerCurrentPotential θ φ) :
    generalPartialBody F θ φ = analyticPartialBody F θ φ := by
  rw [generalPartialBody_eq_kahlerPartialBody hφ, kahlerPartialBody_eq_analyticPartialBody hφA hφ]

/-- `Δ_{Y•}(T)` is closed. -/
theorem isClosed_generalPartialBody (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (φ : F.carrier → EReal) : IsClosed (generalPartialBody F θ φ) :=
  isClosed_iInter fun _ => isClosed_kahlerPartialBody _ φ

/-- `Δ_{Y•}(T)` is convex and compact (a convex body when nonempty, e.g. for `T` with positive
mass by `thm:pobmain` (1)). -/
theorem convex_isCompact_generalPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    Convex ℝ (generalPartialBody F θ φ) ∧ IsCompact (generalPartialBody F θ φ) := by
  have h := fun j : ℕ => kahlerPartialBody_convexBody (F := F)
    (isKahlerCurrentPotential_add_smul hφ F.omega (t := ((j : ℝ) + 1)⁻¹) (by positivity))
  exact ⟨convex_iInter fun j => (h j).1, (h 0).2.1.of_isClosed_subset
    (isClosed_generalPartialBody θ φ) (iInter_subset _ 0)⟩

/-- The DRWNXZ partial body `closure ν(Ω(ξ; T))` lies in `Δ_{Y•}(T)`. -/
theorem partialOkounkovBody_subset_generalPartialBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    partialOkounkovBody F θ φ ⊆ generalPartialBody F θ φ := by
  refine subset_iInter fun j => ?_
  have hj : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  refine (partialOkounkovBody_subset_of_le ?_ φ).trans
    (partialOkounkovBody_subset_kahlerPartialBody
      (isKahlerCurrentPotential_add_smul hφ F.omega hj))
  rw [add_sub_cancel_left]
  exact KahlerDomination.isSemipositive_smul F.omega.isSemipositive hj.le

/-- `⋂_{j ≥ 1} Δ(α + j⁻¹ {ω}) = Δ(α)` for big `α` (`thm:Okounkovtranmain` (4),
`tradOkounkovBody_eq_iInter_add_kahler`). -/
theorem iInter_tradOkounkovBody_nat_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    ⋂ j : ℕ, tradOkounkovBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) = tradOkounkovBody F θ := by
  apply Subset.antisymm
  · rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig]
    refine subset_iInter₂ fun ε hε => ?_
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε'
    refine (iInter_subset _ j).trans (tradOkounkovBody_subset_of_le ?_)
    have heq : θ + (ε : ℝ) • F.omega.form - (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) =
        ((ε : ℝ) - ((j : ℝ) + 1)⁻¹) • F.omega.form := by module
    rw [heq]
    refine KahlerDomination.isSemipositive_smul F.omega.isSemipositive ?_
    rw [inv_eq_one_div]
    linarith
  · refine subset_iInter fun j => tradOkounkovBody_subset_of_le ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by positivity)

/-! ### `thm:pobmain` (2), (3) -/

/-- **`thm:pobmain` (2)**: for `T = θ + dd^c φ`, `S = θ + dd^c ψ` in `𝒵₊(X, α)` with
`T ⪯_𝓘 S`, `Δ_{Y•}(T) ⊆ Δ_{Y•}(S)`, and `Δ_{Y•}(S) ⊆ Δ_{Y•}(α)` for big `α`. Unconditional. -/
theorem generalPartialBody_subset_of_iOrder {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) (hI : IOrderOnManifold (n := m + 1) φ ψ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    generalPartialBody F θ φ ⊆ generalPartialBody F θ ψ ∧
      generalPartialBody F θ ψ ⊆ tradOkounkovBody F θ := by
  have hK := fun (χ : F.carrier → EReal) (hχ : IsThetaPshPotential θ.val χ) (j : ℕ) =>
    isKahlerCurrentPotential_add_smul hχ F.omega (t := ((j : ℝ) + 1)⁻¹) (by positivity)
  refine ⟨iInter_mono fun j =>
    (kahlerPartialBody_subset_of_iOrder (hK φ hφ j) (hK ψ hψ j) hI).1, ?_⟩
  rw [← iInter_tradOkounkovBody_nat_eq hbig]
  exact iInter_mono fun j => (kahlerPartialBody_subset_of_iOrder (hK ψ hψ j) (hK ψ hψ j)
    (iOrderOnManifold_refl ψ)).2

/-- **`thm:pobmain` (3)**: for big `α` and `T = θ + dd^c φ ∈ 𝒵₊(X, α)` with minimal
singularities (every `T' ∈ 𝒵₊(X, α)` is more singular than `T`), `Δ_{Y•}(T) = Δ_{Y•}(α)`.
Unconditional: every gentle Kähler current of `α` lies in `Ω(ξ; T)`. -/
theorem generalPartialBody_eq_tradOkounkovBody_of_minimal
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    (hφ : IsThetaPshPotential θ.val φ)
    (hmin : ∀ ψ : F.carrier → EReal, IsThetaPshPotential θ.val ψ → SingularityLE ψ φ) :
    generalPartialBody F θ φ = tradOkounkovBody F θ := by
  refine (generalPartialBody_subset_of_iOrder hφ hφ (iOrderOnManifold_refl φ) hbig).2.antisymm ?_
  rw [TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents hbig]
  refine closure_minimal ?_ (isClosed_generalPartialBody θ φ)
  rintro _ ⟨s, hs, rfl⟩
  exact partialOkounkovBody_subset_generalPartialBody hφ (flagValuation_mem_partialOkounkovBody
    ⟨hs, hmin s (isThetaPshPotential_of_mem_gentleCurrents hs.1)⟩)

/-! ### `thm:pobmain` (6): superadditivity -/

/-- `Δ(θ; φ) + Δ(θ'; ψ) ⊆ Δ(θ + θ'; φ + ψ)` for the DRWNXZ partial bodies. -/
theorem partialOkounkovBody_add_subset (θ θ' : ClosedRealOneOneForm (m + 1) F.carrier)
    (φ ψ : F.carrier → EReal) :
    partialOkounkovBody F θ φ + partialOkounkovBody F θ' ψ ⊆
      partialOkounkovBody F (θ + θ') (fun x => φ x + ψ x) := by
  have himg : flagValuation F '' gentleKahlerCurrentsBelow θ φ +
      flagValuation F '' gentleKahlerCurrentsBelow θ' ψ ⊆
        flagValuation F '' gentleKahlerCurrentsBelow (θ + θ') (fun x => φ x + ψ x) := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, _, ⟨s', hs', rfl⟩, rfl⟩
    have hmem := add_smul_mem_gentleKahlerCurrents hs.1 hs'.1.1 (a := 1) (b := 1) one_pos
      zero_le_one
    have hform : (((1 : ℚ) : ℝ) • θ + ((1 : ℚ) : ℝ) • θ') = θ + θ' := by simp
    have hfun : (fun x => (((1 : ℚ) : ℝ) : EReal) * s x + (((1 : ℚ) : ℝ) : EReal) * s' x) =
        fun x => s x + s' x := by
      funext x
      simp
    rw [hform, hfun] at hmem
    refine ⟨_, ⟨hmem, TranscendentalDensity.singularityLE_add hs.2 hs'.2⟩, ?_⟩
    have h := flagValuation_add_smul (F := F)
      (isThetaPshPotential_of_mem_gentleCurrents hs.1.1)
      (isThetaPshPotential_of_mem_gentleCurrents hs'.1.1) (a := 1) (b := 1) zero_le_one
      zero_le_one
    have hfun' : (fun x => ((1 : ℝ) : EReal) * s x + ((1 : ℝ) : EReal) * s' x) =
        fun x => s x + s' x := by
      funext x
      simp
    rw [hfun', one_smul, one_smul] at h
    exact h
  unfold partialOkounkovBody
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hcont : Continuous (Function.uncurry (fun a b : Fin (m + 1) → ℝ => a + b)) := by fun_prop
  exact map_mem_closure₂ (f := fun a b : Fin (m + 1) → ℝ => a + b) hcont hx hy
    (fun a ha b hb => himg ⟨a, ha, b, hb, rfl⟩)

/-- The sum of two Kähler approximations is a Kähler approximation of the sum. -/
theorem IsKahlerQEA.add {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} {U V : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    (hV : IsKahlerQEA θ' ψ V) :
    IsKahlerQEA (θ + θ') (fun x => φ x + ψ x) (fun j x => U j x + V j x) := by
  refine ⟨?_, fun j => ⟨⟨isThetaPshPotential_add_from_positive_sum (hU.2 j).1.1 (hV.2 j).1.1,
    hasAnalyticSingularities_add (hU.2 j).1.2 (hV.2 j).1.2⟩, ?_⟩⟩
  · obtain ⟨ω₀, ε, hu⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
    obtain ⟨ω₁, δ, hv⟩ := native_of_sourceQuasiEquisingularApproximation hV.1
    obtain ⟨κ, hκ₀, hκ₁⟩ :=
      QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background ω₀ ω₁
    exact sourceQuasiEquisingularApproximation_of_native
      (QuasiEquisingularAddition.isQuasiEquisingularApproximation_add
        (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
          hu hκ₀)
        (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
          hv hκ₁))
  · obtain ⟨κ, hκ⟩ := (hU.2 j).2
    refine ⟨κ, ?_⟩
    have h := isThetaPshPotential_add_from_positive_sum hκ (hV.2 j).1.1
    have hform : θ - κ.form + θ' = θ + θ' - κ.form := by abel
    rwa [hform] at h

/-- **Superadditivity for Kähler currents**: `Δ_{Y•}(T) + Δ_{Y•}(S) ⊆ Δ_{Y•}(T + S)`. -/
theorem kahlerPartialBody_add_subset {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hψ : IsKahlerCurrentPotential θ' ψ) :
    kahlerPartialBody F θ φ + kahlerPartialBody F θ' ψ ⊆
      kahlerPartialBody F (θ + θ') (fun x => φ x + ψ x) := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  obtain ⟨V, hV⟩ := exists_isKahlerQEA hψ
  rw [kahlerPartialBody_eq_iInter hU, kahlerPartialBody_eq_iInter hV,
    kahlerPartialBody_eq_iInter (hU.add hV)]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rw [mem_iInter] at hx hy ⊢
  exact fun j => partialOkounkovBody_add_subset θ θ' (U j) (V j) ⟨x, hx j, y, hy j, rfl⟩

/-- **`thm:pobmain` (6)** (superadditivity, `eq:pobadditiv`): for `T = θ + dd^c φ ∈ 𝒵₊(X, α)`
and `S = θ' + dd^c ψ ∈ 𝒵₊(X, α')`, `Δ_{Y•}(T) + Δ_{Y•}(S) ⊆ Δ_{Y•}(T + S)`
(`T + S = (θ + θ') + dd^c(φ + ψ)`; the book takes `α' = α`). Unconditional. -/
theorem generalPartialBody_add_subset {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ'.val ψ) :
    generalPartialBody F θ φ + generalPartialBody F θ' ψ ⊆
      generalPartialBody F (θ + θ') (fun x => φ x + ψ x) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rw [generalPartialBody, mem_iInter] at hx hy ⊢
  intro i
  set t : ℝ := (((2 * i + 1 : ℕ) : ℝ) + 1)⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have h := kahlerPartialBody_add_subset (isKahlerCurrentPotential_add_smul hφ F.omega ht0)
    (isKahlerCurrentPotential_add_smul hψ F.omega ht0) ⟨x, hx (2 * i + 1), y, hy (2 * i + 1), rfl⟩
  have htt : t + t = ((i : ℝ) + 1)⁻¹ := by
    rw [ht]
    push_cast
    field_simp
    ring
  have hform : θ + t • F.omega.form + (θ' + t • F.omega.form) =
      θ + θ' + ((i : ℝ) + 1)⁻¹ • F.omega.form := by
    rw [← htt]
    module
  rwa [hform] at h

end Flag

end SGPT.Okounkov.PartialBody
