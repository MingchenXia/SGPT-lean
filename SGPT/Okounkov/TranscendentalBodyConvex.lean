import SGPT.Okounkov.TranscendentalBodyBasic
import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Okounkov.TranscendentalCoreValuationBounded

/-!
# The Okounkov body of a big class is a convex body

Source: blueprint node `tok:body-basic` (DRWNXZ §3 and Proposition 3.3); the book's
`thm:Okounkovtranmain`, first sentence: for a big class `α`, `Δ_{Y•}(α)` is a convex body
(nonempty, compact, convex).

* convexity: `convex_tradOkounkovBody` (`tok:gentle-sum` + linearity of `ν`);
* compactness: `isCompact_tradOkounkovBody` (closed by definition; bounded by
  `tok:valuation-bound`, `exists_flagValuation_le`);
* nonemptiness: a big class contains a Kähler current, hence (`tok:sing-decrease` (a)) a gentle
  Kähler current `T ∈ Ω(ξ)`, and `ν(T) ∈ Δ(ξ)`.

## Main results

* `exists_mem_gentleKahlerCurrents_of_isBig`: `Ω(ξ) ≠ ∅` for a big class (`tok:sing-decrease`
  (b), last clause), for every representative of the class.
* `tradOkounkovBody_nonempty`: `Δ_{Y•}(ξ) ≠ ∅` for a big class.
* `isConvexBody`: the conjunct `IsConvexBodyStatement` of the fixed target
  `OkounkovTranMainStatement`.
* `zero_mem_tradOkounkovBody`: `0 ∈ Δ(θ)` when `θ ≥ κ` for a Kähler form `κ` (in particular
  `0 ∈ Δ({ω})`, the last clause of `tok:body-basic`), and `tradOkounkovBody_subset_add`:
  `Δ(ξ) ⊆ Δ(ξ + ξ')` for such `ξ'` (the first step of `tok:kahler-limit`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Okounkov.TranscendentalCore

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **Blueprint `tok:sing-decrease` (b), last clause**: if `{θ}` is big, then `Ω({θ}) ≠ ∅`, i.e.
there is a gentle potential `ψ ∈ PSH(X, θ)` with `θ + dd^c ψ` a Kähler current. -/
theorem exists_mem_gentleKahlerCurrents_of_isBig {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (gentleKahlerCurrents θ).Nonempty := by
  obtain ⟨K⟩ := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  obtain ⟨ψ, hψ, -, -⟩ := exists_mem_gentleKahlerCurrents_ge K.strictlyPsh
  have himage := image_gentleKahlerCurrents_eq_of_class_eq (F := F) K.represents
  have hmem : flagValuation F ψ ∈ flagValuation F '' gentleKahlerCurrents θ := by
    rw [← himage]
    exact ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', -⟩ := hmem
  exact ⟨ψ', hψ'⟩

/-- **Blueprint `tok:body-basic`, nonemptiness**: `Δ_{Y•}(ξ) ≠ ∅` for a big class `ξ`. -/
theorem tradOkounkovBody_nonempty {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (tradOkounkovBody F θ).Nonempty := by
  obtain ⟨ψ, hψ⟩ := exists_mem_gentleKahlerCurrents_of_isBig (F := F) hbig
  exact ⟨_, image_gentleKahlerCurrents_subset_tradOkounkovBody θ ⟨ψ, hψ, rfl⟩⟩

/-- **Blueprint `tok:body-basic`, last clause**: if `θ - κ ≥ 0` for a Kähler form `κ` (e.g.
`θ = ω`), then `0 ∈ Δ_{Y•}(θ)`: the potential `0` of the Kähler current `θ ≥ κ` lies below a
gentle Kähler potential `ψ ≥ 0` (`tok:sing-decrease` (a)), which is bounded, so `ν(ψ) = 0`
(`tok:valuation-divisor`). -/
theorem zero_mem_tradOkounkovBody {n : ℕ} {F : OriginalFlagGeometry.{u} n}
    {θ : ClosedRealOneOneForm n F.carrier} {κ : KahlerBackground n F.carrier}
    (h : (θ - κ.form).val.IsSemipositive) : (0 : Fin n → ℝ) ∈ tradOkounkovBody F θ := by
  have h0 : IsThetaPshPotential (θ - κ.form).val (fun _ => (0 : EReal)) :=
    (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff _).mpr h
  obtain ⟨ψ, hψ, -, hle⟩ := exists_mem_gentleKahlerCurrents_ge h0
  have hν : flagValuation F ψ = 0 :=
    flagValuation_eq_zero_of_bounded (isThetaPshPotential_of_mem_gentleCurrents hψ.1)
      (C := 0) (fun x => by simpa using hle x)
  rw [← hν]
  exact image_gentleKahlerCurrents_subset_tradOkounkovBody θ ⟨ψ, hψ, rfl⟩

/-- `ν(ω) = 0`: the valuation of the current `ω` (potential `0`) vanishes (blueprint
`tok:body-basic`, `tok:valuation-divisor`). -/
theorem flagValuation_zero_potential {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    flagValuation F (fun _ => (0 : EReal)) = 0 :=
  flagValuation_eq_zero_of_bounded
    (SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy.isThetaPshPotential_zero F.omega)
    (C := 0) (fun _ => by simp)

/-- `0 ∈ Δ_{Y•}({ω})` for the Kähler form `ω` of the flag geometry (blueprint `tok:body-basic`). -/
theorem zero_mem_tradOkounkovBody_omega {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    (0 : Fin n → ℝ) ∈ tradOkounkovBody F F.omega.form := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  refine zero_mem_tradOkounkovBody (κ := KahlerBackground.smul hhalf F.omega) ?_
  have heq : F.omega.form - (KahlerBackground.smul hhalf F.omega).form =
      (1 / 2 : ℝ) • F.omega.form := by
    rw [KahlerBackground.smul_form]; module
  rw [heq]
  exact SGPT.Foundations.Analysis.Pending.KahlerDomination.isSemipositive_smul
    F.omega.isSemipositive hhalf.le

/-- `Δ(θ) ⊆ Δ(θ + θ')` if `θ' - κ ≥ 0` for a Kähler form `κ` (blueprint `tok:kahler-limit`,
first step: `Δ(ξ) ⊆ Δ(ξ + ε{ω})`). -/
theorem tradOkounkovBody_subset_add {n : ℕ} {F : OriginalFlagGeometry.{u} n}
    (θ : ClosedRealOneOneForm n F.carrier) {θ' : ClosedRealOneOneForm n F.carrier}
    {κ : KahlerBackground n F.carrier} (h : (θ' - κ.form).val.IsSemipositive) :
    tradOkounkovBody F θ ⊆ tradOkounkovBody F (θ + θ') := by
  intro x hx
  have := tradOkounkovBody_add_subset θ θ' ⟨x, hx, 0, zero_mem_tradOkounkovBody h, rfl⟩
  simpa using this

variable (F)

/-- **Source `thm:Okounkovtranmain`, first sentence** (blueprint `tok:body-basic`): for every
big class `α`, `Δ_{Y•}(α)` is a convex body (convex, compact, nonempty); the conjunct
`IsConvexBodyStatement` of the fixed target `OkounkovTranMainStatement`. -/
theorem isConvexBody : TranscendentalMain.IsConvexBodyStatement F := by
  intro α hα
  have hrep : RealBottChern.ofRepresentative (Quotient.out α) = α := Quotient.out_eq α
  refine ⟨convex_tradOkounkovBody _, isCompact_tradOkounkovBody _, ?_⟩
  rw [← hrep] at hα
  exact tradOkounkovBody_nonempty hα

end SGPT.Okounkov.TranscendentalBody
