import SGPT.NPP.NonPluripolarClosedLocal
import SGPT.NPP.NonPluripolarCurrent2Opens
import SGPT.NPP.NonPluripolarCurrent3Currents

/-!
# Closedness of non-pluripolar products on complex manifolds

Source: `chapter_npp.tex`, `prop:npp1` (5) ("the non-pluripolar product is a closed positive
current") and `def:npp:L146` ("Then `T₁ ∧ ⋯ ∧ T_p` is a closed positive `(p,p)`-current");
Xia, *Foundations of pluripotential theory*, `thm:nonpluripolar-product-closed` and the paragraph
after `prop:nonpluripolar-local-calculus` ("the local products then glue to a positive current on
`X`, which is closed by `thm:nonpluripolar-product-closed`").

Currents on the complex manifold `M` are S17's chart families (`SGPT.NPP.PositiveCurrent`), and a
current is closed when all its chart expressions are (`PositiveCurrent.IsClosed`, the closedness
used for every current on `M` in the project).

* `isClosedAny_of_local` — closedness of a local current is a local property (partition of unity
  on test functions, `LocalBedfordTaylorDecreasing.exists_sum_extTest`).
* `isClosed_nonPluripolarProduct` — `⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` (`def:npp:L69`) is closed in every
  degree (`prop:npp1` (5)); `isClosed_nonPluripolarProductOfOpens` — the same for the product
  defined under the source quantifiers of `eq:welldefinepluri` (S24).
* `isClosed_currentProduct` — the product `T₁ ∧ ⋯ ∧ T_p` of positive `(1,1)`-currents with local
  potentials (`def:npp:L146`, S29) is closed in every degree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

/-! ### Closedness is local -/

section Local

variable {n : ℕ}

set_option hygiene false in
local notation "E" => ComplexModel n

/-- **Closedness of a current is a local property**: a current on `U ⊆ ℂⁿ` whose restrictions to
open neighbourhoods of all points of `U` are closed is closed. -/
theorem isClosedAny_of_local {U : Opens E} {k : ℕ} {S : LocalProductCurrent n U k}
    (h : ∀ x ∈ (U : Set E), ∃ (V : Opens E) (hVU : V ≤ U), x ∈ V ∧
      IsClosedAny k (restrict hVU S)) : IsClosedAny k S := by
  match k, S, h with
  | 0, _, _ => trivial
  | k + 1, S, h =>
    classical
    choose! V hVU hxV hV using h
    intro ℓ γ
    ext φ
    simp only [_root_.sum_apply, dDist_apply, _root_.zero_apply, Finset.sum_neg_distrib,
      neg_eq_zero]
    obtain ⟨s, ψ, hφ⟩ := LocalBedfordTaylorDecreasing.exists_sum_extTest
      (fun i : (U : Set E) => V i) (fun i => hVU i i.2) (fun x hx => ⟨⟨x, hx⟩, hxV x hx⟩) φ
    rw [hφ]
    simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 := IsClosedCurrent.apply_eq_zero (hV i i.2) ℓ γ (ψ i)
    simp only [LocalBedfordTaylorLocality.restrict_apply] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun a _ => congrArg _ (dTest_extTest _ _ _)

end Local

/-! ### Products of psh functions -/

section Psh

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

variable {p q : ℕ} (hqp : q + p = n)

/-- **`prop:npp1` (5), closedness in every degree**: the non-pluripolar product
`⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` of psh functions on the complex manifold `M` (`def:npp:L69`) is a
closed positive current (positivity is part of `PositiveCurrent`). -/
theorem isClosed_nonPluripolarProduct {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ) :
    (nonPluripolarProduct hqp φ hφ hW).IsClosed := fun e =>
  isClosedAny_nonPluripolarProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)

/-- The same for the product defined under the source quantifiers of `eq:welldefinepluri`
(`nonPluripolarProductOfOpens`). -/
theorem isClosed_nonPluripolarProductOfOpens [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {φ : Fin p → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefinedOnOpens hqp φ hφ) :
    (nonPluripolarProductOfOpens hqp hφ hW).IsClosed :=
  isClosed_nonPluripolarProduct hqp hφ _

end Psh

/-! ### Products of closed positive `(1,1)`-currents -/

section Currents

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

variable {p q : ℕ} (hqp : q + p = m + 1)

/-- **`def:npp:L146`: `T₁ ∧ ⋯ ∧ T_p` is a closed positive `(p,p)`-current**, in every degree:
its restriction to the coordinate expression of every member `U` of the chosen cover is the local
non-pluripolar product of the local potentials, which is closed
(`isClosedAny_nonPluripolarProduct`), and closedness is local (`isClosedAny_of_local`). -/
theorem isClosed_currentProduct {T : Fin p → PositiveCurrent (m + 1) M m}
    (hT : IsCurrentProductWellDefined hqp T) : (currentProduct hqp T hT).IsClosed := by
  intro e
  refine isClosedAny_of_local fun z hz => ?_
  obtain ⟨U, hzU⟩ := hT.chartDomain_cover e z hz
  refine ⟨chartDomain e U.1, chartDomain_le e U.1, hzU, ?_⟩
  change IsClosedAny q (restrict (chartDomain_le e U.1) (hT.productInChart e))
  rw [hT.restrict_productInChart e U]
  exact isClosedAny_nonPluripolarProduct hqp ((hT.pot_spec U.2).1.chartPsh e)
    ((hT.pot_spec U.2).2 e)

end Currents

end SGPT.NPP
