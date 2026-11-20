import SGPT.NPP.NonPluripolarCurrent4Bounded
import SGPT.NPP.NonPluripolarClosedManifold

/-!
# Bounded factors of non-pluripolar products on a complex manifold

Source: `chapter_npp.tex`, `prop:npp1` (3), second sentence, and `rmk:extensionBT` ("Given a
closed positive current `T`, one can also define the product `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p ∧ T` in a
very similar way"); Xia, *Foundations of pluripotential theory*,
`prop:nonpluripolar-bounded-factor-compatibility`.

`M` is a complex manifold of dimension `n` (mathlib's holomorphic atlas); currents are S17's chart
families `SGPT.NPP.PositiveCurrent`, the relative Bedford–Taylor product of `rmk:extensionBT` is
given in every chart by `SGPT.NPP.bedfordTaylorRelInChart`.

* **`nonPluripolarProduct_append_bounded_inChart`** — `prop:npp1` (3), second sentence: for
  locally bounded psh `v₁, …, v_q` and psh `φ_{q+1}, …, φ_p` on `M` with
  `T = ⟨dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` well defined, the non-pluripolar product of the concatenated
  tuple is well defined, and its expression in every chart is the relative Bedford–Taylor product
  `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T` of `rmk:extensionBT`.
* `exists_bedfordTaylorRel_of_nonPluripolarProduct` — `rmk:extensionBT` for a base `T` that is a
  non-pluripolar product (in particular `T = [M]`): the chart expressions
  `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T` glue to a closed positive current on `M`.
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

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The concatenation of a tuple of locally bounded psh functions and a tuple of psh functions is a
tuple of psh functions. -/
theorem manifoldPSH_append {q p' : ℕ} {v : Fin q → M → ℝ}
    (hv : ∀ i, IsLocallyBoundedPSH (n := n) (v i)) {φ : Fin p' → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) :
    ∀ i, SGPT.PSH.ManifoldPSH (n := n) (Fin.append (fun i x => (v i x : EReal)) φ i) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · rw [Fin.append_left]
    exact (hv i).1
  · rw [Fin.append_right]
    exact hφ j

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- Coordinate expressions of a concatenated tuple. -/
theorem append_comp_chart {q p' : ℕ} (v : Fin q → M → ℝ) (φ : Fin p' → M → EReal)
    (e : ComplexChart n M) :
    (fun i z => Fin.append (fun i x => (v i x : EReal)) φ i (e.val.symm z)) =
      Fin.append (fun i z => (v i (e.val.symm z) : EReal)) fun j z => φ j (e.val.symm z) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- **`prop:npp1` (3), second sentence, on a complex manifold**: for locally bounded psh
`v₁, …, v_q` and psh `φ_{q+1}, …, φ_p` on `M` with `T = ⟨dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` well
defined, `⟨dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` is well defined and, in every
chart, equals the relative Bedford–Taylor product `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T`
(`rmk:extensionBT`, `bedfordTaylorRelInChart`). -/
theorem nonPluripolarProduct_append_bounded_inChart {q r p' : ℕ} (hqp' : r + q + p' = n)
    (hqp : r + (q + p') = n) {v : Fin q → M → ℝ} (hv : ∀ i, IsLocallyBoundedPSH (n := n) (v i))
    {φ : Fin p' → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp' φ) :
    ∃ hW' : IsNonPluripolarWellDefined hqp (Fin.append (fun i x => (v i x : EReal)) φ),
      ∀ e : ComplexChart n M,
        (nonPluripolarProduct hqp (Fin.append (fun i x => (v i x : EReal)) φ)
          (manifoldPSH_append hv hφ) hW').inChart e =
          bedfordTaylorRelInChart (nonPluripolarProduct hqp' φ hφ hW) v e := by
  have hloc := fun e : ComplexChart n M =>
    NonPluripolarCurrent.nonPluripolarProduct_append_bounded q hqp' hqp
      (v := fun i z => v i (e.val.symm z)) (fun i => (hv i).chart e)
      (φ := fun j z => φ j (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hW e)
  have hW' : IsNonPluripolarWellDefined hqp (Fin.append (fun i x => (v i x : EReal)) φ) := by
    intro e
    change NonPluripolarCurrent.IsWellDefinedOn hqp (chartTarget e)
      (fun i z => Fin.append (fun i x => (v i x : EReal)) φ i (e.val.symm z))
    rw [append_comp_chart]
    exact (hloc e).1
  refine ⟨hW', fun e => ?_⟩
  change NonPluripolarCurrent.nonPluripolarProduct hqp (chartTarget e)
    (fun i z => Fin.append (fun i x => (v i x : EReal)) φ i (e.val.symm z)) = _
  rw [append_comp_chart]
  exact (hloc e).2

/-- **`rmk:extensionBT` for a non-pluripolar base current**: for locally bounded psh
`v₁, …, v_q` and a well-defined non-pluripolar product `T = ⟨dd^c φ_{q+1} ∧ ⋯ ∧ dd^c φ_p⟩` on `M`
(for `p = q`, `T = [M]`), the coordinate expressions `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T` of
`bedfordTaylorRelInChart` are the chart expressions of one closed positive current on `M`. -/
theorem exists_bedfordTaylorRel_of_nonPluripolarProduct {q r p' : ℕ} (hqp' : r + q + p' = n)
    {v : Fin q → M → ℝ} (hv : ∀ i, IsLocallyBoundedPSH (n := n) (v i))
    {φ : Fin p' → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp' φ) :
    ∃ R : PositiveCurrent n M r, R.IsClosed ∧
      ∀ e : ComplexChart n M, R.inChart e =
        bedfordTaylorRelInChart (nonPluripolarProduct hqp' φ hφ hW) v e := by
  obtain ⟨hW', h⟩ := nonPluripolarProduct_append_bounded_inChart hqp' (by omega) hv hφ hW
  exact ⟨_, isClosed_nonPluripolarProduct _ (manifoldPSH_append hv hφ) hW', h⟩

end SGPT.NPP
