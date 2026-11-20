import SGPT.Checks.Comparison.BJWholePointwiseMax
import SGPT.Checks.Comparison.BJCompareTranslate

/-!
# Finite maxima of translated Boucksom–Jonsson psh metrics

The Boucksom–Jonsson half of `lma:pltest` (`chapter_NApotential.tex`): for a piecewise linear
curve `A` with nodes `τ_0 > ⋯ > τ_N`, `A^An = max_i (A_{τ_i}^An + τ_i)` (`eq:psianvlinear`), and
the book concludes `A^An ∈ PSH(L^An)` from `prop:BJclosedmax` and `lma:varphian`.  Here: if every
`φ_i` lies in `PSH(L^An)` (`IsModuleTopologyPSH`), so does `max_i (φ_i + τ_i)` for arbitrary real
`τ_i`.  The analytic inputs (`lma:varphian` for `φ_i = A_{τ_i}^An`, and the equality
`sup = max` in `eq:psianvlinear`) are not part of this file.

## Main results

* `IsModuleTopologyPSH.finset_sup'`: finite pointwise maxima (`prop:BJclosedmax` iterated).
* `IsModuleTopologyPSH.finset_sup'_add_const`: `max_{i ∈ s} (φ_i + τ_i) ∈ PSH(L^An)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Printed

open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- Finite pointwise maxima of psh metrics are psh (`prop:BJclosedmax`, iterated). -/
theorem IsModuleTopologyPSH.finset_sup' {L : RationalPicardSpace X} {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (φ : ι → BerkovichPoint p → EReal)
    (h : ∀ i ∈ s, IsModuleTopologyPSH.{u} p L (φ i)) :
    IsModuleTopologyPSH.{u} p L (fun v => s.sup' hs (fun i => φ i v)) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa only [Finset.sup'_singleton] using h a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have hrest := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
    have ha' := h a (Finset.mem_cons_self a s)
    simpa only [Finset.sup'_cons hs] using IsModuleTopologyPSH.max p ha' hrest

/-- **The BJ half of `lma:pltest`.**  If every `φ_i` (`i ∈ s`) is a psh metric on `L^An`, then so
is `v ↦ max_{i ∈ s} (φ_i(v) + τ_i)` for arbitrary real `τ_i`. -/
theorem IsModuleTopologyPSH.finset_sup'_add_const {L : RationalPicardSpace X} {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (φ : ι → BerkovichPoint p → EReal) (τ : ι → ℝ)
    (h : ∀ i ∈ s, IsModuleTopologyPSH.{u} p L (φ i)) :
    IsModuleTopologyPSH.{u} p L (fun v => s.sup' hs (fun i => φ i v + (τ i : EReal))) :=
  IsModuleTopologyPSH.finset_sup' p s hs (fun i v => φ i v + (τ i : EReal))
    (fun i hi => (h i hi).add_const p (τ i))

end SGPT.NAPotential.BJ.Printed
