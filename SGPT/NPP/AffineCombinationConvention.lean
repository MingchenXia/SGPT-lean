import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-!
# The convention for `t φ + (1 - t) ψ`

Source `rmk:linearcompsh` (chapter `chapter_npp.tex`): for quasi-psh `φ, ψ`
the expression `t φ + (1 - t) ψ` is read with the convention that at `t = 0`
its value is `ψ` and at `t = 1` its value is `φ` (so no product `0 · (-∞)` has
to be interpreted).

`sourceAffineCombination` is that convention, literally.  We show that it agrees
with the existing pointwise combination `ThetaPshConvexCombination.convexComb`
(whose `EReal` arithmetic has `0 * a = 0` for every `a`), so all existing results
about `convexComb` are results about the book's expression; and that the
combination of two source `θ`-psh functions is source `θ`-psh for `t ∈ [0, 1]`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

section Convention

variable {X : Type*}

/-- Source `rmk:linearcompsh`: `t φ + (1-t) ψ`, with value `ψ` at `t = 0` and
`φ` at `t = 1`. -/
def sourceAffineCombination (t : ℝ) (φ ψ : X → EReal) : X → EReal := fun x =>
  if t = 0 then ψ x else if t = 1 then φ x else
    (t : EReal) * φ x + ((1 - t : ℝ) : EReal) * ψ x

@[simp] theorem sourceAffineCombination_zero (φ ψ : X → EReal) :
    sourceAffineCombination 0 φ ψ = ψ := by
  funext x
  simp [sourceAffineCombination]

@[simp] theorem sourceAffineCombination_one (φ ψ : X → EReal) :
    sourceAffineCombination 1 φ ψ = φ := by
  funext x
  simp [sourceAffineCombination]

theorem sourceAffineCombination_of_ne {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (φ ψ : X → EReal) (x : X) :
    sourceAffineCombination t φ ψ x = (t : EReal) * φ x + ((1 - t : ℝ) : EReal) * ψ x := by
  simp [sourceAffineCombination, h0, h1]

/-- The convention is exactly realized by the `EReal` arithmetic of the existing
pointwise combination `convexComb`, for every real `t`. -/
theorem sourceAffineCombination_eq_convexComb (t : ℝ) (φ ψ : X → EReal) :
    sourceAffineCombination t φ ψ = ThetaPshConvexCombination.convexComb t φ ψ := by
  funext x
  rw [ThetaPshConvexCombination.convexComb_apply]
  by_cases h0 : t = 0
  · subst h0
    simp [sourceAffineCombination]
  by_cases h1 : t = 1
  · subst h1
    simp [sourceAffineCombination]
  exact sourceAffineCombination_of_ne h0 h1 φ ψ x

end Convention

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- With the convention of source `rmk:linearcompsh`, `t φ + (1-t) ψ` is again
source `θ`-psh for every `t ∈ [0, 1]`, including both endpoints. -/
theorem isThetaPSH_sourceAffineCombination
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofFixedModel n M).IsThetaPSH θ (sourceAffineCombination t φ ψ) := by
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0
    simpa using hψ
  rcases ht1.eq_or_lt with h1 | h1
  · subst h1
    simpa using hφ
  rw [sourceAffineCombination_eq_convexComb, isThetaPSH_iff_nativeThetaPotential]
  exact ThetaPshConvexCombination.isThetaPshPotential_convexComb
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
    ((isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ) h0 h1

end SGPT.NPP
