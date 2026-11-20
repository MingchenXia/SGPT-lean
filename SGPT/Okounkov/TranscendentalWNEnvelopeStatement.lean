import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Lipschitz bound from a Laplacian bound: statement (package WN-ENV)

Blueprint node `tok-wn:lipschitz` of the WN chapter (`claude-tok-wn`), the Riesz-representation
step of D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted
volumes of big classes*, arXiv:2103.03660, Corollary 7.6 (`references/wn21-restricted-volume`).

This file contains the **statement only** (`def … : Prop`); nothing is asserted.  It is the
interface for the package WN-KEY (`tok-wn:convergence`), which applies it to the rescaled fibre
restrictions `h(w) = (v_k(z, e^{-k/2} w) + k)/C`.

## Formal conventions

* The Laplacian is Mathlib's `Δ` on `ℂ` (`∂²/∂x² + ∂²/∂y²`).
* "`|Δh| ≤ 1` as distributions on the unit disc" is `|∫ h Δφ| ≤ ∫ |φ|` for every smooth `φ`
  with compact support in the open unit disc `D`; this says that the distribution `Δh` on `D` is a
  function bounded by `1` almost everywhere.
* `h` is continuous on the closed disc, so that the pointwise values in the conclusion are those of
  the continuous representative (the blueprint's "function on the closed unit disc"; in WN21 `h` is
  the restriction of a continuous envelope, the uniform limit of Berman's smooth approximants).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Metric MeasureTheory Laplacian

/-- **`tok-wn:lipschitz`** (WN21 Corollary 7.6): there is a universal constant `A` such that
every function `h` continuous on the closed unit disc of `ℂ` with `|h| ≤ 1` there and `|Δh| ≤ 1`
as distributions on the open unit disc satisfies `|h(w) - h(0)| ≤ A |w|` for `|w| ≤ 1/2`. -/
def LipschitzOfLaplacianStatement : Prop :=
  ∃ A : ℝ, ∀ h : ℂ → ℝ, ContinuousOn h (closedBall 0 1) →
    (∀ z ∈ closedBall (0 : ℂ) 1, |h z| ≤ 1) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      |∫ z, h z * Δ φ z| ≤ ∫ z, |φ z|) →
    ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → |h w - h 0| ≤ A * ‖w‖

end SGPT.Okounkov.TranscendentalWN
