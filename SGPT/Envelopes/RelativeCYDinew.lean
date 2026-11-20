import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-!
# Dinew's lower bound for convex combinations against a common measure (statement)

The uniqueness part of source `thm:Yau_rel` (relative Calabi–Yau theorem) uses Dinew's mixed
inequality for non-pluripolar products against a common measure, in the form of Xia,
*Foundations of pluripotential theory*, `cor:nonpluripolar-common-measure-convex`
(a consequence of `prop:nonpluripolar-multifactor-common-measure`): if
`⟨T^n⟩ ≥ f ν` and `⟨S^n⟩ ≥ g ν` for closed positive `(1,1)`-currents `T, S`, a positive Radon
measure `ν` and nonnegative Borel functions `f, g`, then for `0 ≤ t ≤ 1`
`⟨((1-t)T + tS)^n⟩ ≥ ((1-t) f^{1/n} + t g^{1/n})^n ν`.

`CommonMeasureConvexLowerBound` is the special case `T = θ_u`, `S = θ_v` of two potentials of
the same class `θ` (so `(1-t)T + tS = θ_{(1-t)u + tv}`), for a finite measure `ν`, in positive
dimension `k` (for `k = 0` the exponent `1/k` is meaningless and the statement is void). It is a
**statement**, not an assumption of the project: the uniqueness theorem uses it as an explicit
hypothesis. (Lane S57, `SGPT/NPP/LogConcavityDinew*`, is building the local analytic input of
Dinew's inequality; it does not yet supply this statement.)

With `ThetaPshConvexCombination.convexComb t u v = t u + (1 - t) v`, the weight of `u` (density
`f`) is `t` and the weight of `v` (density `g`) is `1 - t`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeCY

open MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass

universe u

/-- **Dinew's lower bound for convex combinations against a common measure** (Xia, *Foundations
of pluripotential theory*, `cor:nonpluripolar-common-measure-convex`, for two potentials of one
class): for `θ`-psh `u, v`, a finite measure `ν` and measurable `f, g ≥ 0` with
`θ_u^n ≥ f ν` and `θ_v^n ≥ g ν`, and `0 ≤ t ≤ 1`,
`θ_{t u + (1-t) v}^n ≥ (t f^{1/k} + (1-t) g^{1/k})^k ν` (`k = dim X > 0`). -/
def CommonMeasureConvexLowerBound (k : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] [MeasurableSpace M]
    [CompactSpace M] : Prop :=
  0 < k → ∀ (θ : ClosedRealOneOneForm k M) (u v : M → EReal) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (ν : Measure M) [IsFiniteMeasure ν] (f g : M → ℝ≥0∞),
    Measurable f → Measurable g →
    ν.withDensity f ≤ diagonalPotentialMeasure θ u hu →
    ν.withDensity g ≤ diagonalPotentialMeasure θ v hv →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∀ hw : IsThetaPshPotential θ.val (ThetaPshConvexCombination.convexComb t u v),
      ν.withDensity (fun x => (ENNReal.ofReal t * f x ^ ((k : ℝ)⁻¹) +
          ENNReal.ofReal (1 - t) * g x ^ ((k : ℝ)⁻¹)) ^ k) ≤
        diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb t u v) hw

/-- In dimension `0` the statement is void. -/
theorem commonMeasureConvexLowerBound_zero (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [MeasurableSpace M]
    [CompactSpace M] : CommonMeasureConvexLowerBound 0 M :=
  fun h => absurd h (lt_irrefl 0)

end SGPT.Envelopes.RelativeCY
