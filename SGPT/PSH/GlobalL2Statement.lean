import SGPT.Foundations.Analysis.Pending.HormanderInterface
import SGPT.Foundations.Analysis.FirstPass.MultiplierIdeals
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.PSH.BookLineBundleMetrics
import SGPT.Foundations.Analysis.LogPole

/-!
# Global `L²` sections on compact complex manifolds: the statements

Blueprint `claude-global-l2.tex`.  This file only *states* the intermediate results of the
route to global holomorphic sections with multiplier-ideal control (source `lma:existsecposmass`,
the lower bound of `prop:Bergman_approx`, and the existence part of `thm:OT_ext_global`), so that
independent pieces can be proved in parallel.  None of the definitions below is assumed anywhere
as a hypothesis of a result presented as proved.

The route avoids any global Hilbert-space `∂̄` theory: the book only needs `k ≫ 0`, and for large
curvature the global `∂̄`-equation is solved by a Neumann series of *local* Hörmander corrections on
coordinate balls, glued with a partition of unity (the gluing error is `O(1/k)` times the previous
one).

## Statements

* `LocalBallCorrectionSmoothStatement n` (`claude-global-l2:local-smooth`): Hörmander's estimate on
  a ball of `ℂⁿ` for a smooth weight `Φ` with `Levi Φ ≥ c`, applied to `∂̄`-exact data: for every
  smooth `a` there is `G` holomorphic on the smaller ball with
  `∫_{B_r} |a - G|² e^{-Φ} ≤ (2/c) ∫_{B_R} |∂̄a|² e^{-Φ}`.
* `LocalBallCorrectionStatement n` (`claude-global-l2:local-singular`): the same for the singular
  weight `Φ = Ψ + c|z - z₀|²`, `Ψ` an arbitrary (extended-real) plurisubharmonic function.
* `IsOwnFirstChernForm L θ`: `θ = c₁(L, h_L)` for the (smooth) fibre metric of the bundle.
* `GlobalCutoffCorrectionStatement n X` (`claude-global-l2:global-correction`): on a compact
  complex manifold with a Kähler background `ω`, for `k ≥ k₀(L, T, δ)` and every
  `φ ∈ PSH(X, θ - δω)` (`θ = c₁(L, h_L)`), a cut-off `χ F` of a local holomorphic section of
  `L^k ⊗ T` is corrected to a global holomorphic section `s` with `χ F - s ∈ L²(e^{-kφ})`.
* `GlobalPointExtensionStatement n X` (`claude-global-l2:point-extension`): the uniform
  `L²` extension from a point (Xia, *Foundations of pluripotential theory*,
  `thm:compact-point-extension`), in the form used by the book: for `k ≥ k₀(L, T, δ)`, every
  `φ ∈ PSH(X, θ - δω)`, every `x` with `φ(x) > -∞` and every `v ∈ (L^k ⊗ T)_x` there is
  `s ∈ H⁰(X, L^k ⊗ T)` with `s(x) = v` and `∫ |s|² e^{-kφ} dμ ≤ C |v|² e^{-kφ(x)}`, `C`
  independent of `k, φ, x, v`.
* `PointPoleStatement n X` (`claude-global-l2:point-pole`): a quasi-psh function with a logarithmic
  pole at a point.

Status: `LocalBallCorrectionSmoothStatement`, `LocalBallCorrectionStatement` and
`GlobalCutoffCorrectionStatement` are proved (`localBallCorrectionSmooth`, `localBallCorrection`,
`globalCutoffCorrection` in `SGPT/PSH/GlobalL2Local*.lean`, `SGPT/PSH/GlobalL2Correction.lean`);
`GlobalPointExtensionStatement` and `PointPoleStatement` are open.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1 SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

/-! ### Local statements on balls of `ℂⁿ` -/

/-- The pointwise squared norm `|∂̄a|² = ∑_j |∂a/∂z̄_j|²` of the `(0,1)`-form `∂̄a` of a function
on `ℂⁿ`, in the standard coordinates. -/
def dbarNormSq {n : ℕ} (a : ComplexModel n → ℂ) (z : ComplexModel n) : ℝ :=
  ∑ j, ‖dbarDir (coordVec j) a z‖ ^ 2

/-- **Local `L²` correction on a ball, smooth weights** (`claude-global-l2:local-smooth`).
Hörmander's `L²` estimate on the ball `B(z₀, R)` for a smooth weight `Φ` whose Levi form is at
least `c|ξ|²`, applied to the `∂̄`-exact datum `∂̄a`: there is a function `G` holomorphic on the
smaller ball `B(z₀, r)` with
`∫_{B(z₀,r)} |a - G|² e^{-Φ} ≤ (2/c) ∫_{B(z₀,R)} |∂̄a|² e^{-Φ}`.
(Hörmander's constant is `1/c`; `2/c` is what the gluing uses.) -/
def LocalBallCorrectionSmoothStatement (n : ℕ) : Prop :=
  ∀ (z₀ : ComplexModel n) (r R : ℝ), 0 < r → r < R → ∀ c : ℝ, 0 < c →
  ∀ Φ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ Φ (ball z₀ R) →
    (∀ z ∈ ball z₀ R, ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm Φ z ξ) →
  ∀ a : ComplexModel n → ℂ, ContDiffOn ℝ ∞ a (ball z₀ R) →
  ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
    ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ z)) ≤
      ENNReal.ofReal (2 / c) *
        ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ z))

/-- The singular weight `Ψ + c|z - z₀|²` of `LocalBallCorrectionStatement`, as the density
`e^{-Ψ(z) - c|z - z₀|²} ∈ [0, ∞]` (equal to `∞` at the poles of `Ψ`). -/
def ballWeight {n : ℕ} (Ψ : ComplexModel n → EReal) (c : ℝ) (z₀ z : ComplexModel n) : ℝ≥0∞ :=
  multiplierWeight 1 (Ψ z + ((c * ‖z - z₀‖ ^ 2 : ℝ) : EReal))

/-- **Local `L²` correction on a ball, singular weights** (`claude-global-l2:local-singular`).
For every plurisubharmonic `Ψ : ℂⁿ → [-∞, ∞)` on `B(z₀, R)` (poles allowed), every `c > 0` and every
smooth `a` on `B(z₀, R)` there is `G` holomorphic on `B(z₀, r)` with
`∫_{B(z₀,r)} |a - G|² e^{-Ψ - c|z-z₀|²} ≤ (2/c) ∫_{B(z₀,R)} |∂̄a|² e^{-Ψ - c|z-z₀|²}`. -/
def LocalBallCorrectionStatement (n : ℕ) : Prop :=
  ∀ (z₀ : ComplexModel n) (r R : ℝ), 0 < r → r < R → ∀ c : ℝ, 0 < c →
  ∀ Ψ : ComplexModel n → EReal, PlurisubharmonicOn Ψ (ball z₀ R) →
  ∀ a : ComplexModel n → ℂ, ContDiffOn ℝ ∞ a (ball z₀ R) →
  ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
    ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ballWeight Ψ c z₀ z ≤
      ENNReal.ofReal (2 / c) *
        ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z

/-! ### Global statements on a compact complex manifold -/

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `θ = c₁(L, h_L)` for the fibre metric `h_L` of the bundle itself (source `def:Hermmetric`, read
in the atlas frames): on every chart, `θ = ddᶜ(-log |e|²_{h_L})` over the base set of every atlas
frame `e`. -/
def IsOwnFirstChernForm (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (θ : ClosedRealOneOneForm n X) : Prop :=
  ∀ (c : ComplexChart n X) (e : AtlasFrame L) (z : ComplexModel n), z ∈ c.val.target →
    c.val.symm z ∈ e.val.baseSet →
    θ.val.coeff c z = smoothDDC (fun w => -Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2)) z

variable (n X) [MeasurableSpace X] [BorelSpace X]

/-- **Global `L²` correction of a cut-off holomorphic section** (`claude-global-l2:global-correction`).
`X` compact with a Kähler background `ω` and a smooth positive volume `μ`; `L, T` holomorphic line
bundles with smooth metrics, `θ = c₁(L, h_L)`, `δ > 0`.  There is `k₀` such that for every
`k ≥ k₀` and every `φ ∈ PSH(X, θ - δω)`: if `F` is a holomorphic section of `L^k ⊗ T` on an open
`U`, `χ` a smooth function with `tsupport χ ⊆ U`, locally constant on `U` off a compact `K ⊆ U`,
and `∫_K |F|² e^{-kφ} dμ < ∞`, then there is a global holomorphic section `s` of `L^k ⊗ T` with
`∫_X |χ F - s|² e^{-kφ} dμ < ∞`. -/
def GlobalCutoffCorrectionStatement : Prop :=
  CompactSpace X →
  ∀ (ωb : KahlerBackground n X) (μ : Measure X), IsSmoothPositiveVolume (n := n) μ →
  ∀ (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∀ δ : ℝ, 0 < δ →
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
  ∀ φ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val φ →
  ∀ U : Set X, IsOpen U →
  ∀ F : (x : X) → (twistedPower L T k).Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber F U →
  ∀ χ : X → ℝ, ChartSmooth (n := n) χ → tsupport χ ⊆ U →
  ∀ K : Set X, IsCompact K → K ⊆ U → (∀ x ∈ U \ K, ∀ᶠ y in 𝓝 x, χ y = χ x) →
    ∫⁻ x in K, ENNReal.ofReal (‖F x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) ∂μ < ⊤ →
  ∃ s : twistedSections L T k,
    ∫⁻ x, ENNReal.ofReal (‖((χ x : ℝ) : ℂ) • F x - s x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) ∂μ
      < ⊤

/-- **Uniform `L²` extension from a point** (`claude-global-l2:point-extension`; Xia,
*Foundations of pluripotential theory*, `thm:compact-point-extension`, in the form of the book's
`thm:OT_ext` for `Y = {x}`).  `X` compact with a Kähler background `ω` and a smooth positive
volume `μ`; `L, T` holomorphic line bundles with smooth metrics, `θ = c₁(L, h_L)`, `δ > 0`.  There
are `k₀` and `C > 0` such that for every `k ≥ k₀`, every `φ ∈ PSH(X, θ - δω)`, every `x ∈ X` with
`φ(x) > -∞` and every `v ∈ (L^k ⊗ T)_x` there is `s ∈ H⁰(X, L^k ⊗ T)` with `s(x) = v` and
`∫_X |s|² e^{-kφ} dμ ≤ C |v|² e^{-kφ(x)}`. -/
def GlobalPointExtensionStatement : Prop :=
  CompactSpace X →
  ∀ (ωb : KahlerBackground n X) (μ : Measure X), IsSmoothPositiveVolume (n := n) μ →
  ∀ (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∀ δ : ℝ, 0 < δ →
  ∃ (k₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℕ, k₀ ≤ k →
  ∀ φ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val φ →
  ∀ x : X, φ x ≠ ⊥ → ∀ v : (twistedPower L T k).Fiber x,
  ∃ s : twistedSections L T k, s x = v ∧
    ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
      ENNReal.ofReal C * (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x))

/-- **A quasi-plurisubharmonic function with a logarithmic pole at a point**
(`claude-global-l2:point-pole`; input of `claude-global-l2:point-extension` and
`claude-global-l2:existsecposmass`).  On a compact complex manifold with a Kähler background `ω`,
for every `x₀` there are `B > 0` and `P ∈ PSH(X, Bω)` with `P ≤ 0`, `P` finite and continuous off
`x₀`, and `P = log |z - z(x₀)|²` near `x₀` in the preferred chart at `x₀`.  (Standard: a cut-off
of `log |z - z(x₀)|²`; the Levi form of the cut-off is bounded below on the annulus where the
cut-off is not constant.) -/
def PointPoleStatement : Prop :=
  CompactSpace X →
  ∀ (ωb : KahlerBackground n X) (x₀ : X), ∃ B : ℝ, 0 < B ∧ ∃ P : X → EReal,
    IsThetaPshPotential (B • ωb.form).val P ∧ (∀ x, P x ≤ 0) ∧ (∀ x, x ≠ x₀ → P x ≠ ⊥) ∧
    ContinuousOn P {x₀}ᶜ ∧ ∃ r : ℝ, 0 < r ∧ ∀ x ∈ (complexChartAt (n := n) x₀).val.source,
      (complexChartAt (n := n) x₀).val x ∈ ball ((complexChartAt (n := n) x₀).val x₀) r →
        P x = logNormSq ((complexChartAt (n := n) x₀).val x - (complexChartAt (n := n) x₀).val x₀)

end SGPT.PSH.GlobalL2
