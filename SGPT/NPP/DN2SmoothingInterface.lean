import SGPT.Envelopes.LapClassDef

/-!
# Interface: the joint smoothing of FPT `lem:chern-joint-smoothing`

Lanes DN2/DN3, `thm:DNT23_C11bar` (`chapter_npp.tex`), big classes that are not nef.  The proof of
FPT `thm:big-metric-laplacian-rooftop` (`chapters/inputs/q10-big-envelope-regularity.tex`,
lines 414–588; lane DN2) uses the smoothing `Ψ_u(x, w)` of FPT `lem:chern-joint-smoothing`
(lines 12–368; lane DN3) only through the properties collected here.  This file contains
**definitions only**; `JointSmoothingStatement` is proved by lane DN3 and consumed by lane DN2.

## The properties (FPT notation, `r = |w|`)

For a compact complex manifold `Y` with a Kähler form `ω` there are `r₀ > 0` and an operator
`Ψ : (Y → ℝ) → Y → ℝ → ℝ`, `Ψ g x t` = average of `g` over the image of the `ω`-geodesic-jet ball
of radius `t` about `x` (a positive kernel of mass one), such that:

* `contDiffOn`: for integrable `g`, `(z, t) ↦ Ψ g (e⁻¹ z) t` is smooth on `target × (0, r₀)` in
  every chart `e` (FPT: `Ψ_u` smooth for `w ≠ 0`, rotation invariant);
* `mono`, `neg`, `add_const`: positivity, linearity and mass one of the kernel;
* `generator`: `(Ψ_g(·, t) - g)/t² → a Δ_ω g` in the sense of distributions (paired with the
  Kähler volume `ω^N`), `a > 0` (FPT `eq:chern-smoothing-generator`; `Δ_ω` is symmetric for `ω^N`);
* `psh`: for every closed real `(1,1)`-form `θ` and every `θ`-psh potential `u` there are
  `K, A, C ≥ 0`, `C₁ > 0` such that `H_u(x, t) = Ψ_u(x, t) + K t²` satisfies
  - `H_u ≥ u`;
  - `s ↦ H_u(x, eˢ)` is nondecreasing and strictly convex;
  - the initial joint estimate (FPT `eq:chern-initial-joint-bound`):
    `(θ + ddᶜ_{x,w} H_u)[v, η]² ≥ -(A λ_u + C r)|v|² - C|v||η| - C|η|²`,
    `λ_u = t ∂_t H_u`;
  - the improved joint estimate (FPT `eq:chern-improved-joint-bound` together with the
    trace-mass bound `m_u(x,r) ≤ M(x)/r` that FPT derives from a linear smoothing bound by the
    Jensen–Lelong formula): if `u(x) = a` is finite, `L ≥ 0`, and `H_u(x, t) ≤ a + L t` for
    `0 < t ≤ C₁ r`, then at `(x, w)`, `|w| = r`,
    `(θ + ddᶜ_{x,w} H_u)[v, η]² ≥ -(A λ_u + C(1+L) r²)|v|² - C(1+L) r|v||η| - C(1+L) r|η|²`.

The joint Levi form is read in a chart `e` of `Y` through `(z, w) ↦ H_u(e⁻¹ z, |w|) + ρ(z)`, `ρ` a
smooth local potential of `θ` (`IsSmoothLocalPotential`, so `leviForm ρ z v = π θ(v, Jv)`), and
`|v|² = ω(v, Jv)` in the chart (`chartNormSq`).  All constants are independent of the chart and of
the point; normalisations (`2π`, `π`, `4`) are absorbed in the constants.  The obstacle error
`|Ψ_f - f| ≤ C_f t²` of FPT `eq:chern-regular-obstacle-error` is not listed: its one-sided form
`Ψ_f ≤ f + K t²`, which is all the proof uses, follows from `psh` applied to `-f` and the
background `M ω` (`f` with bounded complex Hessian makes `-f` an `(Mω)`-psh potential).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart IntegrationCurrent

universe u

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The corrected smoothing `H_u(x, t) = Ψ_u(x, t) + K t²` of an extended-real potential `u`
(applied to `toReal ∘ u`; the poles form a null set). -/
def correctedSmoothing (Ψ : (Y → ℝ) → Y → ℝ → ℝ) (u : Y → EReal) (K : ℝ) (x : Y) (t : ℝ) : ℝ :=
  Ψ (fun y => (u y).toReal) x t + K * t ^ 2

/-- The logarithmic slope `λ(x, t) = t ∂_t H(x, t)`. -/
def logSlope (H : Y → ℝ → ℝ) (x : Y) (t : ℝ) : ℝ :=
  t * deriv (H x) t

/-- The squared `ω`-length `ω(v, Jv)` of a tangent vector read in a chart. -/
def chartNormSq (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z v : ComplexModel N) : ℝ :=
  wY.form.val.coeff e z ![v, Complex.I • v]

/-- The joint function `(z, w) ↦ H(e⁻¹ z, |w|) + ρ(z)` on a chart. -/
def chartJoint (H : Y → ℝ → ℝ) (e : ComplexChart N Y) (ρ : ComplexModel N → ℝ) :
    ComplexModel N × ℂ → ℝ :=
  fun p => H (e.val.symm p.1) ‖p.2‖ + ρ p.1

/-- The joint Levi bound `(θ + ddᶜ_{x,w} H)[v, η]² ≥ -a₁|v|² - a₂|v||η| - a₃|η|²` at the chart
point `(z, w)`, for every smooth local potential `ρ` of `θ` near `z`. -/
def JointLeviLowerBound (θ : ClosedRealOneOneForm N Y) (wY : KahlerBackground N Y)
    (H : Y → ℝ → ℝ) (e : ComplexChart N Y) (z : ComplexModel N) (w : ℂ) (a₁ a₂ a₃ : ℝ) : Prop :=
  ∀ (W : Set (ComplexModel N)) (ρ : ComplexModel N → ℝ), z ∈ W →
    IsSmoothLocalPotential θ.val e W ρ → ∀ (v : ComplexModel N) (η : ℂ),
      -(a₁ * chartNormSq wY e z v) - a₂ * Real.sqrt (chartNormSq wY e z v) * ‖η‖ - a₃ * ‖η‖ ^ 2 ≤
        leviForm (chartJoint H e ρ) (z, w) (v, η)

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The properties of the joint smoothing** (FPT `lem:chern-joint-smoothing`, in the form used
by the proof of FPT `thm:big-metric-laplacian-rooftop`); see the module docstring. -/
structure IsJointSmoothing (wY : KahlerBackground N Y) (r₀ : ℝ) (Ψ : (Y → ℝ) → Y → ℝ → ℝ) :
    Prop where
  r₀_pos : 0 < r₀
  contDiffOn : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ e : ComplexChart N Y,
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => Ψ g (e.val.symm p.1) p.2)
      (e.val.target ×ˢ Ioo 0 r₀)
  mono : ∀ g g' : Y → ℝ, Integrable g (kahlerVolume wY) → Integrable g' (kahlerVolume wY) →
    g ≤ᵐ[kahlerVolume wY] g' → ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → Ψ g x t ≤ Ψ g' x t
  neg : ∀ (g : Y → ℝ) (x : Y) (t : ℝ), Ψ (fun y => -g y) x t = -Ψ g x t
  add_const : ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) → ∀ (c : ℝ) (x : Y) (t : ℝ), 0 < t →
    t < r₀ → Ψ (fun y => g y + c) x t = Ψ g x t + c
  generator : ∃ a : ℝ, 0 < a ∧ ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) →
    ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
      Tendsto (fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * χ y ∂(kahlerVolume wY)) (𝓝[>] 0)
        (𝓝 (a * ∫ y, g y * laplacian wY.form.val χ y ∂(kahlerVolume wY)))
  psh : ∀ (θ : ClosedRealOneOneForm N Y) (u : Y → EReal), IsThetaPshPotential θ.val u →
    ∃ K A C C₁ : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 < C₁ ∧
      (∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal)) ∧
      (∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s) ∧
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₀ →
          JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
            (A * logSlope (correctedSmoothing Ψ u K) (e.val.symm z) ‖w‖ + C * ‖w‖) C C) ∧
      (∀ (x : Y) (a : ℝ), u x = (a : EReal) → ∀ L : ℝ, 0 ≤ L → ∀ r : ℝ, 0 < r → C₁ * r < r₀ →
        (∀ t : ℝ, 0 < t → t ≤ C₁ * r → correctedSmoothing Ψ u K x t ≤ a + L * t) →
        ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → e.val.symm z = x →
          ∀ w : ℂ, ‖w‖ = r →
            JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
              (A * logSlope (correctedSmoothing Ψ u K) x r + C * (1 + L) * r ^ 2)
              (C * (1 + L) * r) (C * (1 + L) * r))

end SGPT.NPP.DN2

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

universe v

/-- **FPT `lem:chern-joint-smoothing`, as used in `thm:big-metric-laplacian-rooftop`**: every
compact complex manifold with a Kähler form carries a joint smoothing (`IsJointSmoothing`).
Statement only; lane DN3 proves it. -/
def JointSmoothingStatement : Prop :=
  ∀ (N : ℕ) (Y : Type v) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (wY : KahlerBackground N Y), ∃ (r₀ : ℝ) (Ψ : (Y → ℝ) → Y → ℝ → ℝ), IsJointSmoothing wY r₀ Ψ

end SGPT.NPP.DN2
