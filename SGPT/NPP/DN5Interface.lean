import SGPT.NPP.DN5Defs

/-!
# Interfaces of lane DN5 with lanes DN4 (local joint estimate) and DN6 (generator)

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 12–368).  **Statements only.**  The
assembly `SGPT.NPP.DN5Assembly` derives `SGPT.NPP.DN2.JointSmoothingStatement` from them.

* `LocalJointEstimate`: FPT Steps 2–6 in one chart, for an abstract local fibre map
  `Φ` (`IsLocalFibreMap`), a smooth Kähler coefficient `α` and a potential `u` with
  `u + q` plurisubharmonic, `q` a smooth potential of the coefficient `β` of `θ`: on a compact `K`
  and for radii below some `r₁ > 0` (depending on all data), the corrected chart smoothing
  `H(z, t) = localSmoothing Φ α u z t + K₀ t²` satisfies the four `psh` clauses of
  `SGPT.NPP.DN2.IsJointSmoothing` (FPT: `H_u ≥ u`; `s ↦ H(x, eˢ)` nondecreasing and strictly
  convex; `eq:chern-initial-joint-bound`; `eq:chern-improved-joint-bound` under the linear bound).
  The joint Levi form is that of `(z, w) ↦ H(z, |w|) + q(z)`, `|v|² = α_z(v, iv)`.
* `GeneratorEstimate`: FPT `eq:chern-smoothing-generator` for the smoothing
  `SGPT.NPP.DN5.smoothing`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart IntegrationCurrent

/-- The corrected chart smoothing `H(z, t) = localSmoothing Φ α (toReal ∘ u) z t + K₀ t²`. -/
def localCorrected {N : ℕ} (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (u : ComplexModel N → EReal)
    (K₀ : ℝ) (z : ComplexModel N) (t : ℝ) : ℝ :=
  localSmoothing Φ α (fun y => (u y).toReal) z t + K₀ * t ^ 2

/-- **The chart-level joint estimate** (FPT `lem:chern-joint-smoothing`, Steps 2–6, in one
chart; to be proved by lane DN4).  Data: a local fibre map `Φ` on `O ⊇ K' × closedBall 0 R`
(`K'` a neighbourhood of the compact `K`), a smooth closed strictly positive `(1,1)` coefficient
`α` on the open `W ⊇ K`, a smooth `q` on `W`, and `u : ℂⁿ → [-∞, ∞)` with `u + q`
plurisubharmonic on `W` and `u` locally nondegenerate on `W` (every neighbourhood of a point of
`W` contains a point where `u ≠ -∞`; without this the statement is false: `u ≡ -∞`, `q = -‖z‖²`.
Correction by lane DN9; the global potentials `IsThetaPshPotential` are `LocallyNondegenerate`).  Conclusion: there are `r₁ > 0` and constants such that, for every
`z ∈ K`, the four clauses of `SGPT.NPP.DN2.IsJointSmoothing.psh` hold for
`H = localCorrected Φ α u K₀` at radii `< r₁`, the joint Levi form being that of
`(z, w) ↦ H(z, |w|) + q(z)` and `|v|² = α_z(v, iv)`. -/
def LocalJointEstimate (N : ℕ) : Prop :=
  ∀ (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N))
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ)
    (W K K' : Set (ComplexModel N)) (R : ℝ) (q : ComplexModel N → ℝ)
    (u : ComplexModel N → EReal),
    IsLocalFibreMap Φ O → IsOpen W → IsCompact K → K ⊆ interior K' → K' ⊆ W → 0 < R →
    K' ×ˢ Metric.closedBall (0 : ComplexModel N) R ⊆ O →
    ContDiffOn ℝ ∞ α W → (∀ z ∈ W, extDeriv α z = 0) →
    (∀ z ∈ W, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) →
    ContDiffOn ℝ ∞ q W → PlurisubharmonicOn (fun y => u y + (q y : EReal)) W →
    (∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥) →
    ∃ r₁ K₀ A C C₁ : ℝ, 0 < r₁ ∧ 0 ≤ K₀ ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 < C₁ ∧
      ∀ z ∈ K,
        (∀ t : ℝ, 0 < t → t < r₁ → u z ≤ ((localCorrected Φ α u K₀ z t : ℝ) : EReal)) ∧
        (∀ s : ℝ, s < Real.log r₁ →
          0 ≤ deriv (fun s => localCorrected Φ α u K₀ z (Real.exp s)) s ∧
          0 < deriv (deriv (fun s => localCorrected Φ α u K₀ z (Real.exp s))) s) ∧
        (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₁ → ∀ (v : ComplexModel N) (η : ℂ),
          -((A * (‖w‖ * deriv (localCorrected Φ α u K₀ z) ‖w‖) + C * ‖w‖) *
              α z ![v, Complex.I • v]) -
            C * Real.sqrt (α z ![v, Complex.I • v]) * ‖η‖ - C * ‖η‖ ^ 2 ≤
          leviForm (fun p : ComplexModel N × ℂ => localCorrected Φ α u K₀ p.1 ‖p.2‖ + q p.1)
            (z, w) (v, η)) ∧
        (∀ (a L r : ℝ), u z = (a : EReal) → 0 ≤ L → 0 < r → C₁ * r < r₁ →
          (∀ t : ℝ, 0 < t → t ≤ C₁ * r → localCorrected Φ α u K₀ z t ≤ a + L * t) →
          ∀ w : ℂ, ‖w‖ = r → ∀ (v : ComplexModel N) (η : ℂ),
            -((A * (r * deriv (localCorrected Φ α u K₀ z) r) + C * (1 + L) * r ^ 2) *
                α z ![v, Complex.I • v]) -
              C * (1 + L) * r * Real.sqrt (α z ![v, Complex.I • v]) * ‖η‖ -
              C * (1 + L) * r * ‖η‖ ^ 2 ≤
            leviForm (fun p : ComplexModel N × ℂ => localCorrected Φ α u K₀ p.1 ‖p.2‖ + q p.1)
              (z, w) (v, η))

universe v

/-- **The generator of the smoothing** (FPT `eq:chern-smoothing-generator`; to be proved by lane
DN6): `(Ψ_g(·, t) - g)/t² → a Δ_ω g` in the sense of distributions, paired with the Kähler
volume, for the smoothing `SGPT.NPP.DN5.smoothing` of any gluing data. -/
def GeneratorEstimate : Prop :=
  ∀ (N : ℕ) (Y : Type v) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (wY : KahlerBackground N Y) (A : FibreAtlas N Y),
    ∃ a : ℝ, 0 < a ∧ ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) →
      ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
        Tendsto (fun t => ∫ y, (smoothing wY A g y t - g y) / t ^ 2 * χ y ∂(kahlerVolume wY))
          (𝓝[>] 0) (𝓝 (a * ∫ y, g y * laplacian wY.form.val χ y ∂(kahlerVolume wY)))

end SGPT.NPP.DN5
