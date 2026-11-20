import SGPT.NPP.DN5Interface

/-!
# Interfaces of lane DN9 (local joint estimate) with lanes DN10, DN11

Lane DN9, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Steps 2–6).  **Statements only.**

* `SmoothJointEstimate` — FPT `eq:chern-potential-joint-bound` for smooth plurisubharmonic
  potentials, uniformly over the centres of a compact set.
* `QPartEstimate`, `ClauseEstimate` — the smooth potential `q` and the clauses `H ≥ u`,
  convexity, slope bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN9

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart IntegrationCurrent
open SGPT.NPP.DN5

/-- The hypotheses on the chart data common to the interfaces: `Φ` a local fibre map on `O`,
`α` a smooth strictly positive `(1,1)` coefficient on the open `U`, `K ⊆ U` compact with
`K × {0} ⊆ O`. -/
def ChartData {N : ℕ} (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N))
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ)
    (U K : Set (ComplexModel N)) : Prop :=
  IsLocalFibreMap Φ O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ α U ∧
    (∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) ∧ IsCompact K ∧ K ⊆ U ∧
    ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O

/-- **The joint Levi estimate for smooth plurisubharmonic potentials** (FPT
`eq:chern-potential-joint-bound`, uniformly over the centres of `K`; lane DN9): with
`S = localSmoothing Φ α p`,
`L[(z, w) ↦ S(z, |w|)](v, η) ≥ -A₁ |w|² |v|² λ(2|w|) - A₂ (|v|² + |v||η|) λ(|w|)`,
`λ(t) = t ∂_t S(z, t)`, for every `C²` function `p` plurisubharmonic on `B(z, c|w|)`. -/
def SmoothJointEstimate (N : ℕ) : Prop :=
  ∀ (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N))
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (U K : Set (ComplexModel N)),
    ChartData Φ O α U K →
    ∃ r₁ c A₁ A₂ : ℝ, 0 < r₁ ∧ 0 < c ∧ 0 ≤ A₁ ∧ 0 ≤ A₂ ∧
      ∀ z ∈ K, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₁ → ∀ p : ComplexModel N → ℝ, ContDiff ℝ 2 p →
        (∀ y ∈ ball z (c * ‖w‖), ∀ v, 0 ≤ leviForm p y v) → ∀ (v : ComplexModel N) (η : ℂ),
          -(A₁ * ‖w‖ ^ 2 * ‖v‖ ^ 2 *
              (2 * ‖w‖ * deriv (localSmoothing Φ α p z) (2 * ‖w‖))) -
            A₂ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖) * (‖w‖ * deriv (localSmoothing Φ α p z) ‖w‖) ≤
          leviForm (fun x : ComplexModel N × ℂ => localSmoothing Φ α p x.1 ‖x.2‖) (z, w) (v, η)

/-- **The smooth potential**: `S_q - q` is `O(t²)` with its slope, and the Levi form
of `(z, w) ↦ S_q(z, |w|) - q(z)` is bounded above by `C(|w|²|v|² + |w||v||η| + |η|²)`. -/
def QPartEstimate (N : ℕ) : Prop :=
  ∀ (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N))
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (U K : Set (ComplexModel N))
    (q : ComplexModel N → ℝ),
    ChartData Φ O α U K → ContDiffOn ℝ ∞ q U →
    ∃ (V : Set (ComplexModel N)) (r C : ℝ), IsOpen V ∧ K ⊆ V ∧ 0 < r ∧ 0 ≤ C ∧
      ContDiffOn ℝ 2 (fun x : ComplexModel N × ℝ => localSmoothing Φ α q x.1 x.2)
        (V ×ˢ Ioo 0 r) ∧
      ∀ z ∈ K,
        (∀ t : ℝ, 0 < t → t < r → |t * deriv (localSmoothing Φ α q z) t| ≤ C * t ^ 2) ∧
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r → ∀ (v : ComplexModel N) (η : ℂ),
          leviForm (fun x : ComplexModel N × ℂ => localSmoothing Φ α q x.1 ‖x.2‖ - q x.1)
              (z, w) (v, η) ≤
            C * (‖w‖ ^ 2 * ‖v‖ ^ 2 + ‖w‖ * ‖v‖ * ‖η‖ + ‖η‖ ^ 2)

/-- **The clauses `H ≥ u`, convexity, and the slope bounds**, for
`H = localCorrected Φ α u K₀` and every `K₀ ≥ K₀'`. -/
def ClauseEstimate (N : ℕ) : Prop :=
  ∀ (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N))
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (U K : Set (ComplexModel N))
    (q : ComplexModel N → ℝ) (u : ComplexModel N → EReal),
    ChartData Φ O α U K → ContDiffOn ℝ ∞ q U →
    PlurisubharmonicOn (fun y => u y + (q y : EReal)) U →
    (∀ x ∈ U, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥) →
    ∃ r₁ K₀' : ℝ, 0 < r₁ ∧ 0 ≤ K₀' ∧ ∀ K₀ : ℝ, K₀' ≤ K₀ →
      ∃ Cu C' C₁ : ℝ, 0 ≤ Cu ∧ 0 ≤ C' ∧ 2 ≤ C₁ ∧ ∀ z ∈ K,
        (∀ t : ℝ, 0 < t → t < r₁ → u z ≤ ((localCorrected Φ α u K₀ z t : ℝ) : EReal)) ∧
        (∀ s : ℝ, s < Real.log r₁ →
          0 ≤ deriv (fun s => localCorrected Φ α u K₀ z (Real.exp s)) s ∧
          0 < deriv (deriv (fun s => localCorrected Φ α u K₀ z (Real.exp s))) s) ∧
        (∀ t : ℝ, 0 < t → t < r₁ → t * deriv (localCorrected Φ α u K₀ z) t ≤ Cu) ∧
        (∀ a L r : ℝ, u z = (a : EReal) → 0 ≤ L → 0 < r → C₁ * r < r₁ →
          (∀ t : ℝ, 0 < t → t ≤ C₁ * r → localCorrected Φ α u K₀ z t ≤ a + L * t) →
          ∀ t : ℝ, 0 < t → t ≤ 2 * r →
            t * deriv (localCorrected Φ α u K₀ z) t ≤ C' * (1 + L) * r)

end SGPT.NPP.DN9
