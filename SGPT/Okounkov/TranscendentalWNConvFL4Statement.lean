import SGPT.Okounkov.TranscendentalWNConvFLStatement

/-!
# WN21 Lemma 7.5 and Corollary 7.6 along fibre discs (lane WN-FL4, statements)

Blueprint `claude-tok-wn-fl4`, nodes `tok-wn-fl4:disc-laplacian`, `tok-wn-fl4:lipschitz`;
source D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted
volumes of big classes*, arXiv:2103.03660 (WN21), §7: Lemma 7.5, Corollary 7.6 and the paragraph
after it ("Let now `z̃₁, z₂, …, z_n, τ` be local coordinates centered at a point `z ∈ ℰ` …"),
`references/wn21-restricted-volume`.

These are the exceptional-side inputs of `ExceptionalFibreConvergenceStatement F` (WN21
Proposition 7.4 near `ℰ \ X'`).  WN21 states them in local coordinates `(z̃₁, z', τ)` of `𝒳` at a
point of `ℰ` in which `τ` is the fibre coordinate.  We state them for an arbitrary **holomorphic
family of fibre discs** `Γ : G → 𝒳` (`G ⊆ ℂ × ℂ^{m+1}` open) with `π_{ℙ¹}(μ(Γ(t, y))) = [t : 1]`,
through a point `Γ(0, y₀)` with `Ψ(Γ(0, y₀)) ≠ -∞`; local coordinates with `τ` as last coordinate
are such a family (`(t, y) ↦` the point with coordinates `(y, t)`), and so are the slice
coordinates of lane WN-LSC (`LSC.SliceCoords`) near `ℰ \ X'`.  The family form is chart-free and
contains WN21's statements near `ℰ \ X'` and near `X' \ ℰ` (no family exists through the nodes
`X' ∩ ℰ`, where `dτ = 0`).  The form `Θ` and the weight `Ψ` are arbitrary (with a log resolution
`π : 𝒵 → 𝒳` of `Ψ`, `Ψ ∘ π = ψ_{D'} + h`, `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler), as in WN21's
argument, which uses nothing else.

Following lane WN-FL3 (`tok/WN-FL3/NEEDS.md`: at `k = 0` the unit disc may meet a pole of `Ψ`), the
estimates are asserted only for `k ≥ k₀`; the consumer (Proposition 7.4) uses `k → ∞` only.

Notation: `g_k = cutoffObstacle μ χ k`, `v_k = P_Θ[Ψ](g_k) = prescribedEnvelope Θ g_k Ψ`.

* `ExcDiscLaplacianStatement F` (**WN21 Lemma 7.5**, along the discs `t ↦ Γ(t, y)`): there are
  `R > 0`, `C` and `k₀` such that for `k ≥ k₀`, `|y - y₀| < R` and `|t| ≤ e^{-k/2}`: `(t, y) ∈ G`,
  `v_k(Γ(t, y))` is finite with `|v_k(Γ(t, y)) + k| ≤ C`, and `t ↦ v_k(Γ(t, y))` is on the closed
  disc `|t| ≤ e^{-k/2}` the uniform limit of `C²` functions `u_j` with `-C ≤ Δ u_j ≤ C e^k` on the
  open disc.
* `ExcLipschitzStatement F` (**WN21 Corollary 7.6**, with the lower bound of Lemma 7.5): there are
  `R > 0`, `C`, `k₀` such that for `k ≥ k₀`, `|y - y₀| < R`: `v_k(Γ(0, y)) ≥ -k - C`, and for
  `|t| ≤ e^{-k/2}/2`, `v_k(Γ(t, y))` is finite and `|v_k(Γ(t, y)) - v_k(Γ(0, y))| ≤ C e^{k/2} |t|`.

This file contains definitions and **statements only**; nothing is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Laplacian
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl4:disc-laplacian`** (WN21 Lemma 7.5 along a holomorphic family of fibre discs):
for a normal-cone deformation `μ : 𝒳 → X × ℙ¹`, a closed real `(1,1)`-form `Θ`, a `Θ`-psh `Ψ` with
a log resolution `π : 𝒵 → 𝒳` (`Ψ ∘ π = ψ_{D'} + h`, `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler) and a
holomorphic family `Γ : G → 𝒳` of fibre discs (`π_{ℙ¹}(μ(Γ(t, y))) = [t : 1]`) with
`Ψ(Γ(0, y₀)) ≠ -∞`, there are `R > 0`, `C` and `k₀` such that for all `k ≥ k₀` and `|y - y₀| < R`,
`f(t) = v_k(Γ(t, y))` is finite with `|f + k| ≤ C` on `|t| ≤ e^{-k/2}` (where `(t, y) ∈ G`), and
there `f` is the uniform limit of `C²` functions `u_j` with `-C ≤ Δ u_j ≤ C e^k` on `|t| < e^{-k/2}`. -/
def ExcDiscLaplacianStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine),
    IsNormalConeDeformation F μ →
    ∀ (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (Ψ : 𝒳 → EReal), IsThetaPshPotential Θ.val Ψ →
    ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
      [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
      (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
      (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
      (hh : ChartSmooth (n := m + 1 + 1) h),
      CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
      (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
      ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) +
        ddcClosedForm h hh).val.IsKahler →
    ∀ χ : ℝ → ℝ, IsWNCutoff χ →
    ∀ (G : Set (ℂ × ComplexModel (m + 1))) (Γ : ℂ × ComplexModel (m + 1) → 𝒳), IsOpen G →
      ContMDiffOn 𝓘(ℂ, ℂ × ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ G →
      (∀ q ∈ G, (μ (Γ q)).2 = affineLinePoint q.1) →
    ∀ y₀ : ComplexModel (m + 1), ((0 : ℂ), y₀) ∈ G → Ψ (Γ (0, y₀)) ≠ ⊥ →
      ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ y ∈ Metric.ball y₀ R,
        (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) → (t, y) ∈ G ∧
          prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≠ ⊥ ∧
          |(prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y))).toReal + k| ≤ C) ∧
        ∃ u : ℕ → ℂ → ℝ, (∀ j, ContDiff ℝ 2 (u j)) ∧
          TendstoUniformlyOn u
            (fun t => (prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y))).toReal) atTop
            (Metric.closedBall 0 (Real.exp (-(k : ℝ) / 2))) ∧
          ∀ j, ∀ t ∈ Metric.ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
            -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k

/-- **`tok-wn-fl4:lipschitz`** (WN21 Corollary 7.6 along a holomorphic family of fibre discs,
with the lower bound of Lemma 7.5): in the situation of `ExcDiscLaplacianStatement`, there are
`R > 0`, `C` and `k₀` such that for all `k ≥ k₀` and `|y - y₀| < R`: `(0, y) ∈ G`,
`v_k(Γ(0, y)) ≥ -k - C`, and for `|t| ≤ e^{-k/2}/2`: `(t, y) ∈ G`, `v_k(Γ(t, y))` is finite and
`|v_k(Γ(t, y)) - v_k(Γ(0, y))| ≤ C e^{k/2} |t|`. -/
def ExcLipschitzStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine),
    IsNormalConeDeformation F μ →
    ∀ (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (Ψ : 𝒳 → EReal), IsThetaPshPotential Θ.val Ψ →
    ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
      [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
      (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
      (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
      (hh : ChartSmooth (n := m + 1 + 1) h),
      CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
      (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
      ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) +
        ddcClosedForm h hh).val.IsKahler →
    ∀ χ : ℝ → ℝ, IsWNCutoff χ →
    ∀ (G : Set (ℂ × ComplexModel (m + 1))) (Γ : ℂ × ComplexModel (m + 1) → 𝒳), IsOpen G →
      ContMDiffOn 𝓘(ℂ, ℂ × ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ G →
      (∀ q ∈ G, (μ (Γ q)).2 = affineLinePoint q.1) →
    ∀ y₀ : ComplexModel (m + 1), ((0 : ℂ), y₀) ∈ G → Ψ (Γ (0, y₀)) ≠ ⊥ →
      ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ y ∈ Metric.ball y₀ R,
        ((0 : ℂ), y) ∈ G ∧
        ((-(k : ℝ) - C : ℝ) : EReal) ≤
          prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (0, y)) ∧
        ∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) / 2 → (t, y) ∈ G ∧
          prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≠ ⊥ ∧
          |(prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y))).toReal -
            (prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (0, y))).toReal| ≤
            C * Real.exp ((k : ℝ) / 2) * ‖t‖

end SGPT.Okounkov.TranscendentalWN
