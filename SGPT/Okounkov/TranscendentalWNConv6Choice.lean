import SGPT.Okounkov.TranscendentalWNConv6Envelope
import SGPT.Okounkov.TranscendentalWNConv6LineMeasure
import SGPT.Okounkov.TranscendentalWNConv6Diagonal

/-!
# Measure control from the integrated bound (WN21 Corollary 6.5; lane WN-CONV6)

Blueprint `tok-wn-conv6:choice` (chapter `claude-tok-wn-conv6`); source WN21 §6, Corollary 6.5.

`MeasureControlLiminfStatement F` is the analytic core of WN21 §6 (Propositions 6.1–6.4):
`liminf_k ∫_ℂ I_k dω_k ≥ vol(ξ)`, where `I_k(τ) = ∫_{X_τ ∩ D_k} θ̃ⁿ` (`MCData.fibreMass`) and `ω_k`
is `cutoffLineMeasure χ k`.  With the fibre bound `I_k ≤ vol(ξ)` (`MCData.fibreMass_le`), the
properties of `ω_k` (`cutoffLineMeasure_univ`, `cutoffLineMeasure_singleton_zero`,
`le_cutoffLineMeasure_ball`) and the diagonal choice (`Diagonal.exists_tendsto_of_liminf_lintegral`)
it gives `MeasureControlStatement F` (`measureControl_of_liminf`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **WN21 Propositions 6.1–6.4 (the analytic core of `tok-wn:measure-control`)**: for the data of
`MeasureControlStatement`, `liminf_k ∫_ℂ I_k dω_k ≥ vol(ξ)`. -/
def MeasureControlLiminfStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (D : MCData F 𝒳),
    ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ᶠ k in atTop,
      ENNReal.ofReal D.vol ≤ ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k + δ

namespace MCData

variable {F} {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] [CompactSpace 𝒳] [ConnectedSpace 𝒳] (D : MCData F 𝒳)

/-- **The diagonal choice of `τ_k`** (WN21 Corollary 6.5). -/
theorem exists_tau
    (hlim : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ᶠ k in atTop,
      ENNReal.ofReal D.vol ≤ ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k + δ) :
    ∃ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) ∧
      Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) ∧
      ∀ (s : ℕ → F.carrier → 𝒳)
        (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (s k)),
        (∀ k x, D.μ (s k x) = (x, affineLinePoint (τ k))) →
          Tendsto (fun k => fibreContactMass F D.form D.μ D.χ k (s k) (hs k)) atTop
            (𝓝 (ENNReal.ofReal D.vol)) := by
  obtain ⟨τ, hτ0, hτ, hI⟩ := Diagonal.exists_tendsto_of_liminf_lintegral (V := ENNReal.ofReal D.vol)
    (I := D.fibreMass) (ν := fun k => cutoffLineMeasure D.χ k) ENNReal.ofReal_ne_top
    D.fibreMass_le (fun k => (cutoffLineMeasure_univ D.hχ k).le)
    (fun k => cutoffLineMeasure_singleton_zero D.χ k)
    (fun r hr => ⟨ENNReal.ofReal (min r (Real.exp (-1 / 2)) ^ 2),
      ENNReal.ofReal_pos.mpr (by positivity) |>.ne', fun k => le_cutoffLineMeasure_ball D.hχ k hr⟩)
    hlim
  refine ⟨τ, hτ0, hτ, fun s hs hμs => ?_⟩
  refine hI.congr fun k => ?_
  exact (D.fibreContactMass_eq_fibreMass (hτ0 k) (hs k) (hμs k)).symm

end MCData

/-- **`tok-wn:measure-control` from its analytic core**: `MeasureControlLiminfStatement F` implies
`MeasureControlStatement F`. -/
theorem measureControl_of_liminf (h : MeasureControlLiminfStatement F) :
    MeasureControlStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc χ hχ
  let D : MCData F 𝒳 := ⟨E, hE, hE0, μ, hμ, Eℰ, hEℰ, θ, b, c, hc, hcb, hξ, hξc, χ, hχ⟩
  have := D.compactSpace
  have := D.connectedSpace
  exact D.exists_tau (h 𝒳 D)

end SGPT.Okounkov.TranscendentalWN
