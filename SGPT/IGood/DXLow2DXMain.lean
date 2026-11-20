import SGPT.Bergman.Quant4PBMConvergence
import SGPT.IGood.DXLow2Normalize

/-!
# The asymptotic Riemann–Roch formula in the analytic setting

Blueprint `claude-dx-low2`, node `claude-dx-low2:dxmain`. Source `thm:DXmain1` and
`prop:DXmainanalytic` (chapter *`𝓘`-good singularities*) in the book's analytic setting: `X` a
connected compact Kähler manifold, `(L, h₀)` a holomorphic line bundle with a smooth metric,
`θ = c₁(L, h₀)`, the singular metric `h = h₀ e^{-φ}`, `φ ∈ PSH(X, θ)`, and a holomorphic line bundle
`T` (with a smooth metric, on which `h⁰` does not depend):

`lim_k n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) = vol(dd^c h) = vol θ_φ`,

with `h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) = dim Γ(X, L^k ⊗ T ⊗ 𝓘(kφ))` (`LiteralTwistedMultiplierSections`,
the normalized dimension `normalizedH0 L T φ k = n!/kⁿ h⁰`) and `vol θ_φ = ∫_X θⁿ_{P_θ[φ]_𝓘}`
(`sourceIVolume`).

* `tendsto_normalizedH0_of_isKahlerCurrent` (**`prop:DXmainanalytic`**, without the analytic
  singularity assumption): the formula when `θ_φ` is a Kähler current;
* `tendsto_normalizedH0_of_big_bundle`: the formula for every `φ` when `L` is big (`θ` carries a
  Kähler current);
* `tendsto_normalizedH0_of_positive_mass` (**`thm:DXmain1`, Steps 1–2**): the formula for every
  `φ ∈ PSH(X, θ)_{>0}`;
* `riemannRochLowerBound_of_kahler` (**`thm:DXmain1`, `≥`**): the lower half for every `φ`.

The Kähler form of the Bergman chapter is normalized here (`exists_normalized_kahlerBackground`),
so no normalization hypothesis remains. Not covered: `vol θ_φ = 0` with `L` not big (the book's
Step 3, where the formula says `h⁰ = o(kⁿ)`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Source `prop:DXmainanalytic`** (analytic setting; the analytic singularities are not needed):
if `θ_φ` is a Kähler current (`θ = c₁(L, h₀)`), then for every twist `T`
`n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_of_isKahlerCurrent
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ,
      Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨κ, -⟩ := id hcurrent
  obtain ⟨ω, hω⟩ := exists_normalized_kahlerBackground κ
  exact SGPT.Bergman.Quant4.tendsto_normalizedH0_of_kahlerCurrent ω hω L T hL hT hcurrent

/-- **`thm:DXmain1` for big line bundles** (analytic setting): if `θ = c₁(L, h₀)` carries a
Kähler current, then `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ` for every `φ ∈ PSH(X, θ)`. -/
theorem tendsto_normalizedH0_of_big_bundle
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {ψ : X → EReal} (hψ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨κ, -⟩ := id hψ
  obtain ⟨ω, hω⟩ := exists_normalized_kahlerBackground κ
  exact SGPT.Bergman.Quant4.tendsto_normalizedH0_of_big ω hω L T hL hT hψ hφ

/-- **Source `thm:DXmain1`, Steps 1–2** (analytic setting, `X` Kähler): for every
`φ ∈ PSH(X, θ)_{>0}` and every twist `T`, `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_of_positive_mass (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨ω, hω⟩ := exists_normalized_kahlerBackground ωb
  exact SGPT.Bergman.Quant4.tendsto_normalizedH0_of_pos ω hω L T hL hT hφ hφpos

/-- **Source `thm:DXmain1`, the inequality `≥`** (analytic setting, `X` Kähler): for every
`φ ∈ PSH(X, θ)` and every twist `T`, `vol θ_φ ≤ liminf_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem riemannRochLowerBound_of_kahler (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  obtain ⟨ω, hω⟩ := exists_normalized_kahlerBackground ωb
  exact SGPT.Bergman.Quant4.riemannRochLowerBound ω hω L T hL hT hφ

end SGPT.IGood.DXLow2
