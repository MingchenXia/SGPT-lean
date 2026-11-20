import SGPT.Okounkov.TranscendentalWNVolumeExcMain
import SGPT.Okounkov.TranscendentalWNVolumeGlobalLegendre

/-!
# Bundle charts of the exceptional divisor (package WN-VF4): the interface

Blueprint `claude-tok-wn-vf4`, node `tok-wn-vf4:bundle-chart`; source D. Witt Nyström,
arXiv:2103.03660 (WN21), end of §4 (the coordinates `(z̃₁, z')` on `ℰ`, `z₁ = z̃₁ τ`).

Let `μ : 𝒳 → X × ℙ¹` be the deformation to the normal cone of `Z = Y₁` and `ℰ` its exceptional
divisor.  Off the strict transforms `X'` (`S₁ = 0`, `S₁ = strictWeight`) and `Z̃`
(`S₂ = 0`, `S₂ = zStrictWeight`), `ℰ` is the `ℂ*`-bundle `N_{Z|X} \ 0` over `Z`.  A **bundle
chart** of `ℰ` over a chart `e_Z` of `Z` with domain `Ω` is a map `Λ : Ω × ℂ → ℰ`,
`Λ(ζ, w) = ` the point of the fibre over `e_Z⁻¹ ζ` with fibre coordinate `w` (WN21's `z̃₁`), such
that

* `π_X μ Λ(ζ, w) = e_Z⁻¹ ζ`, `Λ` is injective and its image contains every point of `ℰ` over
  `e_Z⁻¹(Ω)` with `S₁, S₂ > 0`, at fibre coordinates `w ≠ 0`;
* the fibre norm is `S₂ / S₁ = |w|² e^{-g}` (`log S₂ - log S₁ = log |w|² - g`) with the twist
  `g` a smooth local potential of `η|_Z` (`η` the curvature of the metric of `𝒪(Z)`): this is
  WN21's `log |z̃₁|² - g_Z`;
* `Λ` is holomorphic with holomorphic inverse: near every point with `w ≠ 0` it is the inverse of
  an atlas chart of the submanifold `ℰ` (`IsExcBundleChart.chart`).

`ExcBundleChartStatement F` asserts that every point of `Z` has a bundle chart over a chart
domain containing it.  It is the only geometric input of the bundle Legendre identity
(`TranscendentalWNVolumeBundleMain`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Chart

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- A map `Λ(ζ, w)` read on the model `ℂ^{m+1}` (`(ζ, w) = stripModelEquiv m v`). -/
def bundleMap (Λ : ComplexModel m → ℂ → 𝒳) (v : ComplexModel (m + 1)) : 𝒳 :=
  Λ (stripModelEquiv m v).1 (stripModelEquiv m v).2

/-- **A bundle chart of `ℰ`** over the chart `e_Z` of `Z` on the open set `Ω`, with fibre
coordinate `w` and twist `g` (`tok-wn-vf4:bundle-chart`). -/
structure IsExcBundleChart (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hμ : IsNormalConeDeformation F μ) (eZ : ComplexChart m F.tail.carrier)
    (Ω : Set (ComplexModel m)) (Λ : ComplexModel m → ℂ → 𝒳) (g : ComplexModel m → ℝ) : Prop where
  isOpen : IsOpen Ω
  subset_target : Ω ⊆ eZ.val.target
  mem : ∀ ζ ∈ Ω, ∀ w : ℂ, Λ ζ w ∈ exceptionalSet F μ
  proj : ∀ ζ ∈ Ω, ∀ w : ℂ, (μ (Λ ζ w)).1 = firstFlagInclusion F (eZ.val.symm ζ)
  inj : ∀ ζ ∈ Ω, ∀ w w' : ℂ, Λ ζ w = Λ ζ w' → w = w'
  cover : ∀ p ∈ exceptionalSet F μ, 0 < strictWeight F E μ p → 0 < zStrictWeight F E μ p →
    ∀ ζ ∈ Ω, (μ p).1 = firstFlagInclusion F (eZ.val.symm ζ) → ∃ w : ℂ, w ≠ 0 ∧ Λ ζ w = p
  weights : ∀ ζ ∈ Ω, ∀ w : ℂ, w ≠ 0 → 0 < strictWeight F E μ (Λ ζ w) ∧
    0 < zStrictWeight F E μ (Λ ζ w) ∧
    Real.log (zStrictWeight F E μ (Λ ζ w)) - Real.log (strictWeight F E μ (Λ ζ w)) =
      logNormSq w - g ζ
  twist : IsSmoothLocalPotential
    (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) E.curvature).val eZ Ω g
  chart : ∀ v : ComplexModel (m + 1), (stripModelEquiv m v).1 ∈ Ω → (stripModelEquiv m v).2 ≠ 0 →
    letI := exceptionalChartedSpace F hμ
    ∃ (Ech : ComplexChart (m + 1) (exceptionalSet F μ)) (D : Set (ComplexModel (m + 1))),
      IsOpen D ∧ v ∈ D ∧ D ⊆ Ech.val.target ∧
        ∀ v' ∈ D, (stripModelEquiv m v').1 ∈ Ω ∧
          ((Ech.val.symm v' : exceptionalSet F μ) : 𝒳) = bundleMap Λ v'

variable {F}

/-- Bundle charts restrict to open subsets of their domain. -/
theorem IsExcBundleChart.mono {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    {hμ : IsNormalConeDeformation F μ} {eZ : ComplexChart m F.tail.carrier}
    {Ω Ω' : Set (ComplexModel m)} {Λ : ComplexModel m → ℂ → 𝒳} {g : ComplexModel m → ℝ}
    (h : IsExcBundleChart F E hμ eZ Ω Λ g) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    IsExcBundleChart F E hμ eZ Ω' Λ g where
  isOpen := hΩ'
  subset_target := hsub.trans h.subset_target
  mem := fun ζ hζ => h.mem ζ (hsub hζ)
  proj := fun ζ hζ => h.proj ζ (hsub hζ)
  inj := fun ζ hζ => h.inj ζ (hsub hζ)
  cover := fun p hp h1 h2 ζ hζ => h.cover p hp h1 h2 ζ (hsub hζ)
  weights := fun ζ hζ => h.weights ζ (hsub hζ)
  twist := h.twist.mono hΩ' hsub
  chart := by
    intro v hv hv0
    obtain ⟨Ech, D, hD, hvD, hDt, hDΛ⟩ := h.chart v (hsub hv) hv0
    have hO : IsOpen (stripModelEquiv m ⁻¹' (Ω' ×ˢ univ)) :=
      (hΩ'.prod isOpen_univ).preimage (stripModelEquiv m).continuous
    refine ⟨Ech, D ∩ stripModelEquiv m ⁻¹' (Ω' ×ˢ univ), hD.inter hO, ⟨hvD, hv, mem_univ _⟩,
      inter_subset_left.trans hDt, fun v' hv' => ⟨hv'.2.1, (hDΛ v' hv'.1).2⟩⟩

end Chart

/-- **`tok-wn-vf4:bundle-chart`**: every point of `Z` lies over the domain of a bundle chart of
`ℰ` (WN21 §4: the `τ`-monomial chart `z₁ = z̃₁ τ` of the blow-up of `X × ℙ¹` along `Z × {0}`,
restricted to `τ = 0`). -/
def ExcBundleChartStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (y₀ : F.tail.carrier),
      ∃ (eZ : ComplexChart m F.tail.carrier) (Ω : Set (ComplexModel m))
        (Λ : ComplexModel m → ℂ → 𝒳) (g : ComplexModel m → ℝ),
        IsExcBundleChart F E hμ eZ Ω Λ g ∧ y₀ ∈ eZ.val.source ∧ eZ.val y₀ ∈ Ω

end SGPT.Okounkov.TranscendentalWN
