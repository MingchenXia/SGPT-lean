import SGPT.IGood.KBigDXMain
import SGPT.LineBundle.TMetricSections
import SGPT.LineBundle.TMetricExists
import SGPT.LineBundle.TMetricBare

/-!
# The asymptotic Riemann–Roch formula for an arbitrary twist `T`

Lane T-METRIC, blueprint `claude-t-metric`, node `claude-t-metric:dxmain1`. Source `thm:DXmain1`
(chapter *`𝓘`-good singularities*): `(L, h)` a Hermitian pseudo-effective line bundle and `T` an
ARBITRARY holomorphic line bundle on a connected compact Kähler manifold `X` of dimension `n`:

  `lim_k n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) = vol(dd^c h)`; in particular the limit exists.

Lanes DX-LOW2 and K-BIG proved this for `T` carrying a smooth Hermitian metric
(`IsSourceSmoothHermitianMetric T`). A `HermitianHolomorphicLineBundle` always carries a
continuous metric, but `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` does not depend on it
(`SGPT.LineBundle.TMetric.normalizedH0_rescale`), and on a compact base the metric can be rescaled
to a smooth one (`SGPT.LineBundle.TMetric.exists_smooth_rescale`). Hence the metric hypothesis on
`T` is removed:

* `exists_smoothMetric`: every `T` is isomorphic (`FrameIdentityEquiv`) to the same holomorphic line
  bundle with a smooth metric, with the same `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` for all `L, k, φ`.
* `tendsto_normalizedH0` (**`thm:DXmain1`**, compact Kähler setting, arbitrary `T`).
* `riemannRochLowerBound`, `riemannRochUpperBound`: the two halves, arbitrary `T`.
* `tendsto_normalizedH0_of_equiv`: the same with the reference metric `h₀` taken on any isomorphic
  copy of `L` (`L ≅ (L, h₀)`); with `exists_smoothMetric L`, both `L` and `T` are arbitrary
  holomorphic line bundles.
* `tendsto_normalizedH0_zero_of_not_big`, `limsup_normalizedH0_le_envelopeMass`: lane K-BIG's
  bigness criterion and Berman's upper bound, arbitrary `T`.

Metric-free bundles (`SGPT.LineBundle.TMetric.FramePartition`): a holomorphic line bundle in
Mathlib's sense, with no metric data, becomes a `HermitianHolomorphicLineBundle` with a smooth metric
(`FramePartition.toHHLB`), and every `HermitianHolomorphicLineBundle` is isomorphic to the one built
from its underlying metric-free bundle:

* `normalizedH0_toHHLB`: `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` only depends on the metric-free bundles
  underlying `L` and `T`.
* `tendsto_normalizedH0_bare`: `thm:DXmain1` with `L` and `T` metric-free holomorphic line bundles
  (`h₀` the glued smooth metric on `L`).

The projective-scheme form `SGPT.IGood.DXMain.DXMain1Statement`
(`SGPT.GAGA.SmoothFlags.dxMain1Statement`) already quantifies over every algebraic line bundle
`T` with no metric.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.IGood.TMetric

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open SGPT.LineBundle.TMetric
open IntegrationCurrent
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Every holomorphic line bundle on a compact complex manifold has a smooth metric, without
changing `h⁰`**: `T` is isomorphic (as a holomorphic line bundle, `FrameIdentityEquiv`) to a
`T'` with a smooth Hermitian metric, and `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) = h⁰(X, T' ⊗ L^k ⊗ 𝓘(kφ))` for
all `L`, `k`, `φ`. (`T' = rescale T ρ` is `T` itself with the metric `ρ h_T`.) -/
theorem exists_smoothMetric [CompactSpace X] (T : HermitianHolomorphicLineBundle.{0, 0} n X) :
    ∃ T' : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric T' ∧
      Nonempty (FrameIdentityEquiv T.Fiber T'.Fiber) ∧
      ∀ (L : HermitianHolomorphicLineBundle.{0, 0} n X) (φ : X → EReal) (k : ℕ),
        normalizedH0 L T' φ k = normalizedH0 L T φ k := by
  obtain ⟨ρ, hρc, hρ, hT'⟩ := exists_smooth_rescale T
  exact ⟨rescale T ρ hρc hρ, hT', ⟨rescaleEquiv T ρ hρc hρ⟩,
    fun L φ k => normalizedH0_rescale L T ρ hρc hρ φ k⟩

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **The lower half of `thm:DXmain1`, arbitrary twist** (compact Kähler setting): for every
`φ ∈ PSH(X, θ)`, `θ = c₁(L, h₀)`, and every holomorphic line bundle `T` (no metric hypothesis),
`vol θ_φ ≤ liminf_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem riemannRochLowerBound (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  obtain ⟨T', hT', -, hh⟩ := exists_smoothMetric T
  obtain ⟨hφ', h⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωb hL hT' hφ
  refine ⟨hφ', ?_⟩
  simpa only [hh L φ] using h

/-- **The upper half of `thm:DXmain1`, arbitrary twist** (compact Kähler setting): for every
`φ ∈ PSH(X, θ)` and every holomorphic line bundle `T` (no metric hypothesis),
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol θ_φ`. -/
theorem riemannRochUpperBound (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    SGPT.Bergman.Quant3.RiemannRochUpperBound (chernForm L hL) L T φ := by
  obtain ⟨T', hT', -, hh⟩ := exists_smoothMetric T
  obtain ⟨hφ', h⟩ := SGPT.IGood.KBig.riemannRochUpperBound ωb hL hT' hφ
  refine ⟨hφ', ?_⟩
  simpa only [hh L φ] using h

/-- **Source `thm:DXmain1` (asymptotic Riemann–Roch formula), compact Kähler setting, arbitrary
twist**: `X` a connected compact Kähler manifold of dimension `n`, `(L, h₀)` a holomorphic line
bundle with a smooth metric, `θ = c₁(L, h₀)`, `φ ∈ PSH(X, θ)` (`h = h₀ e^{-φ}` a psh metric:
`(L, h)` Hermitian pseudo-effective), and `T` an ARBITRARY holomorphic line bundle (the metric that
`HermitianHolomorphicLineBundle` bundles is not used and not assumed smooth). Then
`lim_k n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) = vol(dd^c h) = vol θ_φ`; in particular the limit exists. -/
theorem tendsto_normalizedH0 (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨T', hT', -, hh⟩ := exists_smoothMetric T
  have h := SGPT.IGood.KBig.tendsto_normalizedH0 ωb hL hT' hφ
  simpa only [hh L φ] using h

/-- **`thm:DXmain1` for arbitrary `L` and `T`**: let `L`, `T` be holomorphic line bundles (no
metric hypotheses) and `h₀` a smooth Hermitian metric on `L`, given as an isomorphic copy
`L₀ = (L, h₀)` (`L ≅ L₀`; one exists by `exists_smoothMetric L`). For every psh metric
`h = h₀ e^{-φ}` (`φ ∈ PSH(X, c₁(L, h₀))`), `n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) → vol(dd^c h)`. -/
theorem tendsto_normalizedH0_of_equiv (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) {L₀ : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L₀.Fiber) (hL₀ : IsSourceSmoothHermitianMetric L₀)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L₀ hL₀) φ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop
      (𝓝 (sourceIVolume (chernForm L₀ hL₀) φ hφ)) := by
  have h := tendsto_normalizedH0 ωb T hL₀ hφ
  simpa only [← normalizedH0_congr ΦL (FrameIdentityEquiv.refl T.Fiber) φ] using h

/-- the bigness criterion, arbitrary twist: if `c₁(L, h₀)` carries no Kähler current,
then `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) → 0` for every `φ` and every holomorphic line bundle `T`. -/
theorem tendsto_normalizedH0_zero_of_not_big (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (φ : X → EReal)
    (hnb : ¬ ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 0) := by
  obtain ⟨T', hT', -, hh⟩ := exists_smoothMetric T
  have h := SGPT.Bergman.KBig.tendsto_normalizedH0_zero_of_not_big omega hvol L T' hL hT' φ hnb
  simpa only [hh L φ] using h

/-- Berman's upper bound, arbitrary twist: if `PSH(X, θ) ≠ ∅`, then
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ∫_X θⁿ_{P_θ(0)}` for every `φ` and every holomorphic
line bundle `T`. -/
theorem limsup_normalizedH0_le_envelopeMass (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (φ : X → EReal)
    (hne : ∃ u : X → EReal, (ofFixedModel n X).IsThetaPSH (chernForm L hL) u) :
    ∃ hP : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (SGPT.Bergman.KBig.obstacleEnvelope L hL),
      limsup (fun k => normalizedH0 L T φ k) atTop ≤
        sourcePotentialNonPluripolarMeasure (chernForm L hL)
          (SGPT.Bergman.KBig.obstacleEnvelope L hL) hP univ := by
  obtain ⟨T', hT', -, hh⟩ := exists_smoothMetric T
  obtain ⟨hP, h⟩ :=
    SGPT.Bergman.KBig.limsup_normalizedH0_le_envelopeMass omega hvol L T' hL hT' φ hne
  refine ⟨hP, ?_⟩
  simpa only [hh L φ] using h

/-! ### Metric-free holomorphic line bundles -/

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` only depends on the metric-free holomorphic line bundles underlying
`L` and `T`: it is unchanged when `L`, `T` are replaced by the bundles `PL.toHHLB`, `PT.toHHLB`
built from their underlying metric-free bundles (with any frame partitions). -/
theorem normalizedH0_toHHLB (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (PL : FramePartition n L.Fiber) (PT : FramePartition n T.Fiber) (φ : X → EReal) (k : ℕ) :
    normalizedH0 PL.toHHLB PT.toHHLB φ k = normalizedH0 L T φ k :=
  (normalizedH0_congr (FramePartition.equivToHHLB L PL) (FramePartition.equivToHHLB T PT) φ k).symm

/-- **Source `thm:DXmain1` for metric-free holomorphic line bundles**: `EL`, `ET` holomorphic line
bundles on a connected compact Kähler manifold in Mathlib's sense (fibre bundle with fibre `ℂ`,
vector bundle and holomorphic structure; no metric data), made into Hermitian holomorphic line
bundles by frame partitions `PL`, `PT` (which exist: `exists_framePartition`; the result does not
depend on them, `FramePartition.toHHLBEquiv`). With `h₀` the resulting smooth metric on `EL`,
`θ = c₁(EL, h₀)` and `φ ∈ PSH(X, θ)`:
`n!/kⁿ h⁰(X, ET ⊗ EL^k ⊗ 𝓘(kφ)) → vol θ_φ`. -/
theorem tendsto_normalizedH0_bare (ωb : KahlerBackground n X)
    (EL : X → Type) [∀ x, AddCommGroup (EL x)] [∀ x, Module ℂ (EL x)]
    [∀ x, TopologicalSpace (EL x)] [TopologicalSpace (Bundle.TotalSpace ℂ EL)] [FiberBundle ℂ EL]
    [VectorBundle ℂ ℂ EL] [ContMDiffVectorBundle ∞ ℂ EL (𝓘(ℂ, ComplexModel n))]
    (ET : X → Type) [∀ x, AddCommGroup (ET x)] [∀ x, Module ℂ (ET x)]
    [∀ x, TopologicalSpace (ET x)] [TopologicalSpace (Bundle.TotalSpace ℂ ET)] [FiberBundle ℂ ET]
    [VectorBundle ℂ ℂ ET] [ContMDiffVectorBundle ∞ ℂ ET (𝓘(ℂ, ComplexModel n))]
    (PL : FramePartition n EL) (PT : FramePartition n ET) {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH
      (chernForm PL.toHHLB PL.isSourceSmoothHermitianMetric_toHHLB) φ) :
    Tendsto (fun k => normalizedH0 PL.toHHLB PT.toHHLB φ k) atTop
      (𝓝 (sourceIVolume (chernForm PL.toHHLB PL.isSourceSmoothHermitianMetric_toHHLB) φ hφ)) :=
  tendsto_normalizedH0 ωb PT.toHHLB PL.isSourceSmoothHermitianMetric_toHHLB hφ

end SGPT.IGood.TMetric
