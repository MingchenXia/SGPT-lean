import SGPT.Trace.RestVolGeneral

/-!
# The restricted volume vanishes when eq:traceposmasscond2 fails

Source: `chapter_trace.tex`, Section *Restricted volumes of line bundles*, the remark after
`thm:rest_volume_2` (`chapter_trace:remark:24`): "One could also show that when
eq:traceposmasscond2 fails, the right-hand side of eq:DXmainrelative is `0`."

Setting of `thm:rest_volume` (`SGPT.Trace.RestVol.rest_volume`): `X` compact Kähler, `Y ⊆ X` a
closed connected submanifold of dimension `m`, `L` a holomorphic line bundle with smooth metric
`h₀` (`θ = c₁(L, h₀)`), `A` a line bundle with smooth metric of Kähler curvature `ω` and a section
`ϕ ∈ H⁰(X, A)` not vanishing identically on `Y`, `h = h₀ e^{-φ}` with `φ ∈ PSH(X, θ)` and
`ν(φ, Y) = 0`, and `T` a holomorphic line bundle.

* `tendsto_restrictedH0_zero_of_not_traceposmasscond2`: if eq:traceposmasscond2
  (`lim_{ε→0+} ∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(φ))^m > 0`) fails, then
  `m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k)) → 0`.
* `tendsto_restrictedH0_zero_of_tendsto_zero`: the same conclusion when the limit of
  eq:traceposmasscond2 is `0` (the limit always exists: it is the mass
  `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`, `tendsto_sourceTraceMass_add_smul_right'`, so "fails" means
  "is `0`").

Proof: by right-continuity of the perturbed trace masses at `ε = 0`
(`tendsto_sourceTraceMass_add_smul_right'`), the limit in eq:traceposmasscond2 is the mass
`∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m` (`0` when the trace is not defined); if the condition fails this
mass is `0`, and the general form of eq:DXmainrelative (`tendsto_restrictedH0`, whose upper bound
is the book's Step 2 bound `limsup ≤ ∫_Y (θ|_Y + k₀⁻¹ω|_Y + dd^c Tr^{θ+k₀⁻¹ω}_Y(φ))^m`,
`limsup_restrictedH0_le_perturbed`, letting `k₀ → ∞`) gives the limit `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **Source `chapter_trace:remark:24`**: in the setting of `thm:rest_volume`, if
eq:traceposmasscond2 fails, i.e. there is no `M > 0` with
`∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(φ))^m → M` as `ε → 0+` (`ω = c₁(A, h_A)`), then the
right-hand side of eq:DXmainrelative is `0`: for every holomorphic line bundle `T`,
`m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k)) → 0`. -/
theorem tendsto_restrictedH0_zero_of_not_traceposmasscond2
    {L T A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hA : IsSourceSmoothHermitianMetric A) (hAK : (sourceNativeFirstChernForm A hA).val.IsKahler)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (sA : HolomorphicSections (n := n) A.Fiber) (hsA : ∃ y ∈ W, sA y ≠ 0)
    {φ : X → EReal} (hφ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let ωA : KahlerBackground n X := ⟨sourceNativeFirstChernForm A hA, hAK⟩
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    (¬ ∃ M : ℝ≥0∞, 0 < M ∧ Tendsto (fun ε : ℝ => SGPT.Trace.sourceTraceMass ωA
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA) (contMDiff_val hk hW.2.2)
      (sourceNativeFirstChernForm L hL + ε • ωA.form) φ) (𝓝[>] 0) (𝓝 M)) →
    Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 0) := by
  intro ωA hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  intro hfail
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA
  have hpullA : (ClosedRealOneOneForm.pullback hval ωA.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 ωA.form ωA.isKahler
  -- the limit of eq:traceposmasscond2 is the mass of the trace
  have hlim := tendsto_sourceTraceMass_add_smul_right' hk ωA ωA ωW hval hpullA
    (sourceNativeFirstChernForm L hL) hφ hν
  have hzero : SGPT.Trace.sourceTraceMass ωA ωW hval (sourceNativeFirstChernForm L hL) φ = 0 := by
    by_contra hne
    exact hfail ⟨_, pos_iff_ne_zero.mpr hne, hlim⟩
  have h : Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 (SGPT.Trace.sourceTraceMass ωA ωW hval (sourceNativeFirstChernForm L hL) φ)) :=
    tendsto_restrictedH0 hL hT hA hAK hW sA hsA hφ hν
  rwa [hzero] at h

/-- **Source `chapter_trace:remark:24`, limit form**: in the setting of `thm:rest_volume`, if
`lim_{ε→0+} ∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(φ))^m = 0`, then for every holomorphic line
bundle `T`, `m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k)) → 0`. -/
theorem tendsto_restrictedH0_zero_of_tendsto_zero
    {L T A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hA : IsSourceSmoothHermitianMetric A) (hAK : (sourceNativeFirstChernForm A hA).val.IsKahler)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (sA : HolomorphicSections (n := n) A.Fiber) (hsA : ∃ y ∈ W, sA y ≠ 0)
    {φ : X → EReal} (hφ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let ωA : KahlerBackground n X := ⟨sourceNativeFirstChernForm A hA, hAK⟩
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    Tendsto (fun ε : ℝ => SGPT.Trace.sourceTraceMass ωA
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA) (contMDiff_val hk hW.2.2)
      (sourceNativeFirstChernForm L hL + ε • ωA.form) φ) (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 0) := by
  intro ωA hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  intro h0
  refine tendsto_restrictedH0_zero_of_not_traceposmasscond2 hL hT hA hAK hW sA hsA hφ hν ?_
  rintro ⟨M, hM, hlimM⟩
  exact hM.ne' (tendsto_nhds_unique hlimM h0)

end SGPT.Trace.RestVol
